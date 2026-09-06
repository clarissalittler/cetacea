//! Session behavior: imports (relative, once-only, aliased, mode
//! isolation), status lines, policies, goal lookup, and countermodels.

use hol_session::{DeclStatus, Options, Policy, Session, Severity, VirtualFs};

fn library() -> VirtualFs {
    let mut fs = VirtualFs::default();
    fs.add(
        "lib/prop.ctea",
        "mode constructive\ntheorem id (P : Prop) : P -> P := by\n  intro h\n  exact h\n\nmode classical\n\ntheorem em (P : Prop) : P \\/ not P := by\n  by_cases h : P\n  left\n  exact h\n  right\n  exact h\n",
    );
    fs.add("lib/prelude.ctea", "import prop.ctea\n");
    fs
}

fn check(fs: &VirtualFs, opts: Options, path: &str, source: &str) -> hol_session::CheckResult {
    Session::new(fs, opts).check(Some(path), source)
}

#[test]
fn imports_resolve_relative_to_the_importer_and_load_once() {
    let fs = library();
    let source = "import ../lib/prelude.ctea\nimport ../lib/prop.ctea\n\ntheorem use_id (Q : Prop) : Q -> Q := by\n  exact id\n";
    let result = check(&fs, Options::default(), "work/hw.ctea", source);
    assert!(!result.has_errors(), "{:?}", result.diagnostics);
    let local: Vec<_> = result.decls.iter().filter(|d| !d.is_imported).collect();
    assert_eq!(local.len(), 1);
    assert_eq!(local[0].render(), "accepted theorem use_id (constructive)");
    let imported: Vec<_> = result
        .decls
        .iter()
        .filter(|d| d.is_imported)
        .map(|d| d.name.as_str())
        .collect();
    assert_eq!(imported, vec!["id", "em"], "each file is loaded once");
}

#[test]
fn import_mode_does_not_leak_and_std_dir_maps_paths() {
    let fs = library();
    let opts = Options {
        std_dir: Some("lib".to_string()),
        ..Options::default()
    };
    // `std/prelude.ctea` is mapped to `lib/prelude.ctea`; the imported
    // file's `mode classical` does not leak, so `em` is rejected here.
    let source = "import ../../std/prelude.ctea\n\ntheorem classical_here (P : Prop) : P \\/ not P := by\n  exact em\n";
    let result = check(&fs, opts, "docs/x/y.ctea", source);
    assert!(result.has_errors());
    let message = &result.diagnostics[0].message;
    assert!(message.contains("classical reasoning"), "{message}");
}

#[test]
fn aliased_imports_qualify_names() {
    let fs = library();
    let source = "import ../lib/prop.ctea as prop\n\ntheorem use_qualified (Q : Prop) : Q -> Q := by\n  exact prop.id\n\ntheorem unqualified_fails (Q : Prop) : Q -> Q := by\n  exact id\n";
    let result = check(&fs, Options::default(), "work/hw.ctea", source);
    let statuses: Vec<_> = result
        .decls
        .iter()
        .filter(|d| !d.is_imported)
        .map(|d| (d.name.as_str(), d.status))
        .collect();
    assert_eq!(
        statuses,
        vec![
            ("use_qualified", DeclStatus::Accepted),
            ("unqualified_fails", DeclStatus::Failed)
        ]
    );
    assert!(result
        .diagnostics
        .iter()
        .any(|d| d.message.contains("unknown hypothesis or theorem `id`")));
}

#[test]
fn status_lines_and_policies() {
    let fs = VirtualFs::default();
    let source = "\
axiom magic (P : Prop) : P
theorem uses_axiom (Q : Prop) : Q := by
  exact magic
theorem hole (Q : Prop) : Q -> Q := by
  sorry
theorem depends (Q : Prop) : Q -> Q := by
  exact hole
mode classical
theorem classical (P : Prop) : not not P -> P := by
  intro h
  by_contra hn
  exact h hn
";
    let result = check(&fs, Options::default(), "hw.ctea", source);
    let lines: Vec<String> = result.decls.iter().map(|d| d.render()).collect();
    assert_eq!(
        lines,
        vec![
            "trusted axiom magic",
            "accepted theorem uses_axiom (constructive; axioms: magic)",
            "incomplete theorem hole (constructive; uses sorry)",
            "incomplete theorem depends (constructive; uses sorry)",
            "accepted theorem classical (classical)",
        ]
    );
    assert!(result.ok());

    let strict = Options {
        policy: Policy {
            deny_sorry: true,
            deny_axioms: true,
            deny_classical: true,
        },
        ..Options::default()
    };
    let result = check(&fs, strict, "hw.ctea", source);
    assert_eq!(result.violations.len(), 4, "{:?}", result.violations);
    assert!(!result.ok());
}

#[test]
fn goals_at_reports_the_state_after_each_tactic() {
    let fs = VirtualFs::default();
    let source = "\
theorem and_comm (P Q : Prop) : P /\\ Q -> Q /\\ P := by
  intro h
  split
  exact h.right
  exact h.left
";
    let result = check(&fs, Options::default(), "hw.ctea", source);
    assert!(result.ok(), "{:?}", result.diagnostics);
    let (name, goals) = result.goals_at(1).unwrap();
    assert_eq!(name, "and_comm");
    assert_eq!(goals.len(), 1);
    assert_eq!(goals[0].target, "P /\\ Q -> Q /\\ P");
    let (_, goals) = result.goals_at(2).unwrap();
    assert_eq!(
        goals[0].hyps,
        vec![("h".to_string(), "P /\\ Q".to_string())]
    );
    assert_eq!(goals[0].target, "Q /\\ P");
    let (_, goals) = result.goals_at(3).unwrap();
    assert_eq!(goals.len(), 2);
    assert_eq!(goals[0].target, "Q");
    assert_eq!(goals[1].target, "P");
    let (_, goals) = result.goals_at(5).unwrap();
    assert!(goals.is_empty());
    assert!(result.goals_at(9).is_none());
}

#[test]
fn propositional_countermodels_explain_false_statements() {
    let fs = VirtualFs::default();
    let source = "\
theorem converse_error (P Q : Prop) : (P -> Q) -> Q -> P := by
  intro hpq
  intro hq
  exact hq
theorem wrong_turn (P Q R : Prop) : (P -> R) -> (Q -> R) -> P -> R := by
  intro hpr
  intro hqr
  intro hp
  apply hqr
  exact hp
";
    let result = check(&fs, Options::default(), "hw.ctea", source);
    let errors: Vec<&hol_session::Diag> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert_eq!(errors.len(), 2);
    assert!(
        errors[0]
            .notes
            .iter()
            .any(|n| n.contains("not a tautology: it is false when P = false, Q = true")),
        "{:?}",
        errors[0].notes
    );
    assert!(
        errors[1].notes.iter().any(|n| n
            .contains("open goal does not follow from the current hypotheses: it is false when")),
        "{:?}",
        errors[1].notes
    );
    assert_eq!(result.decls[0].render(), "failed theorem converse_error");
}
