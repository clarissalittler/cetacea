//! M3: natural numbers, induction, calc, tier gating, and arithmetic
//! countermodels.

use hol_session::{DeclStatus, Options, Session, Severity, VirtualFs};
use hol_syntax::Tier;

fn check(source: &str, tier: Option<Tier>) -> hol_session::CheckResult {
    let fs = VirtualFs::default();
    let opts = Options {
        tier,
        ..Options::default()
    };
    Session::new(&fs, opts).check(Some("hw.ctea"), source)
}

fn statuses(result: &hol_session::CheckResult) -> Vec<(String, DeclStatus)> {
    result
        .decls
        .iter()
        .filter(|d| !d.is_imported)
        .map(|d| (d.name.clone(), d.status))
        .collect()
}

#[test]
fn numerals_compute_and_print_infix() {
    let result = check(
        "theorem two_plus_two : 2 + 2 = 4 := by\n  refl\ntheorem succ_form (n : Nat) : add(n, 1) = succ(n) := by\n  refl\ntheorem le_small : le(2, 5) := by\n  simp\n  trivial\ntheorem sub_trunc : sub(2, 5) = 0 := by\n  refl\n",
        Some(Tier::FolNat),
    );
    assert!(result.ok(), "{:?}", result.diagnostics);
    assert_eq!(result.decls[1].statement, "n + 1 = succ(n)");
    assert_eq!(result.decls[2].statement, "2 <= 5");
    assert_eq!(result.decls[3].statement, "2 - 5 = 0");
}

#[test]
fn tier_one_rejects_arithmetic() {
    let result = check("theorem two : 2 = 2 := by\n  refl\n", None);
    assert!(result.has_errors());
    assert!(result.diagnostics[0]
        .message
        .contains("needs natural numbers"));
    let result = check("theorem two (n : Nat) : n = n := by\n  refl\n", None);
    assert!(
        result.diagnostics[0]
            .message
            .contains("`Nat` needs `logic fol_nat`"),
        "{:?}",
        result.diagnostics
    );
    let result = check("logic fol_nat\ntheorem two : 2 = 2 := by\n  refl\n", None);
    assert!(result.ok(), "{:?}", result.diagnostics);
}

#[test]
fn induction_with_and_without_generalizing() {
    let source = "\
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      exact ih

theorem add_comm_gen (n : Nat) : forall m : Nat, n + m = m + n := by
  intro m
  induction n generalizing m with
  | zero =>
      refl
  | succ k ih =>
      simp
      exact ih m

theorem needs_revert (n : Nat) : le(n, n) -> le(n, n) := by
  intro h
  induction n with
  | zero =>
      exact h
  | succ k ih =>
      exact h
";
    let result = check(source, Some(Tier::FolNat));
    assert_eq!(
        statuses(&result),
        vec![
            ("add_zero".to_string(), DeclStatus::Accepted),
            ("add_comm_gen".to_string(), DeclStatus::Accepted),
            ("needs_revert".to_string(), DeclStatus::Failed),
        ]
    );
    assert!(result.decls[0].datatypes.contains(&"Nat".to_string()));
    let error = result
        .diagnostics
        .iter()
        .find(|d| d.severity == Severity::Error)
        .unwrap();
    assert!(
        error
            .message
            .contains("while the hypothesis `h` depends on it"),
        "{}",
        error.message
    );
    assert!(error.notes.iter().any(|n| n.contains("revert h")));
}

#[test]
fn calc_chains_equalities() {
    let source = "\
theorem chain (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
    _ = c := h2

theorem chain_block (a b : Nat) (h : a = b) : a + 0 = b := by
  calc a + 0 = a := by
        refl
    _ = b := h

theorem broken (a b c : Nat) (h1 : a = b) : a = c := by
  calc a = b := h1
    _ = c := h1
";
    let result = check(source, Some(Tier::FolNat));
    assert_eq!(
        statuses(&result),
        vec![
            ("chain".to_string(), DeclStatus::Accepted),
            ("chain_block".to_string(), DeclStatus::Accepted),
            ("broken".to_string(), DeclStatus::Failed),
        ]
    );
}

#[test]
fn arithmetic_countermodels() {
    let result = check(
        "theorem wrong (n m : Nat) : n + m = n := by\n  refl\ntheorem wrong_goal (n : Nat) : le(n, 3) -> le(n, 2) := by\n  intro h\n  simp\n  exact h\n",
        Some(Tier::FolNat),
    );
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert_eq!(errors.len(), 2);
    assert!(
        errors[0]
            .notes
            .iter()
            .any(|n| n.contains("false when n = 0, m = 1")),
        "{:?}",
        errors[0].notes
    );
    assert!(
        errors[1]
            .notes
            .iter()
            .any(|n| n.contains("false when n = 3")),
        "{:?}",
        errors[1].notes
    );
}

#[test]
fn strong_induction_from_the_library() {
    let fs = library_fs();
    let source = "\
import ../lib/prelude.ctea

theorem zero_le_all (n : Nat) : le(0, n) := by
  apply strong_induction {P := fun m : Nat => le(0, m); n := n}
  simp
  trivial
  intro k
  intro hk
  simp
  trivial
";
    let opts = Options {
        tier: Some(Tier::FolNat),
        ..Options::default()
    };
    let result = Session::new(&fs, opts).check(Some("work/hw.ctea"), source);
    assert!(result.ok(), "{:?}", result.diagnostics);
}

fn library_fs() -> VirtualFs {
    let mut fs = VirtualFs::default();
    for name in [
        "prelude", "prop", "fol", "eq", "set", "nat", "modular", "fun", "list", "finite",
    ] {
        let path = format!("lib/{name}.ctea");
        fs.add(
            &path,
            &std::fs::read_to_string(format!("../../{path}")).unwrap(),
        );
    }
    fs
}

#[test]
fn hol_tier_lists_functions_and_cases() {
    let fs = library_fs();
    let source = "\
import ../lib/prelude.ctea

-- Polymorphic lists: the statement is implicitly polymorphic.
theorem len_two (A : Type) (a b : A) : length(cons(a, cons(b, nil))) = 2 := by
  refl

theorem map_id (l : List Nat) : map(fun x : Nat => x, l) = l := by
  induction l with
  | nil =>
      refl
  | cons h t ih =>
      simp
      exact ih

-- Functions as values and extensionality.
theorem add_zero_fun : (fun n : Nat => n + 0) = (fun n : Nat => n) := by
  funext n
  refl

-- Case analysis on a data type variable, without induction hypotheses.
theorem zero_or_succ (n : Nat) : n = 0 \\/ exists k : Nat, n = succ(k) := by
  cases n with
  | zero =>
      left
      refl
  | succ k =>
      right
      exists k
      refl

-- A recursive predicate.
theorem two_in (x : Nat) : elem(x, cons(x, cons(1, nil))) := by
  exact elem_head

-- Membership in a finite set literal is decided by computation.
theorem wrong_list (l : List Nat) : length(l) = 0 := by
  induction l with
  | nil =>
      refl
  | cons h t ih =>
      simp
      exact ih
";
    let opts = Options {
        tier: Some(Tier::Hol),
        ..Options::default()
    };
    let result = Session::new(&fs, opts).check(Some("work/hw.ctea"), source);
    let statuses = statuses(&result);
    assert_eq!(
        statuses,
        vec![
            ("len_two".to_string(), DeclStatus::Accepted),
            ("map_id".to_string(), DeclStatus::Accepted),
            ("add_zero_fun".to_string(), DeclStatus::Accepted),
            ("zero_or_succ".to_string(), DeclStatus::Accepted),
            ("two_in".to_string(), DeclStatus::Accepted),
            ("wrong_list".to_string(), DeclStatus::Failed),
        ],
        "{:?}",
        result.diagnostics
    );
    let error = result
        .diagnostics
        .iter()
        .find(|d| d.severity == Severity::Error)
        .unwrap();
    assert!(
        error
            .notes
            .iter()
            .any(|n| n.contains("false when l = cons(")),
        "{:?}",
        error.notes
    );
}

#[test]
fn tier_one_and_two_reject_hol_features() {
    let source = "theorem fun_val (f : Nat -> Nat) : f = f := by\n  refl\n";
    let result = check(source, Some(Tier::FolNat));
    assert!(
        result.diagnostics[0].message.contains("needs `logic hol`"),
        "{:?}",
        result.diagnostics
    );
    let source = "data Bit\n| off\n| on\ntheorem t : off = off := by\n  refl\n";
    let result = check(source, Some(Tier::FolNat));
    assert!(
        result.diagnostics[0].message.contains("needs `logic hol`"),
        "{:?}",
        result.diagnostics
    );
    let result = check(source, Some(Tier::Hol));
    assert!(result.ok(), "{:?}", result.diagnostics);
}
