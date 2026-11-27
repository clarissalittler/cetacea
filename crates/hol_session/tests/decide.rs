//! `decide`: evaluating statements with no unknowns.

use hol_session::{CheckResult, DeclStatus, Options, Policy, Session, Severity, VirtualFs};

const COLORS: &str = "logic hol\n\ndata Color\n| red\n| green\n| blue\n\ndefrec elem (A : Type) (x : A) (l : List A) : Prop on l\n| nil => False\n| cons h t => x = h \\/ elem(x, t)\n\n";
const LIST: &str = "data List (A : Type)\n| nil\n| cons(A, List A)\n\n";

fn check_with(body: &str, policy: Policy) -> CheckResult {
    let fs = VirtualFs::default();
    let source = COLORS.replacen("defrec", &format!("{LIST}defrec"), 1) + body;
    let opts = Options {
        policy,
        ..Options::default()
    };
    Session::new(&fs, opts).check(Some("hw.ctea"), &source)
}

fn check(body: &str) -> CheckResult {
    check_with(body, Policy::default())
}

/// The first error's message followed by its notes.
fn error(result: &CheckResult) -> Vec<String> {
    result
        .diagnostics
        .iter()
        .find(|d| d.severity == Severity::Error)
        .map(|d| {
            std::iter::once(d.message.clone())
                .chain(d.notes.iter().cloned())
                .collect()
        })
        .unwrap_or_default()
}

fn has(lines: &[String], needle: &str) -> bool {
    lines.iter().any(|line| line.contains(needle))
}

#[test]
fn closed_statements_are_evaluated() {
    let result = check(
        "theorem a : 3 * 4 = 12 /\\ 2 < 5 /\\ not (7 <= 3) := by\n  decide\n\n\
         theorem b : elem(green, cons(red, cons(green, nil))) := by\n  decide\n\n\
         theorem c : not elem(blue, cons(red, cons(green, nil))) := by\n  decide\n\n\
         theorem d : (red = red <-> True) /\\ (red = blue <-> False) := by\n  decide\n",
    );
    assert!(result.ok(), "{:?}", error(&result));
    // The proof is an ordinary one: nothing is assumed, nothing is classical.
    for decl in result.decls.iter().filter(|d| d.kind == "theorem") {
        assert_eq!(decl.status, DeclStatus::Accepted, "{}", decl.name);
        assert_eq!(decl.mode, "constructive", "{}", decl.name);
        assert!(decl.axioms.is_empty() && !decl.uses_sorry, "{}", decl.name);
    }
}

#[test]
fn quantifiers_over_an_enumeration_run_through_its_values() {
    let result = check(
        "theorem all : forall c : Color, c = red \\/ c = green \\/ c = blue := by\n  decide\n\n\
         theorem some : exists c : Color, not (c = red) /\\ not (c = green) := by\n  decide\n\n\
         theorem nested : forall c : Color, exists d : Color, not (c = d) := by\n  decide\n\n\
         theorem none : not (exists c : Color, c = red /\\ c = blue) := by\n  decide\n",
    );
    assert!(result.ok(), "{:?}", error(&result));
}

#[test]
fn a_false_statement_is_refused_and_the_false_part_is_named() {
    let result = check("theorem t : forall c : Color, c = red \\/ c = green := by\n  decide\n");
    let lines = error(&result);
    assert!(
        has(&lines, "`decide` evaluated the goal, and it is false"),
        "{lines:?}"
    );
    assert!(
        has(&lines, "this part is false: `blue = red \\/ blue = green`"),
        "{lines:?}"
    );
    assert!(has(&lines, "it fails when c = blue"), "{lines:?}");
    assert_eq!(result.decls.last().unwrap().status, DeclStatus::Failed);

    let result = check(
        "theorem t : elem(red, cons(red, nil)) /\\ elem(blue, cons(red, nil)) := by\n  decide\n",
    );
    let lines = error(&result);
    assert!(
        has(&lines, "this part is false: `elem(blue, cons(red, nil))`"),
        "{lines:?}"
    );

    let result = check("theorem t : 2 + 2 = 5 := by\n  decide\n");
    let lines = error(&result);
    assert!(
        has(&lines, "the two sides compute to `4` and `5`"),
        "{lines:?}"
    );
}

#[test]
fn what_cannot_be_evaluated_is_explained() {
    let result = check("theorem t : forall n m : Nat, n + m = m + n := by\n  decide\n");
    let lines = error(&result);
    assert!(
        has(&lines, "`decide` could not settle the goal"),
        "{lines:?}"
    );
    assert!(has(&lines, "it quantifies over `Nat`"), "{lines:?}");

    let result = check("theorem t (c : Color) (P : Prop) : c = red \\/ P := by\n  decide\n");
    let lines = error(&result);
    assert!(has(&lines, "it depends on `P` and `c`"), "{lines:?}");
}

#[test]
fn a_statement_true_at_every_value_needs_no_list_of_values() {
    let result = check("theorem t : forall n : Nat, n = n := by\n  decide\n");
    assert!(result.ok(), "{:?}", error(&result));
}

#[test]
fn a_section_can_leave_decide_out() {
    let policy = Policy {
        allow_tactics: Some(vec!["intro".to_string(), "exact".to_string()]),
        ..Policy::default()
    };
    let result = check_with("theorem t : 2 + 2 = 4 := by\n  decide\n", policy);
    let lines = error(&result);
    assert!(has(&lines, "`decide` is not available"), "{lines:?}");
}
