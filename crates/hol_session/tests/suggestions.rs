//! Diagnostics that point somewhere useful: misspelled names and the
//! wording of countermodels.

use hol_session::{Options, Session, VirtualFs};

fn messages(source: &str) -> Vec<String> {
    let mut fs = VirtualFs::default();
    fs.add(
        "nat.ctea",
        "theorem add_zero_right (P : Prop) : P -> P := by\n  intro h\n  exact h\n",
    );
    let result = Session::new(&fs, Options::default()).check(Some("hw.ctea"), source);
    result
        .diagnostics
        .iter()
        .flat_map(|d| std::iter::once(d.message.clone()).chain(d.notes.iter().cloned()))
        .collect()
}

#[test]
fn a_misspelled_tactic_is_suggested() {
    let found = messages("theorem t (P : Prop) : P -> P := by\n  intro h\n  exatc h\n");
    assert!(
        found.contains(&"unknown tactic `exatc`; did you mean `exact`?".to_string()),
        "{found:?}"
    );
    // A different word is not a typo.
    let found = messages("theorem t (P : Prop) : P -> P := by\n  intro h\n  omega\n");
    assert!(
        found.contains(&"unknown tactic `omega`".to_string()),
        "{found:?}"
    );
}

#[test]
fn a_misspelled_theorem_or_hypothesis_is_suggested() {
    let found = messages(
        "import nat.ctea\n\ntheorem t (P : Prop) : P -> P := by\n  intro h\n  exact add_zero_rigth h\n",
    );
    assert!(
        found.contains(&"did you mean `add_zero_right`?".to_string()),
        "{found:?}"
    );
    let found = messages("theorem t (P : Prop) : P -> P := by\n  intro hyp\n  exact hpy\n");
    assert!(
        found.contains(&"did you mean `hyp`?".to_string()),
        "{found:?}"
    );
    let found = messages(
        "import nat.ctea\n\ntheorem t (P : Prop) : P -> P := by\n  intro h\n  exact add_zero_rigth {P := P} h\n",
    );
    assert!(
        found.contains(&"theorem `t` failed: unknown theorem `add_zero_rigth`".to_string())
            && found.contains(&"did you mean `add_zero_right`?".to_string()),
        "{found:?}"
    );
}

#[test]
fn a_statement_with_no_atoms_is_described_in_plain_words() {
    let found = messages("theorem t : False := by\n  trivial\n");
    assert!(
        found.iter().any(|m| m
            == "the statement is not a tautology: it is false however its propositions are read. No proof can close it; check the statement itself."),
        "{found:?}"
    );
    let found = messages("theorem t (P Q : Prop) : P -> Q := by\n  intro h\n  exact h\n");
    assert!(
        found
            .iter()
            .any(|m| m.contains("it is false when P = true, Q = false")),
        "{found:?}"
    );
}
