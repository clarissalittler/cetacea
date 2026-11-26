//! Course sections: allowed and disallowed tactics and theorems.

use hol_session::{
    analyze, hints, CheckResult, Course, DeclStatus, Options, Policy, Session, Severity, VirtualFs,
};

const LIB: &str = "theorem and_swap (P Q : Prop) : P /\\ Q -> Q /\\ P := by\n  intro h\n  split\n  exact h.right\n  exact h.left\n\ntheorem or_swap (P Q : Prop) : P \\/ Q -> Q \\/ P := by\n  intro h\n  cases h with\n  | left hp =>\n      right\n      exact hp\n  | right hq =>\n      left\n      exact hq\n";

fn fs() -> VirtualFs {
    let mut fs = VirtualFs::default();
    fs.add("lib.ctea", LIB);
    fs
}

fn check(source: &str, policy: Policy) -> CheckResult {
    let fs = fs();
    let opts = Options {
        policy,
        ..Options::default()
    };
    Session::new(&fs, opts).check(Some("hw.ctea"), source)
}

fn names(items: &[&str]) -> Vec<String> {
    items.iter().map(|s| s.to_string()).collect()
}

fn errors(result: &CheckResult) -> Vec<(u32, String)> {
    result
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| (d.line, d.message.clone()))
        .collect()
}

#[test]
fn an_allow_list_reports_other_tactics_where_they_are_written() {
    let source = "theorem t (P Q : Prop) : P /\\ Q -> Q /\\ P := by\n  intro h\n  cases h with\n  | intro hp hq =>\n      split\n      exact hq\n      exact hp\n";
    let policy = Policy {
        allow_tactics: Some(names(&["intro", "exact", "split"])),
        section: Some("Week 1".to_string()),
        ..Policy::default()
    };
    let result = check(source, policy);
    assert_eq!(
        errors(&result),
        vec![(
            3,
            "`cases` is not available in the section `Week 1`".to_string()
        )]
    );
    let diag = &result.diagnostics[0];
    assert_eq!(
        diag.notes,
        vec!["tactics available here: intro, exact, split"]
    );
    // The proof is still a proof: the rule is about the course, not logic.
    assert_eq!(result.decls[0].status, DeclStatus::Accepted);
    assert!(!result.ok());
    assert_eq!(
        result.violations,
        vec!["theorem `t` uses `cases`, which the section `Week 1` does not allow"]
    );
    assert_eq!(result.located_violations, result.violations);
}

#[test]
fn nested_blocks_are_covered_and_sorry_stays_available() {
    let source = "theorem t (P Q : Prop) : P \\/ Q -> Q \\/ P := by\n  intro h\n  show Q \\/ P\n  cases h with\n  | left hp =>\n      have hq : Q \\/ P := by\n        simp\n        right\n        exact hp\n      exact hq\n  | right hq =>\n      sorry\n";
    let policy = Policy {
        allow_tactics: Some(names(&[
            "intro", "exact", "cases", "have", "left", "right", "show",
        ])),
        ..Policy::default()
    };
    let result = check(source, policy);
    assert_eq!(
        errors(&result),
        vec![(7, "`simp` is not available in this assignment".to_string())]
    );
    // `sorry` is governed by `deny_sorry`, not by the tactic list.
    assert_eq!(result.decls[0].status, DeclStatus::Incomplete);
}

#[test]
fn a_denied_tactic_stays_denied_even_when_listed() {
    let policy = Policy {
        allow_tactics: Some(names(&["intro", "exact", "simp"])),
        deny_tactics: names(&["simp"]),
        ..Policy::default()
    };
    let result = check(
        "theorem t (P : Prop) : P -> P := by\n  intro h\n  simp\n  exact h\n",
        policy,
    );
    assert_eq!(
        errors(&result),
        vec![(3, "`simp` is not allowed in this assignment".to_string())]
    );
    assert_eq!(
        result.diagnostics[0].notes,
        vec!["tactics available here: intro, exact"]
    );
}

#[test]
fn library_theorems_can_be_closed_while_local_ones_stay_open() {
    let source = "import lib.ctea\n\ntheorem mine (P Q : Prop) : P /\\ Q -> Q /\\ P := by\n  intro h\n  split\n  exact h.right\n  exact h.left\n\ntheorem uses_mine (A B : Prop) : A /\\ B -> B /\\ A := by\n  intro h\n  exact mine h\n\ntheorem uses_lib (A B : Prop) : A /\\ B -> B /\\ A := by\n  intro h\n  exact and_swap h\n";
    let policy = Policy {
        allow_theorems: Some(Vec::new()),
        ..Policy::default()
    };
    let result = check(source, policy);
    assert_eq!(
        errors(&result),
        vec![(
            15,
            "the theorem `and_swap` is not available in this assignment".to_string()
        )]
    );
    assert_eq!(
        result.violations,
        vec!["theorem `uses_lib` cites `and_swap`, which this assignment does not allow"]
    );
    let uses_lib = result.decls.iter().find(|d| d.name == "uses_lib").unwrap();
    assert_eq!(uses_lib.theorems, vec!["and_swap"]);
    let uses_mine = result.decls.iter().find(|d| d.name == "uses_mine").unwrap();
    assert!(uses_mine.theorems.is_empty());
}

#[test]
fn theorem_patterns_allow_and_deny() {
    let source = "import lib.ctea\n\ntheorem a (A B : Prop) : A /\\ B -> B /\\ A := by\n  intro h\n  exact and_swap h\n\ntheorem b (A B : Prop) : A \\/ B -> B \\/ A := by\n  intro h\n  exact or_swap {P := A; Q := B} h\n";
    let allow_and = Policy {
        allow_theorems: Some(names(&["and_*"])),
        ..Policy::default()
    };
    assert_eq!(
        errors(&check(source, allow_and)),
        vec![(
            9,
            "the theorem `or_swap` is not available in this assignment".to_string()
        )]
    );
    let deny_swap = Policy {
        deny_theorems: names(&["*_swap"]),
        ..Policy::default()
    };
    assert_eq!(errors(&check(source, deny_swap)).len(), 2);
    assert!(check(source, Policy::default()).ok());
}

#[test]
fn a_hypothesis_named_like_a_theorem_is_not_a_citation() {
    let source = "import lib.ctea\n\ntheorem t (A B : Prop) : (A /\\ B -> B /\\ A) -> A /\\ B -> B /\\ A := by\n  intro and_swap\n  intro h\n  exact and_swap h\n";
    let policy = Policy {
        allow_theorems: Some(Vec::new()),
        ..Policy::default()
    };
    let result = check(source, policy);
    assert!(result.ok(), "{:?}", errors(&result));
}

#[test]
fn a_failed_proof_still_reports_what_it_used() {
    let source = "import lib.ctea\n\ntheorem t (A B : Prop) : A /\\ B -> B /\\ A := by\n  intro h\n  simp\n  have k : B /\\ A := and_swap h\n";
    let policy = Policy {
        deny_tactics: names(&["simp"]),
        deny_theorems: names(&["and_swap"]),
        ..Policy::default()
    };
    let result = check(source, policy);
    assert_eq!(result.decls.last().unwrap().status, DeclStatus::Failed);
    let messages: Vec<String> = errors(&result).into_iter().map(|(_, m)| m).collect();
    assert!(messages
        .iter()
        .any(|m| m == "`simp` is not allowed in this assignment"));
    assert!(messages
        .iter()
        .any(|m| m == "the theorem `and_swap` is not allowed in this assignment"));
}

#[test]
fn advisory_rules_warn_without_failing() {
    let policy = Policy {
        deny_tactics: names(&["simp"]),
        advisory: true,
        ..Policy::default()
    };
    let result = check(
        "theorem t (P : Prop) : P -> P := by\n  intro h\n  simp\n  exact h\n",
        policy,
    );
    assert!(result.ok());
    assert!(result.violations.is_empty());
    assert!(result.diagnostics.iter().any(|d| {
        d.severity == Severity::Warning && d.message == "`simp` is not allowed in this assignment"
    }));
}

#[test]
fn sections_drive_a_whole_check() {
    let course = Course::parse(
        r#"{"title":"Demo","sections":[
            {"id":"rules","title":"Rules only","tier":"fol",
             "allow_tactics":["intro","exact","split"],"allow_theorems":[]},
            {"id":"library","title":"With the library","extends":"rules",
             "allow_tactics":["cases","left","right"],"allow_theorems":["and_*"]}
        ]}"#,
    )
    .unwrap();
    let source = "import lib.ctea\n\ntheorem t (A B : Prop) : A /\\ B -> B /\\ A := by\n  intro h\n  exact and_swap h\n";
    let early = check(source, course.resolve("rules").unwrap().policy);
    assert_eq!(
        errors(&early),
        vec![(
            5,
            "the theorem `and_swap` is not available in the section `Rules only`".to_string()
        )]
    );
    let later = check(source, course.resolve("library").unwrap().policy);
    assert!(later.ok(), "{:?}", errors(&later));
}

#[test]
fn hints_never_suggest_what_the_section_forbids() {
    let fs = fs();
    let source = "import lib.ctea\n\ntheorem t (A B : Prop) : A /\\ B -> B /\\ A := by\n  intro h\n  sorry\n";
    let open = Options::default();
    let all: Vec<String> = hints(&fs, open, Some("hw.ctea"), source, 4)
        .into_iter()
        .map(|h| h.tactic)
        .collect();
    assert!(all.iter().any(|t| t == "split"), "{all:?}");
    assert!(all.iter().any(|t| t.contains("and_swap")), "{all:?}");
    let restricted = Options {
        policy: Policy {
            allow_tactics: Some(names(&["intro", "exact", "apply", "cases"])),
            allow_theorems: Some(Vec::new()),
            ..Policy::default()
        },
        ..Options::default()
    };
    let some: Vec<String> = hints(&fs, restricted, Some("hw.ctea"), source, 4)
        .into_iter()
        .map(|h| h.tactic)
        .collect();
    assert!(!some.iter().any(|t| t == "split"), "{some:?}");
    assert!(!some.iter().any(|t| t.contains("and_swap")), "{some:?}");
}

#[test]
fn the_analysis_describes_the_rules_and_marks_the_library() {
    let fs = fs();
    let policy = Policy {
        allow_tactics: Some(names(&["intro", "exact"])),
        allow_theorems: Some(names(&["and_*"])),
        section: Some("Week 2".to_string()),
        ..Policy::default()
    };
    let opts = Options {
        policy,
        ..Options::default()
    };
    let source =
        "import lib.ctea\n\ntheorem mine (P : Prop) : P -> P := by\n  intro h\n  exact h\n";
    let analysis = analyze(&fs, opts, Some("hw.ctea"), source, None);
    let rules = analysis.rules.expect("a restricting policy is described");
    assert_eq!(rules.section.as_deref(), Some("Week 2"));
    assert_eq!(rules.tactics_available, Some(names(&["intro", "exact"])));
    assert!(rules.restricts_theorems);
    let allowed = |name: &str| {
        analysis
            .library
            .iter()
            .find(|e| e.name == name)
            .map(|e| e.allowed)
    };
    assert_eq!(allowed("and_swap"), Some(true));
    assert_eq!(allowed("or_swap"), Some(false));
    assert_eq!(allowed("mine"), Some(true));
    let unrestricted = analyze(&fs, Options::default(), Some("hw.ctea"), source, None);
    assert!(unrestricted.rules.is_none());
}
