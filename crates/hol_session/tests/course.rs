//! Course workflow: tactic policies and assignment manifests.

use hol_session::{
    check_manifest, manifest_from_result, Manifest, Options, Policy, Session, VirtualFs,
};

fn check(source: &str, policy: Policy) -> hol_session::CheckResult {
    let fs = VirtualFs::default();
    let opts = Options {
        policy,
        ..Options::default()
    };
    Session::new(&fs, opts).check(Some("hw.ctea"), source)
}

#[test]
fn deny_tactics_reports_forbidden_tactics() {
    let source = "sort T\npred P(T)\ntheorem t (x : T) : P(x) -> P(x) := by\n  intro h\n  cases h with\n  | intro a b =>\n      sorry\n";
    let source = source.replace(
        "cases h with\n  | intro a b =>\n      sorry",
        "simp\n  exact h",
    );
    let result = check(
        &source,
        Policy {
            deny_tactics: vec!["simp".to_string()],
            ..Policy::default()
        },
    );
    assert_eq!(
        result.violations,
        vec!["theorem `t` uses `simp`, which this assignment does not allow".to_string()]
    );
    assert_eq!(result.decls[0].tactics, vec!["exact", "intro", "simp"]);
}

#[test]
fn manifests_pin_statements_and_imports() {
    let skeleton = "import ../std/prelude.ctea\n\ntheorem hw1 (P Q : Prop) : P /\\ Q -> Q /\\ P := by\n  sorry\n\ntheorem hw2 (P : Prop) : P -> P := by\n  sorry\n";
    let mut fs = VirtualFs::default();
    fs.add("lib/prelude.ctea", "");
    let opts = Options {
        std_dir: Some("lib".to_string()),
        ..Options::default()
    };
    let result = Session::new(&fs, opts.clone()).check(Some("work/hw.ctea"), skeleton);
    let manifest = manifest_from_result(&result, "Homework 1", Some("fol"));
    assert_eq!(manifest.theorems.len(), 2);
    assert_eq!(manifest.theorems[0].statement, "P /\\ Q -> Q /\\ P");
    assert_eq!(
        manifest.allowed_imports,
        vec!["std/prelude.ctea".to_string()]
    );
    let json = serde_json::to_string(&manifest).unwrap();
    let manifest: Manifest = serde_json::from_str(&json).unwrap();

    // A complete submission.
    let good = "import ../std/prelude.ctea\n\ntheorem hw1 (P Q : Prop) : P /\\ Q -> Q /\\ P := by\n  intro h\n  split\n  exact h.right\n  exact h.left\n\ntheorem hw2 (P : Prop) : P -> P := by\n  intro h\n  exact h\n";
    let result = Session::new(&fs, opts.clone()).check(Some("work/hw.ctea"), good);
    let report = check_manifest(&result, &manifest);
    assert!(report.violations.is_empty(), "{:?}", report.violations);
    assert!(report.complete);

    // A submission that weakens a statement, drops a theorem, and imports
    // something else.
    let bad = "import ../std/prelude.ctea\nimport ../lib/secret.ctea\n\ntheorem hw1 (P Q : Prop) : P /\\ Q -> P /\\ Q := by\n  intro h\n  exact h\n";
    fs.add("lib/secret.ctea", "");
    let result = Session::new(&fs, opts).check(Some("work/hw.ctea"), bad);
    let report = check_manifest(&result, &manifest);
    assert_eq!(report.violations.len(), 3, "{:?}", report.violations);
    assert!(report.violations[0].contains("not allowed"));
    assert!(report.violations[1].contains("statement of `hw1` was changed"));
    assert!(report.violations[2].contains("`hw2` is missing"));
    assert!(!report.complete);
    assert_eq!(report.theorems[0].status, "changed");
    assert_eq!(report.theorems[1].status, "missing");
}
