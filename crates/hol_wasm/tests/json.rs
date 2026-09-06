//! The JSON shapes the browser relies on.

use hol_wasm::{analyze_json, hints_json};

const SOURCE: &str = "import ../std/prelude.ctea\n\nsort Person\npred Happy(Person)\n\ntheorem and_comm (P Q : Prop) : P /\\ Q -> Q /\\ P := by\n  intro h\n  split\n  exact h.right\n  exact h.left\n\ntheorem stuck (P Q : Prop) : P /\\ Q -> P := by\n  intro h\n";

#[test]
fn analysis_has_declarations_steps_and_library() {
    let text = analyze_json(SOURCE, "{}");
    let json: serde_json::Value = serde_json::from_str(&text).unwrap();
    assert_eq!(json["ok"], false);
    assert_eq!(json["tier"], "fol");
    let decls = json["declarations"].as_array().unwrap();
    let local: Vec<&serde_json::Value> =
        decls.iter().filter(|d| d["is_imported"] == false).collect();
    assert_eq!(local.len(), 2);
    assert_eq!(local[0]["status"], "accepted");
    assert_eq!(local[1]["status"], "failed");
    let theorems = json["theorems"].as_array().unwrap();
    assert_eq!(theorems[0]["name"], "and_comm");
    let steps = theorems[0]["steps"].as_array().unwrap();
    assert_eq!(steps.len(), 4);
    assert_eq!(steps[0]["text"], "intro h");
    assert!(steps[0]["explanation"]
        .as_str()
        .unwrap()
        .starts_with("Assume `P /\\ Q` as `h`"));
    assert_eq!(steps[1]["after"].as_array().unwrap().len(), 2);
    let library = json["library"].as_array().unwrap();
    assert!(library
        .iter()
        .any(|e| e["name"] == "forall_mono" && e["is_imported"] == true));
    assert!(library
        .iter()
        .any(|e| e["name"] == "and_comm" && e["is_imported"] == false));
    let diagnostics = json["diagnostics"].as_array().unwrap();
    assert!(diagnostics
        .iter()
        .any(|d| d["message"].as_str().unwrap().contains("incomplete")));
}

#[test]
fn hints_are_verified_by_running_them() {
    let text = hints_json(SOURCE, "{}", 13);
    let hints: Vec<serde_json::Value> = serde_json::from_str(&text).unwrap();
    let tactics: Vec<&str> = hints
        .iter()
        .map(|h| h["tactic"].as_str().unwrap())
        .collect();
    assert!(tactics.contains(&"exact h.left"), "{tactics:?}");
    assert!(
        !tactics.contains(&"split"),
        "split fails on `P`: {tactics:?}"
    );
    assert!(
        !tactics.contains(&"exact h"),
        "`exact h` fails: {tactics:?}"
    );
    let closing = hints
        .iter()
        .find(|h| h["tactic"] == "exact h.left")
        .unwrap();
    assert_eq!(closing["closes_goal"], true);
}
