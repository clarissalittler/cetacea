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

#[test]
fn quantified_countermodel_reaches_browser_diagnostics() {
    let source = "sort U\ntheorem swap (R : U -> U -> Prop) : (forall y : U, exists x : U, R(x, y)) -> exists x : U, forall y : U, R(x, y) := by\n  show_goal\n";
    let json: serde_json::Value = serde_json::from_str(&analyze_json(source, "{}")).unwrap();
    assert_eq!(json["ok"], false);
    assert_eq!(json["declarations"][0]["status"], "failed");
    assert!(json["diagnostics"].as_array().unwrap().iter().any(|diag| {
        diag["notes"].as_array().unwrap().iter().any(|note| {
            let text = note.as_str().unwrap();
            text.contains("first-order statement is false")
                && text.contains("U = {a, b} (2 elements)")
                && text.contains("R : U -> U -> Prop")
        })
    }));
}

#[test]
fn a_course_section_in_the_request_sets_tier_and_rules() {
    let source = "theorem t (P Q : Prop) : P /\\ Q -> Q /\\ P := by\n  intro h\n  cases h with\n  | intro hp hq =>\n      split\n      exact hq\n      exact hp\n";
    let options = r#"{"tier":"hol","section":"week1","course":{"title":"Demo","sections":[
        {"id":"week1","title":"Week 1","tier":"fol","allow_tactics":["intro","exact","split"]}]}}"#;
    let json: serde_json::Value = serde_json::from_str(&analyze_json(source, options)).unwrap();
    assert_eq!(json["ok"], false);
    assert_eq!(json["tier"], "fol");
    assert_eq!(json["rules"]["section"], "Week 1");
    assert_eq!(json["declarations"][0]["status"], "accepted");
    let diag = &json["diagnostics"][0];
    assert_eq!(diag["line"], 3);
    assert_eq!(
        diag["message"],
        "`cases` is not available in the section `Week 1`"
    );

    let unknown = r#"{"section":"week9","course":{"sections":[{"id":"week1"}]}}"#;
    let json: serde_json::Value = serde_json::from_str(&analyze_json(source, unknown)).unwrap();
    assert!(json["error"]
        .as_str()
        .unwrap()
        .contains("there is no section `week9`"));
}
