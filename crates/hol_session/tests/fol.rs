use hol_kernel::Term;
use hol_session::fol::{first_order_countermodel, FiniteModel};
use hol_session::{CheckResult, Options, Session, Severity, VirtualFs};

fn check(source: &str) -> CheckResult {
    Session::new(&VirtualFs::default(), Options::default()).check(Some("quantifiers.ctea"), source)
}

fn model(source: &str) -> Option<FiniteModel> {
    let result = check(source);
    let statement = &result
        .env
        .theorem("test")
        .unwrap_or_else(|| panic!("{:?}", result.diagnostics))
        .statement;
    first_order_countermodel(&result.env, statement)
}

fn notes(result: &CheckResult) -> Vec<&str> {
    result
        .diagnostics
        .iter()
        .filter(|diag| diag.severity == Severity::Error)
        .flat_map(|diag| diag.notes.iter().map(String::as_str))
        .collect()
}

const SWAP: &str = "sort U
theorem test (R : U -> U -> Prop)
  : (forall y : U, exists x : U, R(x, y)) -> exists x : U, forall y : U, R(x, y) := by
  show_goal
";

#[test]
fn quantifier_swap_has_a_genuine_two_element_countermodel() {
    let found = model(SWAP).expect("countermodel");
    assert_eq!(found.domains.len(), 1);
    assert_eq!(found.domains[0].1, 2);
    let relation = &found.interpretations[0];
    assert_eq!(relation.arguments, vec![0, 0]);
    assert_eq!(relation.result, None);
    let size = found.domains[0].1;
    assert!((0..size).all(|right| (0..size).any(|left| relation.values[left * size + right] == 1)));
    assert!(!(0..size).any(|left| (0..size).all(|right| relation.values[left * size + right] == 1)));
    assert_eq!(model(SWAP), Some(found.clone()));
    assert!(found.describe().contains("U = {a, b} (2 elements)"));
    let result = check(SWAP);
    assert!(notes(&result)
        .iter()
        .any(|note| note.contains("first-order statement is false")));
    assert!(!result.ok());
}

#[test]
fn valid_quantifier_direction_and_shadowing_do_not_get_countermodels() {
    for claim in [
        "(exists x : U, forall y : U, R(x, y)) -> forall y : U, exists x : U, R(x, y)",
        "(forall x : U, R(x, x)) -> forall x : U, exists y : U, R(x, y)",
        "(forall x : U, exists x : U, R(x, x)) <-> exists y : U, R(y, y)",
        "(forall x : U, R(x, x)) -> R(a, a)",
    ] {
        let source = format!(
            "sort U\nconst a : U\ntheorem test (R : U -> U -> Prop) : {claim} := by\n  show_goal\n"
        );
        assert!(model(&source).is_none(), "{claim}");
        assert!(
            !notes(&check(&source))
                .iter()
                .any(|note| note.contains("false in")),
            "{claim}"
        );
    }
}

#[test]
fn equality_constants_and_total_functions_are_not_independent_atoms() {
    for claim in [
        "forall x : U, x = x",
        "a = b -> P(a) -> P(b)",
        "a = b -> f(a) = f(b)",
        "a = b -> b = c -> a = c",
        "exists x : U, x = a",
    ] {
        let source = format!("sort U\nconst a : U\nconst b : U\nconst c : U\npred P(U)\nfunc f : U -> U\ntheorem test : {claim} := by\n  show_goal\n");
        assert!(model(&source).is_none(), "{claim}");
    }
    let aliases =
        model("sort U\nconst a : U\nconst b : U\ntheorem test : not a = b := by\n  show_goal\n")
            .unwrap();
    assert_eq!(aliases.domains[0].1, 1);
    assert!(aliases
        .interpretations
        .iter()
        .all(|entry| entry.values == vec![0]));
    let function = model(
        "sort U\nfunc f : U -> U\ntheorem test : forall x : U, f(x) = x := by\n  show_goal\n",
    )
    .unwrap();
    assert_eq!(function.domains[0].1, 2);
    assert!(function.interpretations[0]
        .values
        .iter()
        .enumerate()
        .any(|(input, output)| input != *output));
    assert!(function.describe().contains("->"));
}

#[test]
fn sorts_have_independent_nonempty_domains() {
    let found = model("sort A\nsort B\ntheorem test : (forall x y : A, x = y) -> forall z w : B, z = w := by\n  show_goal\n").unwrap();
    assert_eq!(
        found
            .domains
            .iter()
            .map(|(_, size)| *size)
            .collect::<Vec<_>>(),
        vec![1, 2]
    );
    assert!(model("theorem test (A : Type) (R : A -> A -> Prop) : (forall y : A, exists x : A, R(x,y)) -> exists x : A, forall y : A, R(x,y) := by\n  show_goal\n").is_some());
}

#[test]
fn search_reaches_three_elements_and_silently_stops_beyond_its_bound() {
    let three = model(
        "sort U\ntheorem test : forall x y z : U, x = y \\/ x = z \\/ y = z := by\n  show_goal\n",
    )
    .unwrap();
    assert_eq!(three.domains[0].1, 3);
    let four = "sort U\ntheorem test : forall x y z w : U, x = y \\/ x = z \\/ x = w \\/ y = z \\/ y = w \\/ z = w := by\n  show_goal\n";
    assert!(model(four).is_none());
    let result = check(four);
    assert!(!result.ok());
    assert!(!notes(&result)
        .iter()
        .any(|note| note.contains("finite world") || note.contains("valid")));
}

#[test]
fn symbol_identity_preserves_repeated_predicate_applications() {
    let source = "sort U\nconst a : U\npred P(U)\ntheorem test : P(a) -> P(a) := by\n  show_goal\n";
    assert!(model(source).is_none());
    let invalid = "sort U\nconst a : U\npred P(U)\ntheorem test : P(a) := by\n  show_goal\n";
    let found = model(invalid).unwrap();
    assert!(found.describe().contains("P : U -> Prop = {}"));
    assert!(notes(&check(invalid))
        .iter()
        .any(|note| note.contains("finite world")));
}

#[test]
fn all_axioms_constrain_the_world_and_unsupported_axioms_decline() {
    for source in [
        "sort U\npred P(U)\naxiom all : forall x : U, P(x)\ntheorem test : forall x : U, P(x) := by\n  show_goal\n",
        "sort U\npred P(U)\naxiom all (x : U) : P(x)\ntheorem test : forall x : U, P(x) := by\n  show_goal\n",
        "sort U\npred P(U)\naxiom contradiction : False\ntheorem test : forall x : U, P(x) := by\n  show_goal\n",
        "sort U\npred P(U)\naxiom schema (A : Type) (x y : A) : x = y\ntheorem test : forall x : U, P(x) := by\n  show_goal\n",
        "logic fol_nat\nsort U\npred P(U)\naxiom arithmetic : 1 = 2\ntheorem test : forall x : U, P(x) := by\n  show_goal\n",
    ] {
        assert!(model(source).is_none(), "{source}");
        assert!(!notes(&check(source)).iter().any(|note| note.contains("No proof can close")), "{source}");
    }
    let found = model("sort U\npred P(U)\nconst a : U\naxiom witness : P(a)\ntheorem test : forall x : U, P(x) := by\n  show_goal\n").unwrap();
    let predicate = found
        .interpretations
        .iter()
        .find(|entry| entry.arguments.len() == 1)
        .unwrap();
    let constant = found
        .interpretations
        .iter()
        .find(|entry| entry.arguments.is_empty())
        .unwrap();
    assert_eq!(predicate.values[constant.values[0]], 1);
    assert!(predicate.values.contains(&0));
}

#[test]
fn defined_and_interpreted_symbols_are_not_reported_as_arbitrary_relations() {
    for source in [
        "sort U\ndef Always (x : U) : Prop := True\ntheorem test : forall x : U, Always(x) := by\n  show_goal\n",
        "sort U\nconst a : U\ndef Always (x : U) : Prop := True\ntheorem test : Always(a) := by\n  show_goal\n",
        "logic fol_nat\ntheorem test : forall n : Nat, n = n := by\n  show_goal\n",
        "logic hol\ndata Bit\n| off\n| on\ntheorem test : not off = on := by\n  show_goal\n",
        "sort U\ntheorem test (S : Set U) : S = S := by\n  show_goal\n",
        "logic hol\ntheorem test : forall P : Prop, P -> P := by\n  show_goal\n",
    ] {
        assert!(model(source).is_none(), "{source}");
        assert!(!notes(&check(source)).iter().any(|note| note.contains("No proof can close")), "{source}");
    }
}

#[test]
fn a_bad_witness_is_an_open_goal_countermodel_not_a_false_statement() {
    let result = check("sort U\nconst a : U\nconst b : U\npred P(U)\ntheorem test : (exists x : U, P(x)) -> exists x : U, P(x) := by\n  intro h\n  exists a\n  show_goal\n");
    let feedback = notes(&result);
    assert!(feedback.iter().any(|note| note.contains("open goal does not follow") && note.contains("finite world")), "{feedback:?}");
    assert!(!feedback
        .iter()
        .any(|note| note.contains("first-order statement is false")));
    let justified = check("sort U\nconst a : U\npred P(U)\ntheorem test : P(a) -> exists x : U, P(x) := by\n  intro h\n  exists a\n  show_goal\n");
    assert!(!notes(&justified)
        .iter()
        .any(|note| note.contains("false") || note.contains("does not follow")));
}

#[test]
fn limits_and_higher_order_inputs_decline_without_proving_validity() {
    let result = check("sort U\npred P(U)\ntheorem test : forall x : U, P(x) := by\n  sorry\n");
    let mut statement = result.env.theorem("test").unwrap().statement.clone();
    for _ in 0..80 {
        statement = Term::imp(&Term::true_(), &statement).unwrap();
    }
    assert!(first_order_countermodel(&result.env, &statement).is_none());
    assert!(model(
        "sort U\npred R(U,U,U,U)\ntheorem test : forall x : U, R(x,x,x,x) := by\n  show_goal\n"
    )
    .is_none());
}

#[test]
fn imported_axioms_are_respected_and_json_carries_feedback() {
    let mut files = VirtualFs::default();
    files.add(
        "facts.ctea",
        "sort U\npred P(U)\naxiom all : forall x : U, P(x)\n",
    );
    let result = Session::new(&files, Options::default()).check(
        Some("hw.ctea"),
        "import facts.ctea\ntheorem test : forall x : U, P(x) := by\n  show_goal\n",
    );
    assert!(!notes(&result)
        .iter()
        .any(|note| note.contains("No proof can close")));
    let serialized: serde_json::Value = serde_json::from_str(&check(SWAP).to_json()).unwrap();
    assert!(serialized["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .any(|diag| diag["notes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|note| note.as_str().unwrap().contains("U = {a, b}"))));
}
