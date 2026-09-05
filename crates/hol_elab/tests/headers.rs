//! Elaborate declarations and theorem headers and print the statements
//! back in surface syntax.

use std::path::Path;

use hol_elab::{elab_command, elab_theorem_header, new_env, print_term, Env};
use hol_syntax::{parse_file, Command};

/// Elaborates every command of a file except proofs, returning printed
/// theorem statements by name and any diagnostics.
fn run(env: &mut Env, source: &str) -> (Vec<(String, String)>, Vec<String>) {
    let parsed = parse_file(source);
    assert!(parsed.errors.is_empty(), "{:?}", parsed.errors);
    let mut statements = Vec::new();
    let mut errors = Vec::new();
    for command in &parsed.file.commands {
        match command {
            Command::Import { .. } => {}
            Command::Theorem {
                name,
                params,
                statement,
                span,
                ..
            } => match elab_theorem_header(env, name, params, statement, *span) {
                Ok(header) => {
                    statements.push((name.name.clone(), print_term(env, &header.statement)));
                }
                Err(diag) => errors.push(format!("{}:{}: {}", name.name, diag.span, diag.message)),
            },
            other => {
                if let Err(diag) = elab_command(env, other) {
                    errors.push(format!("{}: {}", diag.span, diag.message));
                }
            }
        }
    }
    (statements, errors)
}

fn statement_text(source: &str, name: &str) -> String {
    // The statement as written: between `:` after the params and `:= by`,
    // whitespace-normalized.
    let start = source.find(&format!("theorem {name}")).unwrap();
    let rest = &source[start..];
    let end = rest.find(":= by").unwrap();
    let header = &rest[..end];
    let colon = header.rfind("\n  : ").map(|i| i + 4).unwrap_or_else(|| {
        // single-line header: statement follows the last `) :` or `name :`
        let params_end = header
            .rfind(") :")
            .map(|i| i + 3)
            .unwrap_or_else(|| header.find(':').unwrap() + 1);
        params_end
    });
    header[colon..]
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

#[test]
fn standard_library_headers_round_trip() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut env = new_env();
    let mut mismatches = Vec::new();
    let mut count = 0;
    for file in [
        "std/prop.ctea",
        "std/fol.ctea",
        "std/eq.ctea",
        "std/set.ctea",
    ] {
        let source = std::fs::read_to_string(root.join(file)).unwrap();
        let (statements, errors) = run(&mut env, &source);
        assert!(errors.is_empty(), "{file}: {}", errors.join("\n"));
        for (name, printed) in statements {
            count += 1;
            let mut written = statement_text(&source, &name);
            // `P -> False` prints as `not P`.
            written = written
                .replace("(x in A -> False)", "not x in A")
                .replace("x in A -> False", "not x in A");
            if written != printed {
                mismatches.push(format!(
                    "{file} {name}:\n  written: {written}\n  printed: {printed}"
                ));
            }
        }
    }
    assert!(count > 60);
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

#[test]
fn tier_one_rejects_higher_order_features() {
    let mut env = new_env();
    let source = "sort Person\npred Happy(Person)\ntheorem bad (f : Person -> Person) : f = f := by\n  refl\n";
    let (_, errors) = run(&mut env, source);
    assert!(
        errors.iter().any(|e| e.contains("needs `logic hol`")),
        "{errors:?}"
    );

    let source = "theorem num : 2 = 2 := by\n  refl\n";
    let (_, errors) = run(&mut env, source);
    assert!(
        errors.iter().any(|e| e.contains("needs natural numbers")),
        "{errors:?}"
    );

    let source = "theorem arity : Happy -> True := by\n  trivial\n";
    let (_, errors) = run(&mut env, source);
    assert!(
        errors.iter().any(|e| e.contains("takes 1 argument")),
        "{errors:?}"
    );

    let source = "theorem unknown : Sad(alice) := by\n  trivial\n";
    let (_, errors) = run(&mut env, source);
    assert!(
        errors.iter().any(|e| e.contains("unknown name `Sad`")),
        "{errors:?}"
    );
}

#[test]
fn definitions_hypothesis_params_and_sets() {
    let mut env = new_env();
    let source = "\
sort Person
pred Happy(Person)
const alice : Person
def Reflexive (T : Type) (R : T -> T -> Prop) : Prop := forall x : T, R(x, x)
def SameMood (x y : Person) : Prop := Happy(x) <-> Happy(y)
def HappySet : Set Person := { x : Person | Happy(x) }
theorem with_hyp (P Q : Prop) (h : P) : Q -> P := by
  intro hq
  exact h
theorem refl_same : Reflexive(SameMood) := by
  sorry
theorem lit : alice in {alice} := by
  sorry
theorem pw (A B : Set Person) : B in powerset(A) <-> B subset A := by
  sorry
theorem lam : Reflexive(fun x y : Person => x = y) := by
  sorry
theorem em (T : Type) (A : Set T) : empty(T) subset A := by
  sorry
";
    let (statements, errors) = run(&mut env, source);
    assert!(errors.is_empty(), "{}", errors.join("\n"));
    let get = |name: &str| {
        statements
            .iter()
            .find(|(n, _)| n == name)
            .unwrap()
            .1
            .clone()
    };
    assert_eq!(get("with_hyp"), "P -> Q -> P");
    assert_eq!(get("refl_same"), "Reflexive(SameMood)");
    assert_eq!(get("lit"), "alice in singleton(alice)");
    assert_eq!(get("pw"), "B in powerset(A) <-> B subset A");
    assert_eq!(get("lam"), "Reflexive(fun x y : Person => x = y)");
    assert_eq!(get("em"), "empty(T) subset A");
    let def = env.def("SameMood").unwrap();
    assert_eq!(
        print_term(&env, def.equation.concl()),
        "SameMood = fun x y : Person => Happy(x) <-> Happy(y)"
    );
    assert!(
        env.theorem("with_hyp").is_none(),
        "headers are not theorems yet"
    );
}
