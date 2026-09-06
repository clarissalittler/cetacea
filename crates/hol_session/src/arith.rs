//! Arithmetic countermodels: a statement over `Nat` variables is tested
//! on small values by substituting numerals and normalizing with the
//! computation rules plus the decision rules (`x = x <-> True`,
//! propositional simplification). A statement that normalizes to `False`
//! for some assignment has no proof, and the assignment is reported.

use hol_elab::Env;
use hol_kernel::{Name, Term, Type};
use hol_tactics::{normal_form, Rules, Subst};

const MAX_VARS: usize = 3;
const MAX_VALUE: u64 = 6;

fn nat() -> Type {
    Type::con("Nat", vec![])
}

fn numeral(env: &Env, n: u64) -> Option<Term> {
    let zero = env.theory().constant("zero", nat()).ok()?;
    let succ = env
        .theory()
        .constant("succ", Type::fun(nat(), nat()))
        .ok()?;
    let mut term = zero;
    for _ in 0..n {
        term = Term::app(&succ, &term).ok()?;
    }
    Some(term)
}

fn has_binders(t: &Term) -> bool {
    t.dest_forall().is_some()
        || t.dest_exists().is_some()
        || t.is_lam()
        || match t.as_app() {
            Some((f, x)) => has_binders(f) || has_binders(x),
            None => false,
        }
}

/// Free variables in order of first occurrence, so reports read the way
/// the statement does.
fn free_vars_in_order(t: &Term) -> Vec<(Name, Type)> {
    fn walk(t: &Term, out: &mut Vec<(Name, Type)>) {
        match t.view() {
            hol_kernel::TermView::Free(name, ty) if !out.iter().any(|(n, _)| n == name) => {
                out.push((name.clone(), ty.clone()));
            }
            hol_kernel::TermView::App(f, x) => {
                walk(f, out);
                walk(x, out);
            }
            hol_kernel::TermView::Lam(_, _, body) => walk(body, out),
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(t, &mut out);
    out
}

/// A falsifying assignment of small numbers, described as `n = 2, m = 0`.
pub fn arithmetic_countermodel(env: &Env, statement: &Term) -> Option<String> {
    if env.sort("Nat").is_none() || has_binders(statement) {
        return None;
    }
    let vars = free_vars_in_order(statement);
    if vars.is_empty() || vars.len() > MAX_VARS || vars.iter().any(|(_, ty)| ty != &nat()) {
        return None;
    }
    let mut subst = Subst::new();
    let mut rules = Rules::definitional(env, &mut subst);
    rules.with_decision_rules(&mut subst);
    let count = vars.len() as u32;
    let total = (MAX_VALUE + 1).pow(count);
    for index in 0..total {
        let mut values = Vec::new();
        let mut rest = index;
        for _ in 0..count {
            values.push(rest % (MAX_VALUE + 1));
            rest /= MAX_VALUE + 1;
        }
        let bindings: Vec<(Term, Term)> = vars
            .iter()
            .zip(&values)
            .map(|((name, ty), value)| {
                Some((Term::free(name.clone(), ty.clone()), numeral(env, *value)?))
            })
            .collect::<Option<_>>()?;
        let instance = statement.subst_free(&bindings).ok()?;
        let result = normal_form(&subst, &rules, &instance);
        if result.is_true() {
            continue;
        }
        if result.is_false() {
            let description = vars
                .iter()
                .zip(&values)
                .map(|((name, _), value)| format!("{name} = {value}"))
                .collect::<Vec<_>>()
                .join(", ");
            return Some(description);
        }
        // The rules cannot decide this instance; say nothing rather than
        // something wrong.
        return None;
    }
    None
}
