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

/// Small values of a datatype, built from its constructors up to a
/// depth. Type parameters are instantiated at the given types.
fn small_values(env: &Env, ty: &Type, depth: u32) -> Vec<Term> {
    let Type::Con(name, args) = ty else {
        return Vec::new();
    };
    if depth == 0 {
        return Vec::new();
    }
    let Some(info) = env.theory().datatype(name.as_str()).cloned() else {
        return Vec::new();
    };
    let subst: hol_kernel::TypeSubst = info
        .params
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    let mut out = Vec::new();
    for ctor in &info.ctors {
        let arg_types: Vec<Type> = ctor.args.iter().map(|t| t.subst(&subst)).collect();
        let Ok(head) = env
            .theory()
            .constant(ctor.name.clone(), Type::funs(&arg_types, ty.clone()))
        else {
            continue;
        };
        let mut combos: Vec<Vec<Term>> = vec![Vec::new()];
        for arg_ty in &arg_types {
            let values = small_values(env, arg_ty, depth - 1);
            let mut next = Vec::new();
            for combo in &combos {
                for value in &values {
                    let mut extended = combo.clone();
                    extended.push(value.clone());
                    next.push(extended);
                }
            }
            combos = next;
            if combos.len() > 64 {
                combos.truncate(64);
            }
        }
        for combo in combos {
            if let Ok(term) = Term::apps(&head, &combo) {
                out.push(term);
            }
        }
    }
    out
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
    if vars.is_empty() || vars.len() > MAX_VARS {
        return None;
    }
    // Candidate values per variable: numerals for Nat, small constructor
    // trees for other datatypes.
    let mut domains: Vec<Vec<Term>> = Vec::new();
    for (_, ty) in &vars {
        let values = if ty == &nat() {
            (0..=MAX_VALUE).filter_map(|n| numeral(env, n)).collect()
        } else {
            small_values(env, ty, 3)
        };
        if values.is_empty() {
            return None;
        }
        domains.push(values);
    }
    let mut subst = Subst::new();
    let mut rules = Rules::definitional(env, &mut subst);
    rules.with_decision_rules(&mut subst);
    let total: usize = domains.iter().map(|d| d.len()).product();
    if total > 2000 {
        return None;
    }
    for index in 0..total {
        let mut choice = Vec::new();
        let mut rest = index;
        for domain in &domains {
            choice.push(&domain[rest % domain.len()]);
            rest /= domain.len();
        }
        let bindings: Vec<(Term, Term)> = vars
            .iter()
            .zip(&choice)
            .map(|((name, ty), value)| (Term::free(name.clone(), ty.clone()), (*value).clone()))
            .collect();
        let instance = statement.subst_free(&bindings).ok()?;
        let result = normal_form(&subst, &rules, &instance);
        if result.is_true() {
            continue;
        }
        if result.is_false() {
            let description = vars
                .iter()
                .zip(&choice)
                .map(|((name, _), value)| format!("{name} = {}", hol_elab::print_term(env, value)))
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
