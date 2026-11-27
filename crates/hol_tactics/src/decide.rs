//! `decide`: settling a statement by evaluating it.
//!
//! A statement with no unknowns, built from computable definitions,
//! data constructors, the connectives, and quantifiers over types with
//! finitely many values, has a truth value that computation finds.
//! `decide` normalizes the goal with the computation rules, the
//! `True`/`False` simplifications, and the rules that expand a
//! quantifier over an enumeration type into its instances. Every step
//! is a kernel rewrite, so a goal is closed only by a real proof; when
//! the goal is false or cannot be evaluated, the functions here work
//! out what to tell the student.

use hol_elab::Env;
use hol_kernel::{Term, TermView, Type};

use crate::conv::{head_unfold, normal_form, rewrite_root, rhs, Rules};
use crate::simp_rules::{enumeration_values, is_enumeration};
use crate::unify::{is_meta_name, Subst};

/// The rules `decide` evaluates with.
pub fn decision_rules(env: &Env, subst: &mut Subst) -> Rules {
    let mut rules = Rules::definitional(env, subst);
    rules.with_decision_rules(subst);
    rules.with_enumeration_rules(env, subst);
    rules
}

/// The values of `ty` when it is an enumeration type.
fn values_of(env: &Env, ty: &Type) -> Option<Vec<Term>> {
    let Type::Con(name, args) = ty else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    let info = env.theory().datatype(name.as_str())?;
    if !is_enumeration(info) {
        return None;
    }
    enumeration_values(info).ok()
}

/// The smallest part of a false statement that is itself false, with
/// the values chosen for quantified variables on the way to it.
pub struct FalsePart {
    pub part: Term,
    pub choices: Vec<(String, Term)>,
}

/// Narrows a statement that evaluates to `False` down to a false part
/// worth showing: the failing side of a conjunction, the failing
/// instance of a universal statement, the body of a definition.
pub fn locate_false(env: &Env, subst: &Subst, rules: &Rules, statement: &Term) -> FalsePart {
    let is_false = |t: &Term| normal_form(subst, rules, t).is_false();
    let is_true = |t: &Term| normal_form(subst, rules, t).is_true();
    let mut part = statement.clone();
    let mut choices = Vec::new();
    // Unfolding a definition is worth showing only if it exposes
    // structure to narrow further; otherwise the folded form the student
    // wrote is the clearer one, and this remembers it.
    let mut folded: Option<Term> = None;
    for _ in 0..40 {
        if let Some((a, b)) = part.dest_and() {
            if is_false(a) {
                part = a.clone();
                folded = None;
                continue;
            }
            if is_false(b) {
                part = b.clone();
                folded = None;
                continue;
            }
            break;
        }
        if part.dest_not().is_none() {
            if let Some((a, b)) = part.dest_imp() {
                if is_true(a) && is_false(b) {
                    part = b.clone();
                    folded = None;
                    continue;
                }
                break;
            }
        }
        if let Some(pred) = part.dest_forall() {
            let TermView::Lam(binder, ty, _) = pred.view() else {
                break;
            };
            let Some(values) = values_of(env, ty) else {
                break;
            };
            let failing = values.into_iter().find_map(|value| {
                let instance = pred.beta_apply(&value).ok()?;
                is_false(&instance).then_some((value, instance))
            });
            let Some((value, instance)) = failing else {
                break;
            };
            choices.push((binder.to_string(), value));
            part = instance;
            folded = None;
            continue;
        }
        // A defined name: look inside its definition, unless doing so
        // already gives the bare answer.
        let unfolded = match head_unfold(subst, rules, &part) {
            Ok(conv) if rhs(&conv) != part => Some(rhs(&conv)),
            _ => rewrite_root(subst, rules, &part)
                .and_then(|step| hol_kernel::beta_norm_conv(&rhs(&step)).ok())
                .map(|conv| rhs(&conv)),
        };
        match unfolded {
            Some(next) if !next.is_false() && !next.is_true() && next != part => {
                folded.get_or_insert_with(|| part.clone());
                part = next;
            }
            _ => break,
        }
    }
    FalsePart {
        part: folded.unwrap_or(part),
        choices,
    }
}

/// Why evaluation stopped short of `True` or `False`, in the student's
/// terms. Empty when no specific reason is found.
pub fn stuck_reasons(env: &Env, residue: &Term) -> Vec<String> {
    let mut reasons = Vec::new();
    let mut types: Vec<String> = Vec::new();
    fn walk(env: &Env, t: &Term, types: &mut Vec<String>) {
        match t.view() {
            TermView::App(f, x) => {
                let quantifier = t.dest_forall().or_else(|| t.dest_exists());
                if let Some(pred) = quantifier {
                    if let TermView::Lam(_, ty, _) = pred.view() {
                        let shown = ty.to_string();
                        if values_of(env, ty).is_none() && !types.contains(&shown) {
                            types.push(shown);
                        }
                    }
                }
                walk(env, f, types);
                walk(env, x, types);
            }
            TermView::Lam(_, _, body) => walk(env, body, types),
            _ => {}
        }
    }
    walk(env, residue, &mut types);
    for ty in types {
        reasons.push(format!(
            "it quantifies over `{ty}`, and `decide` can only run through a type whose values are a fixed list of constants"
        ));
    }
    let unknowns: Vec<String> = residue
        .free_vars()
        .into_iter()
        .map(|(name, _)| name)
        .filter(|name| !is_meta_name(name))
        .map(|name| format!("`{name}`"))
        .collect();
    if !unknowns.is_empty() {
        reasons.push(format!(
            "it depends on {}, and `decide` evaluates only statements with no unknowns; `cases` on a variable of a data type gives one known value per case",
            unknowns.join(" and ")
        ));
    }
    reasons
}
