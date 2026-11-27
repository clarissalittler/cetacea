//! Derived rules. Nothing here is trusted: every function is built from
//! the primitives in [`crate::rules`], so a bug here can only fail to
//! prove something, never prove something false.

use std::collections::BTreeSet;

use crate::error::{bail, Result};
use crate::rules;
use crate::term::{Term, TermView};
use crate::thm::Thm;

/// `|- t = t'` where `t'` is the beta normal form of `t`.
pub fn beta_norm_conv(t: &Term) -> Result<Thm> {
    t.require_closed("beta_norm")?;
    conv(t)
}

fn conv(t: &Term) -> Result<Thm> {
    // Nothing to reduce: `|- t = t` without walking the term.
    if t.is_beta_normal() {
        return rules::refl(t);
    }
    match t.view() {
        TermView::App(f, x) => {
            let step = rules::mk_comb(&conv(f)?, &conv(x)?)?;
            let rhs = rhs_of(&step);
            if rhs.beta_head().is_none() {
                return Ok(step);
            }
            let reduced = rules::trans(&step, &rules::beta(&rhs)?)?;
            let rest = conv(&rhs_of(&reduced))?;
            rules::trans(&reduced, &rest)
        }
        TermView::Lam(..) => {
            let (x, body) = t.open_fresh(&BTreeSet::new()).expect("lambda");
            rules::abs(&x, &conv(&body)?)
        }
        _ => rules::refl(t),
    }
}

fn rhs_of(th: &Thm) -> Term {
    th.concl().dest_eq().expect("equation").1.clone()
}

/// Beta-normalizes the conclusion of a theorem.
pub fn beta_norm(th: &Thm) -> Result<Thm> {
    let conv = beta_norm_conv(th.concl())?;
    rules::eq_mp(&conv, th)
}

/// From `|- a = b`, a template `λx. P x`, and `|- P a`, derives `|- P b`.
pub fn subst(eq: &Thm, template: &Term, th: &Thm) -> Result<Thm> {
    if !template.is_lam() {
        bail!("subst", "template `{template}` is not a lambda");
    }
    let (a, b) = eq
        .concl()
        .dest_eq()
        .map(|(a, b)| (a.clone(), b.clone()))
        .ok_or_else(|| crate::error::KernelError::new("subst", "expected an equation"))?;
    let template_a = Term::app(template, &a)?;
    let template_b = Term::app(template, &b)?;
    // template a = template b
    let congruence = rules::mk_comb(&rules::refl(template)?, eq)?;
    // P a = template a
    let left = rules::sym(&rules::beta(&template_a)?)?;
    // template b = P b
    let right = rules::beta(&template_b)?;
    let chain = rules::trans(&rules::trans(&left, &congruence)?, &right)?;
    rules::eq_mp(&chain, th)
}

/// Function extensionality as a derived rule: from `|- f x = g x` with
/// `x` not free in `f`, `g`, or the hypotheses, derives `|- f = g`.
pub fn funext(x: &Term, th: &Thm) -> Result<Thm> {
    let Some((fx, gx)) = th.concl().dest_eq() else {
        bail!("funext", "expected an equation, found `{}`", th.concl());
    };
    let (f, g) = match (fx.as_app(), gx.as_app()) {
        (Some((f, x1)), Some((g, x2))) if x1 == x && x2 == x => (f.clone(), g.clone()),
        _ => bail!("funext", "expected `f {x} = g {x}`, found `{}`", th.concl()),
    };
    if f.contains_var(x) || g.contains_var(x) {
        bail!("funext", "`{x}` occurs in `{f}` or `{g}`");
    }
    let abstracted = rules::abs(x, th)?;
    let (lam_f, lam_g) = abstracted
        .concl()
        .dest_eq()
        .map(|(a, b)| (a.clone(), b.clone()))
        .expect("equation");
    let left = rules::sym(&rules::eta(&lam_f)?)?;
    let right = rules::eta(&lam_g)?;
    rules::trans(&rules::trans(&left, &abstracted)?, &right)
}

/// From `|- P <-> Q`, `|- P -> Q`.
pub fn iff_left(th: &Thm) -> Result<Thm> {
    let Some((p, _)) = th.concl().dest_iff() else {
        bail!(
            "iff_left",
            "expected a biconditional, found `{}`",
            th.concl()
        );
    };
    let p = p.clone();
    let q = rules::eq_mp(th, &rules::assume(&p)?)?;
    rules::imp_intro(&p, &q)
}

/// From `|- P <-> Q`, `|- Q -> P`.
pub fn iff_right(th: &Thm) -> Result<Thm> {
    let Some((_, q)) = th.concl().dest_iff() else {
        bail!(
            "iff_right",
            "expected a biconditional, found `{}`",
            th.concl()
        );
    };
    let q = q.clone();
    let p = rules::eq_mp(&rules::sym(th)?, &rules::assume(&q)?)?;
    rules::imp_intro(&q, &p)
}

/// Instantiates leading universal quantifiers with the given terms.
pub fn spec(th: &Thm, args: &[Term]) -> Result<Thm> {
    let mut current = th.clone();
    for arg in args {
        current = rules::forall_elim(&current, arg)?;
    }
    Ok(current)
}

/// Discharges the given hypotheses in order, producing nested
/// implications.
pub fn discharge(premises: &[Term], th: &Thm) -> Result<Thm> {
    let mut current = th.clone();
    for premise in premises.iter().rev() {
        current = rules::imp_intro(premise, &current)?;
    }
    Ok(current)
}

/// Generalizes over the given variables in order.
pub fn generalize(vars: &[Term], th: &Thm) -> Result<Thm> {
    let mut current = th.clone();
    for var in vars.iter().rev() {
        current = rules::forall_intro(var, &current)?;
    }
    Ok(current)
}
