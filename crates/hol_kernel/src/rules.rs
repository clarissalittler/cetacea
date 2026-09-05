//! Primitive inference rules.
//!
//! Every function here returns a [`Thm`] and is one line of the trusted
//! rule table. Equality rules follow HOL; the connectives and quantifiers
//! have natural deduction introduction and elimination rules, so the
//! rule table students learn is literally the kernel.
//!
//! Term equality in side conditions is alpha-equivalence and nothing
//! more. Beta and eta conversion are explicit rules; the tactic layer
//! normalizes before matching.

use crate::error::{bail, Result};
use crate::term::{Term, TermView};
use crate::thm::{Tags, Thm};
use crate::types::TypeSubst;

/// `P |- P`.
pub fn assume(p: &Term) -> Result<Thm> {
    require_prop("assume", p)?;
    Ok(Thm::new(vec![p.clone()], p.clone(), Tags::none()))
}

/// Adds a hypothesis: from `Γ |- Q` to `Γ, P |- Q`.
pub fn add_hyp(th: &Thm, p: &Term) -> Result<Thm> {
    require_prop("add_hyp", p)?;
    Ok(Thm::new(
        Thm::merged_hyps(&[th.hyps(), std::slice::from_ref(p)]),
        th.concl().clone(),
        th.tags().clone(),
    ))
}

/// `|- t = t`.
pub fn refl(t: &Term) -> Result<Thm> {
    t.require_closed("refl")?;
    Ok(Thm::new(vec![], Term::eq(t, t)?, Tags::none()))
}

/// From `|- a = b`, `|- b = a`.
pub fn sym(th: &Thm) -> Result<Thm> {
    let (a, b) = dest_eq("sym", th)?;
    Ok(Thm::new(
        th.hyps().to_vec(),
        Term::eq(b, a)?,
        th.tags().clone(),
    ))
}

/// From `|- a = b` and `|- b = c`, `|- a = c`.
pub fn trans(ab: &Thm, bc: &Thm) -> Result<Thm> {
    let (a, b1) = dest_eq("trans", ab)?;
    let (b2, c) = dest_eq("trans", bc)?;
    if b1 != b2 {
        bail!(
            "trans",
            "middle terms differ: `{b1}` in the first equation, `{b2}` in the second"
        );
    }
    Ok(Thm::new(
        Thm::merged_hyps(&[ab.hyps(), bc.hyps()]),
        Term::eq(a, c)?,
        ab.tags().union(bc.tags()),
    ))
}

/// From `|- f = g` and `|- x = y`, `|- f x = g y`.
pub fn mk_comb(fg: &Thm, xy: &Thm) -> Result<Thm> {
    let (f, g) = dest_eq("mk_comb", fg)?;
    let (x, y) = dest_eq("mk_comb", xy)?;
    let fx = Term::app(f, x)?;
    let gy = Term::app(g, y)?;
    Ok(Thm::new(
        Thm::merged_hyps(&[fg.hyps(), xy.hyps()]),
        Term::eq(&fx, &gy)?,
        fg.tags().union(xy.tags()),
    ))
}

/// From `|- a = b`, `|- (λx. a) = (λx. b)`, provided `x` is not free in
/// the hypotheses.
pub fn abs(x: &Term, th: &Thm) -> Result<Thm> {
    let (a, b) = dest_eq("abs", th)?;
    if x.as_free().is_none() {
        bail!("abs", "`{x}` is not a free variable");
    }
    if th.var_in_hyps(x) {
        bail!(
            "abs",
            "cannot abstract over `{x}`: it occurs free in a hypothesis"
        );
    }
    Ok(Thm::new(
        th.hyps().to_vec(),
        Term::eq(&Term::lam(x, a)?, &Term::lam(x, b)?)?,
        th.tags().clone(),
    ))
}

/// For `t = (λx. b) a`, `|- (λx. b) a = b[a/x]`.
pub fn beta(t: &Term) -> Result<Thm> {
    t.require_closed("beta")?;
    let Some(reduced) = t.beta_head() else {
        bail!("beta", "`{t}` is not a beta redex");
    };
    Ok(Thm::new(vec![], Term::eq(t, &reduced)?, Tags::none()))
}

/// For `t = λx. f x` with `x` not free in `f`, `|- (λx. f x) = f`.
pub fn eta(t: &Term) -> Result<Thm> {
    t.require_closed("eta")?;
    let TermView::Lam(_, _, body) = t.view() else {
        bail!("eta", "`{t}` is not a lambda abstraction");
    };
    let Some((f, x)) = body.as_app() else {
        bail!("eta", "`{t}` is not of the form `fun x => f x`");
    };
    let is_binder = matches!(x.view(), TermView::Bound(0, _));
    if !is_binder || !f.is_closed() {
        bail!(
            "eta",
            "`{t}` is not of the form `fun x => f x` with `x` not free in `f`"
        );
    }
    Ok(Thm::new(vec![], Term::eq(t, f)?, Tags::none()))
}

/// From `|- P = Q` and `|- P`, `|- Q`.
pub fn eq_mp(pq: &Thm, p: &Thm) -> Result<Thm> {
    let (lhs, rhs) = dest_eq("eq_mp", pq)?;
    if lhs != p.concl() {
        bail!(
            "eq_mp",
            "the equation's left side `{lhs}` does not match the theorem `{}`",
            p.concl()
        );
    }
    Ok(Thm::new(
        Thm::merged_hyps(&[pq.hyps(), p.hyps()]),
        rhs.clone(),
        pq.tags().union(p.tags()),
    ))
}

/// `|- True`.
pub fn true_intro() -> Thm {
    Thm::new(vec![], Term::true_(), Tags::none())
}

/// From `|- False`, `|- P`.
pub fn false_elim(th: &Thm, p: &Term) -> Result<Thm> {
    require_prop("false_elim", p)?;
    if !th.concl().is_false() {
        bail!(
            "false_elim",
            "expected a proof of `False`, found `{}`",
            th.concl()
        );
    }
    Ok(Thm::new(th.hyps().to_vec(), p.clone(), th.tags().clone()))
}

/// From `|- P` and `|- Q`, `|- P /\ Q`.
pub fn and_intro(p: &Thm, q: &Thm) -> Result<Thm> {
    Ok(Thm::new(
        Thm::merged_hyps(&[p.hyps(), q.hyps()]),
        Term::and(p.concl(), q.concl())?,
        p.tags().union(q.tags()),
    ))
}

/// From `|- P /\ Q`, `|- P`.
pub fn and_left(th: &Thm) -> Result<Thm> {
    let Some((p, _)) = th.concl().dest_and() else {
        bail!("and_left", "expected a conjunction, found `{}`", th.concl());
    };
    Ok(Thm::new(th.hyps().to_vec(), p.clone(), th.tags().clone()))
}

/// From `|- P /\ Q`, `|- Q`.
pub fn and_right(th: &Thm) -> Result<Thm> {
    let Some((_, q)) = th.concl().dest_and() else {
        bail!(
            "and_right",
            "expected a conjunction, found `{}`",
            th.concl()
        );
    };
    Ok(Thm::new(th.hyps().to_vec(), q.clone(), th.tags().clone()))
}

/// From `|- P`, `|- P \/ Q`.
pub fn or_left(th: &Thm, q: &Term) -> Result<Thm> {
    Ok(Thm::new(
        th.hyps().to_vec(),
        Term::or(th.concl(), q)?,
        th.tags().clone(),
    ))
}

/// From `|- Q`, `|- P \/ Q`.
pub fn or_right(p: &Term, th: &Thm) -> Result<Thm> {
    Ok(Thm::new(
        th.hyps().to_vec(),
        Term::or(p, th.concl())?,
        th.tags().clone(),
    ))
}

/// From `|- P \/ Q`, `P |- R`, and `Q |- R`, `|- R`. The hypotheses `P`
/// and `Q` are discharged from their respective branches.
pub fn or_elim(disj: &Thm, left: &Thm, right: &Thm) -> Result<Thm> {
    let Some((p, q)) = disj.concl().dest_or() else {
        bail!(
            "or_elim",
            "expected a disjunction, found `{}`",
            disj.concl()
        );
    };
    if left.concl() != right.concl() {
        bail!(
            "or_elim",
            "the branches prove different things: `{}` and `{}`",
            left.concl(),
            right.concl()
        );
    }
    let left_hyps = left.hyps_without(p);
    let right_hyps = right.hyps_without(q);
    Ok(Thm::new(
        Thm::merged_hyps(&[disj.hyps(), &left_hyps, &right_hyps]),
        left.concl().clone(),
        disj.tags().union(left.tags()).union(right.tags()),
    ))
}

/// From `Γ |- Q`, `Γ - {P} |- P -> Q`.
pub fn imp_intro(p: &Term, th: &Thm) -> Result<Thm> {
    require_prop("imp_intro", p)?;
    Ok(Thm::new(
        th.hyps_without(p),
        Term::imp(p, th.concl())?,
        th.tags().clone(),
    ))
}

/// From `|- P -> Q` and `|- P`, `|- Q`.
pub fn imp_elim(imp: &Thm, p: &Thm) -> Result<Thm> {
    let Some((ante, conseq)) = imp.concl().dest_imp() else {
        bail!(
            "imp_elim",
            "expected an implication, found `{}`",
            imp.concl()
        );
    };
    if ante != p.concl() {
        bail!(
            "imp_elim",
            "the implication expects `{ante}`, but the theorem proves `{}`",
            p.concl()
        );
    }
    Ok(Thm::new(
        Thm::merged_hyps(&[imp.hyps(), p.hyps()]),
        conseq.clone(),
        imp.tags().union(p.tags()),
    ))
}

/// From `|- P -> Q` and `|- Q -> P`, `|- P <-> Q`, which is `P = Q` at
/// type `Prop`. This is propositional extensionality.
pub fn iff_intro(pq: &Thm, qp: &Thm) -> Result<Thm> {
    let Some((p1, q1)) = pq.concl().dest_imp() else {
        bail!(
            "iff_intro",
            "expected an implication, found `{}`",
            pq.concl()
        );
    };
    let Some((q2, p2)) = qp.concl().dest_imp() else {
        bail!(
            "iff_intro",
            "expected an implication, found `{}`",
            qp.concl()
        );
    };
    if p1 != p2 || q1 != q2 {
        bail!(
            "iff_intro",
            "the implications `{}` and `{}` are not converses",
            pq.concl(),
            qp.concl()
        );
    }
    Ok(Thm::new(
        Thm::merged_hyps(&[pq.hyps(), qp.hyps()]),
        Term::iff(p1, q1)?,
        pq.tags().union(qp.tags()),
    ))
}

/// From `|- P`, `|- forall x. P`, provided `x` is not free in the
/// hypotheses.
pub fn forall_intro(x: &Term, th: &Thm) -> Result<Thm> {
    if x.as_free().is_none() {
        bail!("forall_intro", "`{x}` is not a free variable");
    }
    if th.var_in_hyps(x) {
        bail!(
            "forall_intro",
            "cannot generalize `{x}`: it occurs free in a hypothesis"
        );
    }
    Ok(Thm::new(
        th.hyps().to_vec(),
        Term::forall(x, th.concl())?,
        th.tags().clone(),
    ))
}

/// From `|- forall x. P`, `|- P[t/x]`.
pub fn forall_elim(th: &Thm, t: &Term) -> Result<Thm> {
    let Some(pred) = th.concl().dest_forall() else {
        bail!(
            "forall_elim",
            "expected a universal statement, found `{}`",
            th.concl()
        );
    };
    let instance = pred
        .beta_apply(t)
        .map_err(|err| crate::error::KernelError::new("forall_elim", err.message))?;
    Ok(Thm::new(th.hyps().to_vec(), instance, th.tags().clone()))
}

/// From `|- P[t/x]`, `|- exists x. P`. The existential statement is
/// given explicitly because it is not determined by the instance.
pub fn exists_intro(ex: &Term, witness: &Term, th: &Thm) -> Result<Thm> {
    ex.require_closed("exists_intro")?;
    let Some(pred) = ex.dest_exists() else {
        bail!(
            "exists_intro",
            "expected an existential statement, found `{ex}`"
        );
    };
    let instance = pred
        .beta_apply(witness)
        .map_err(|err| crate::error::KernelError::new("exists_intro", err.message))?;
    if &instance != th.concl() {
        bail!(
            "exists_intro",
            "witness `{witness}` requires a proof of `{instance}`, but the theorem proves `{}`",
            th.concl()
        );
    }
    Ok(Thm::new(th.hyps().to_vec(), ex.clone(), th.tags().clone()))
}

/// From `|- exists x. P` and `P[x] |- Q`, `|- Q`, provided the
/// eigenvariable `x` is free neither in `Q`, nor in the other
/// hypotheses of the second theorem, nor in the first theorem.
pub fn exists_elim(ex: &Thm, x: &Term, th: &Thm) -> Result<Thm> {
    let Some(pred) = ex.concl().dest_exists() else {
        bail!(
            "exists_elim",
            "expected an existential statement, found `{}`",
            ex.concl()
        );
    };
    if x.as_free().is_none() {
        bail!("exists_elim", "`{x}` is not a free variable");
    }
    let instance = pred
        .beta_apply(x)
        .map_err(|err| crate::error::KernelError::new("exists_elim", err.message))?;
    if th.concl().contains_var(x) {
        bail!(
            "exists_elim",
            "the eigenvariable `{x}` occurs in the conclusion `{}`",
            th.concl()
        );
    }
    let remaining = th.hyps_without(&instance);
    if remaining.iter().any(|hyp| hyp.contains_var(x)) {
        bail!(
            "exists_elim",
            "the eigenvariable `{x}` occurs in a hypothesis other than `{instance}`"
        );
    }
    if ex.concl().contains_var(x) || ex.var_in_hyps(x) {
        bail!(
            "exists_elim",
            "the eigenvariable `{x}` occurs in the existential theorem"
        );
    }
    Ok(Thm::new(
        Thm::merged_hyps(&[ex.hyps(), &remaining]),
        th.concl().clone(),
        ex.tags().union(th.tags()),
    ))
}

/// Instantiates type variables in the hypotheses and conclusion.
pub fn inst_type(th: &Thm, subst: &TypeSubst) -> Thm {
    Thm::new(
        th.hyps().iter().map(|hyp| hyp.subst_type(subst)).collect(),
        th.concl().subst_type(subst),
        th.tags().clone(),
    )
}

/// Simultaneously substitutes terms for free variables in the
/// hypotheses and conclusion.
pub fn inst(th: &Thm, subst: &[(Term, Term)]) -> Result<Thm> {
    let concl = th.concl().subst_free(subst)?;
    let hyps = th
        .hyps()
        .iter()
        .map(|hyp| hyp.subst_free(subst))
        .collect::<Result<Vec<_>>>()?;
    Ok(Thm::new(hyps, concl, th.tags().clone()))
}

/// `|- P \/ not P`, tagged classical.
pub fn excluded_middle(p: &Term) -> Result<Thm> {
    require_prop("excluded_middle", p)?;
    Ok(Thm::new(
        vec![],
        Term::or(p, &Term::not(p)?)?,
        Tags::classical(),
    ))
}

/// `|- P`, tagged sorry. Closes any goal and taints everything that
/// depends on it.
pub fn sorry(p: &Term) -> Result<Thm> {
    require_prop("sorry", p)?;
    Ok(Thm::new(vec![], p.clone(), Tags::sorry()))
}

fn require_prop(rule: &'static str, t: &Term) -> Result<()> {
    t.require_closed(rule)?;
    if !t.ty().is_prop() {
        bail!(
            rule,
            "`{t}` has type `{}`, but a proposition was expected",
            t.ty()
        );
    }
    Ok(())
}

fn dest_eq<'a>(rule: &'static str, th: &'a Thm) -> Result<(&'a Term, &'a Term)> {
    match th.concl().dest_eq() {
        Some(pair) => Ok(pair),
        None => bail!(rule, "expected an equation, found `{}`", th.concl()),
    }
}
