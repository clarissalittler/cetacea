//! Conversions: kernel-checked rewriting, definition unfolding, and
//! normalization.
//!
//! A conversion turns a term `t` into a theorem `|- t = t'`. Rewriting
//! with an equation `∀xs. l = r` matches `l` against a subterm (one-way,
//! binding only the equation's metavariables), instantiates the
//! equation, and stitches the result into the surrounding term with
//! `mk_comb` and `abs`. Every step is a kernel rule, so the simplifier
//! cannot be wrong, only slow.

use std::collections::BTreeSet;

use hol_elab::Env;
use hol_kernel::{
    abs, beta_norm_conv, forall_elim, inst_type, mk_comb, refl, sym, trans, Name, Term, TermView,
    Thm, TypeSubst,
};

use crate::unify::{is_meta_name, Subst};

#[derive(Clone, Debug)]
pub struct Rule {
    pub name: String,
    pub lhs: Term,
    /// `|- lhs = rhs`, possibly with hypotheses (for local equations) and
    /// metavariables (for quantified or schematic equations).
    pub thm: Thm,
}

impl Rule {
    /// Strips leading universal quantifiers with fresh metavariables. The
    /// theorem's type variables are made schematic too when `generic` is
    /// set (definitions and library lemmas), and left rigid otherwise
    /// (local hypotheses).
    pub fn from_thm(subst: &mut Subst, thm: &Thm, name: &str, generic: bool) -> Option<Rule> {
        let mut thm = thm.clone();
        if generic {
            let mut vars = BTreeSet::new();
            thm.concl().type_vars(&mut vars);
            let map: TypeSubst = vars
                .into_iter()
                .filter(|v| !hol_elab::is_meta(v))
                .map(|v| (v, subst.fresh_type_meta()))
                .collect();
            thm = inst_type(&thm, &map);
        }
        while let Some(pred) = thm.concl().dest_forall() {
            let TermView::Lam(binder, ty, _) = pred.view() else {
                break;
            };
            let meta = subst.fresh_meta(binder.as_str(), ty.clone());
            thm = forall_elim(&thm, &meta).ok()?;
        }
        let (lhs, _) = thm.concl().dest_eq()?;
        Some(Rule {
            name: name.to_string(),
            lhs: lhs.clone(),
            thm,
        })
    }
}

#[derive(Clone, Debug, Default)]
pub struct Rules {
    pub rules: Vec<Rule>,
    /// Applied only to the result of a constructor-injectivity rewrite:
    /// `x = x` becomes `True` and `True /\ P` becomes `P`, so that
    /// `succ(a) = succ(b)` simplifies to `a = b` while ordinary goals keep
    /// their trivial equalities.
    pub tidy: Vec<Rule>,
}

impl Rules {
    /// Every definition, recursive-function equation, and the set
    /// comprehension principle: the rules that define computation.
    pub fn definitional(env: &Env, subst: &mut Subst) -> Rules {
        let mut rules = Vec::new();
        for def in env.defs() {
            if !env.is_transparent(&def.name) {
                continue;
            }
            if let Some(rule) = Rule::from_thm(subst, &def.equation, def.name.as_str(), true) {
                rules.push(rule);
            }
        }
        // Registered lemmas: schematize their parameters first.
        for info in env.simp_lemmas() {
            let Ok((thm, _, _)) = crate::unify::schematize(
                subst,
                &info.thm,
                &info.type_params(),
                &info.term_params(),
            ) else {
                continue;
            };
            if let Some(rule) = Rule::from_thm(subst, &thm, info.name.as_str(), true) {
                rules.push(rule);
            }
        }
        for (name, thm) in crate::simp_rules::datatype_rules(env) {
            if let Some(rule) = Rule::from_thm(subst, &thm, &name, true) {
                rules.push(rule);
            }
        }
        for thm in env.all_equations() {
            if let Some(rule) = Rule::from_thm(subst, thm, "equation", true) {
                rules.push(rule);
            }
        }
        if let Some(thm) = env.theory().theorem(hol_kernel::MEM_SET_OF) {
            if let Some(rule) = Rule::from_thm(subst, thm, "membership", true) {
                rules.push(rule);
            }
        }
        let mut tidy = Vec::new();
        if let Ok(thm) = crate::simp_rules::reflexivity_rule() {
            if let Some(rule) = Rule::from_thm(subst, &thm, "eq_self", true) {
                tidy.push(rule);
            }
        }
        if let Ok(props) = crate::simp_rules::propositional_rules() {
            for (name, thm) in props {
                if name == "and_true_left" || name == "and_true_right" {
                    if let Some(rule) = Rule::from_thm(subst, &thm, &name, true) {
                        tidy.push(rule);
                    }
                }
            }
        }
        Rules { rules, tidy }
    }

    /// Only the equation of one definition.
    pub fn for_def(env: &Env, subst: &mut Subst, name: &Name) -> Rules {
        let mut rules = Vec::new();
        if let Some(def) = env.def_by_exact_name(name) {
            if let Some(rule) = Rule::from_thm(subst, &def.equation, def.name.as_str(), true) {
                rules.push(rule);
            }
        }
        if let Some(thms) = env.equations(name) {
            for thm in thms {
                if let Some(rule) = Rule::from_thm(subst, thm, name.as_str(), true) {
                    rules.push(rule);
                }
            }
        }
        Rules {
            rules,
            tidy: Vec::new(),
        }
    }

    /// Adds `x = x <-> True` and the `True`/`False` propositional
    /// simplifications, used for deciding closed statements. They are
    /// kept out of the default `simp` set so that `simp` leaves the
    /// logical structure of a goal alone.
    pub fn with_decision_rules(&mut self, subst: &mut Subst) {
        if let Ok(thm) = crate::simp_rules::reflexivity_rule() {
            if let Some(rule) = Rule::from_thm(subst, &thm, "eq_self", true) {
                self.rules.push(rule);
            }
        }
        if let Ok(props) = crate::simp_rules::propositional_rules() {
            for (name, thm) in props {
                if let Some(rule) = Rule::from_thm(subst, &thm, &name, true) {
                    self.rules.push(rule);
                }
            }
        }
    }

    /// The same rules with the structural recursion equations first, so
    /// that a step-by-step search sees the unfolded shapes the old checker
    /// produced.
    pub fn equations_first(&self) -> Rules {
        let (eqs, rest): (Vec<Rule>, Vec<Rule>) = self
            .rules
            .iter()
            .cloned()
            .partition(|r| r.name == "equation");
        Rules {
            rules: eqs.into_iter().chain(rest).collect(),
            tidy: self.tidy.clone(),
        }
    }

    pub fn push(&mut self, rule: Rule) {
        self.rules.push(rule);
    }

    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    /// Definitional rules whose left side is exactly a constant.
    pub fn is_def_constant(&self, name: &Name) -> bool {
        self.rules.iter().any(|r| {
            matches!(r.lhs.as_const(), Some((n, _)) if n == name) && r.lhs.as_app().is_none()
        })
    }
}

/// Tries every rule at the root of `t`. Returns `|- t = t'`.
fn rewrite_root(subst: &Subst, rules: &Rules, t: &Term) -> Option<Thm> {
    let own_metas: BTreeSet<Name> = t
        .free_vars()
        .into_iter()
        .map(|(n, _)| n)
        .filter(is_meta_name)
        .collect();
    for rule in &rules.rules {
        let mut local = subst.clone();
        if !local.unify(&rule.lhs, t) {
            continue;
        }
        // One-way: the term's own metavariables must stay unsolved.
        if own_metas
            .iter()
            .any(|m| local.is_solved(m) && !subst.is_solved(m))
        {
            continue;
        }
        let Ok(thm) = local.apply_thm(&rule.thm) else {
            continue;
        };
        let Some((lhs, rhs)) = thm.concl().dest_eq() else {
            continue;
        };
        if lhs != t || rhs == t {
            continue;
        }
        if rule.name.ends_with(".inj") {
            if let Some(conv) = crate::simp_rules::tidy_injectivity(rhs) {
                if let Ok(chained) = trans(&thm, &conv) {
                    return Some(chained);
                }
            }
        }
        return Some(thm);
    }
    None
}

/// One bottom-up pass. Returns `None` when nothing changed.
fn rewrite_pass(subst: &Subst, rules: &Rules, t: &Term) -> hol_kernel::Result<Option<Thm>> {
    let inner = match t.view() {
        TermView::App(f, x) => {
            let cf = rewrite_pass(subst, rules, f)?;
            let cx = rewrite_pass(subst, rules, x)?;
            match (cf, cx) {
                (None, None) => None,
                (cf, cx) => {
                    let cf = match cf {
                        Some(c) => c,
                        None => refl(f)?,
                    };
                    let cx = match cx {
                        Some(c) => c,
                        None => refl(x)?,
                    };
                    Some(mk_comb(&cf, &cx)?)
                }
            }
        }
        TermView::Lam(..) => {
            let (var, body) = t.open_fresh(&BTreeSet::new()).expect("lambda");
            match rewrite_pass(subst, rules, &body)? {
                None => None,
                Some(cb) => Some(abs(&var, &cb)?),
            }
        }
        _ => None,
    };
    let current = match &inner {
        Some(c) => rhs(c),
        None => t.clone(),
    };
    match rewrite_root(subst, rules, &current) {
        Some(root) => Ok(Some(match inner {
            Some(c) => trans(&c, &root)?,
            None => root,
        })),
        None => Ok(inner),
    }
}

pub fn rhs(thm: &Thm) -> Term {
    thm.concl().dest_eq().expect("equation").1.clone()
}

/// Rewrites to a normal form: repeated bottom-up passes with beta
/// normalization between them. Returns `|- t = t'` and whether anything
/// changed.
pub fn normalize(subst: &Subst, rules: &Rules, t: &Term) -> hol_kernel::Result<(Thm, bool)> {
    let mut acc = beta_norm_conv(t)?;
    let mut changed = rhs(&acc) != *t;
    for _ in 0..200 {
        let current = rhs(&acc);
        let Some(step) = rewrite_pass(subst, rules, &current)? else {
            break;
        };
        let stepped = trans(&acc, &step)?;
        let beta = beta_norm_conv(&rhs(&stepped))?;
        acc = trans(&stepped, &beta)?;
        changed = true;
    }
    Ok((acc, changed))
}

/// Rewrites pass by pass and stops as soon as `stop` holds of the current
/// form, returning `|- t = t'` for that form. `None` when it never holds.
pub fn normalize_until(
    subst: &Subst,
    rules: &Rules,
    t: &Term,
    stop: impl Fn(&Term) -> bool,
) -> hol_kernel::Result<Option<Thm>> {
    let mut acc = beta_norm_conv(t)?;
    for _ in 0..200 {
        let current = rhs(&acc);
        if stop(&current) {
            return Ok(Some(acc));
        }
        let Some(step) = rewrite_pass(subst, rules, &current)? else {
            return Ok(None);
        };
        let stepped = trans(&acc, &step)?;
        let beta = beta_norm_conv(&rhs(&stepped))?;
        acc = trans(&stepped, &beta)?;
    }
    Ok(None)
}

/// The normal form of a term, without the theorem.
pub fn normal_form(subst: &Subst, rules: &Rules, t: &Term) -> Term {
    match normalize(subst, rules, t) {
        Ok((thm, _)) => rhs(&thm),
        Err(_) => t.clone(),
    }
}

/// Unfolds definitions at the head only, until the head is not a defined
/// constant: `Reflexive(R)` becomes `forall x, R(x, x)`, but arguments
/// are left alone. Returns `|- t = t'` (a reflexive equation when
/// nothing unfolds).
pub fn head_unfold(subst: &Subst, rules: &Rules, t: &Term) -> hol_kernel::Result<Thm> {
    let mut acc = refl(t)?;
    for _ in 0..50 {
        let current = rhs(&acc);
        let (head, args) = current.strip_app();
        let Some((name, _)) = head.as_const() else {
            break;
        };
        // `x in S`: unfold the set's head and apply comprehension.
        if name.as_str() == hol_kernel::MEM && args.len() == 2 {
            let set_conv = head_unfold(subst, rules, args[1])?;
            let unfolded_set = rhs(&set_conv);
            let mem_x = current.as_app().expect("application").0.clone();
            let whole = mk_comb(&refl(&mem_x)?, &set_conv)?;
            let candidate = rhs(&whole);
            let Some(root) = rewrite_root(subst, rules, &candidate) else {
                break;
            };
            if unfolded_set == *args[1] && rhs(&root) == candidate {
                break;
            }
            let beta = beta_norm_conv(&rhs(&root))?;
            let step = trans(&trans(&whole, &root)?, &beta)?;
            acc = trans(&acc, &step)?;
            continue;
        }
        if !rules.is_def_constant(name) {
            break;
        }
        let Some(head_eq) = rewrite_root(subst, rules, head) else {
            break;
        };
        let mut whole = head_eq;
        for arg in args {
            whole = mk_comb(&whole, &refl(arg)?)?;
        }
        let beta = beta_norm_conv(&rhs(&whole))?;
        let step = trans(&whole, &beta)?;
        acc = trans(&acc, &step)?;
    }
    Ok(acc)
}

/// `|- t = t'` from `|- t' = t`.
pub fn flip(thm: &Thm) -> hol_kernel::Result<Thm> {
    sym(thm)
}
