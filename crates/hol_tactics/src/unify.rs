//! Unification of kernel terms with metavariables.
//!
//! Metavariables are free variables whose names start with `?`; type
//! metavariables are type variables whose names start with `?`. Solving
//! a metavariable never touches the kernel: a substitution is applied
//! with `inst_type` and `inst`, which the kernel checks as usual.
//!
//! Metavariables applied to distinct variables (`?P x y`) are solved as
//! Miller patterns, by abstraction. Other applications fall back to
//! structural decomposition, which is what a first-order matcher would
//! do and covers the schematic predicates of the course.

use std::collections::{BTreeMap, BTreeSet};

use hol_elab::Unifier;
use hol_kernel::{beta_norm, inst, inst_type, Name, Term, TermView, Thm, Type};

#[derive(Clone, Debug, Default)]
pub struct Subst {
    terms: BTreeMap<Name, Term>,
    pub types: Unifier,
    counter: u64,
}

pub fn is_meta_name(name: &Name) -> bool {
    name.as_str().starts_with('?')
}

/// The metavariable at the head of a term, if it is one.
pub fn as_meta(t: &Term) -> Option<(&Name, &Type)> {
    match t.as_free() {
        Some((name, ty)) if is_meta_name(name) => Some((name, ty)),
        _ => None,
    }
}

/// The user-facing name of a metavariable such as `?P.3`.
pub fn meta_display_name(name: &Name) -> String {
    let text = name.as_str().trim_start_matches('?');
    match text.rfind('.') {
        Some(index) => text[..index].to_string(),
        None => text.to_string(),
    }
}

impl Subst {
    pub fn new() -> Subst {
        Subst::default()
    }

    pub fn fresh_meta(&mut self, hint: &str, ty: Type) -> Term {
        self.counter += 1;
        Term::free(format!("?{hint}.{}", self.counter), ty)
    }

    pub fn fresh_type_meta(&mut self) -> Type {
        self.types.fresh()
    }

    pub fn is_solved(&self, name: &Name) -> bool {
        self.terms.contains_key(name)
    }

    pub fn binding(&self, name: &Name) -> Option<&Term> {
        self.terms.get(name)
    }

    fn bind(&mut self, name: &Name, value: Term) {
        self.terms.insert(name.clone(), value);
    }

    pub fn apply_type(&self, ty: &Type) -> Type {
        self.types.zonk(ty)
    }

    /// Applies the substitution fully: type metavariables, then term
    /// metavariables, repeated until stable.
    pub fn apply(&self, t: &Term) -> Term {
        let mut current = self.types.zonk_term(t);
        for _ in 0..64 {
            let bindings: Vec<(Term, Term)> = current
                .free_vars()
                .into_iter()
                .filter(|(name, _)| is_meta_name(name))
                .filter_map(|(name, ty)| {
                    let value = self.terms.get(&name)?;
                    let value = self.types.zonk_term(value);
                    Some((Term::free(name, ty), value))
                })
                .collect();
            if bindings.is_empty() {
                return current;
            }
            // A binding's type may differ from the occurrence's type only
            // through unsolved type metavariables; zonking both sides first
            // keeps `subst_free` happy.
            let next = match current.subst_free(&bindings) {
                Ok(next) => next,
                Err(_) => return current,
            };
            let next = next.beta_normalize();
            if next == current {
                return current;
            }
            current = next;
        }
        current
    }

    /// Instantiates a theorem's metavariables and beta-normalizes.
    pub fn apply_thm(&self, thm: &Thm) -> hol_kernel::Result<Thm> {
        let mut vars = BTreeSet::new();
        thm.concl().type_vars(&mut vars);
        for hyp in thm.hyps() {
            hyp.type_vars(&mut vars);
        }
        let mut type_subst = hol_kernel::TypeSubst::new();
        for var in vars {
            if hol_elab::is_meta(&var) {
                type_subst.insert(var.clone(), self.types.zonk(&Type::Var(var)));
            }
        }
        let thm = inst_type(thm, &type_subst);
        let mut current = thm;
        for _ in 0..64 {
            let mut free = current.concl().free_vars();
            for hyp in current.hyps() {
                free.extend(hyp.free_vars());
            }
            let bindings: Vec<(Term, Term)> = free
                .into_iter()
                .filter(|(name, _)| is_meta_name(name))
                .filter_map(|(name, ty)| {
                    let value = self.terms.get(&name)?;
                    let value = self.types.zonk_term(value);
                    Some((Term::free(name, ty), value))
                })
                .collect();
            if bindings.is_empty() {
                break;
            }
            current = inst(&current, &bindings)?;
            current = beta_norm(&current)?;
        }
        Ok(current)
    }

    /// Unsolved metavariables occurring in a term.
    pub fn unsolved_in(&self, t: &Term) -> Vec<(Name, Type)> {
        self.apply(t)
            .free_vars()
            .into_iter()
            .filter(|(name, _)| is_meta_name(name))
            .collect()
    }

    /// Unifies two terms, extending the substitution. On failure the
    /// substitution may be partially extended; callers that need
    /// transactional behavior clone first.
    pub fn unify(&mut self, a: &Term, b: &Term) -> bool {
        let a = self.apply(a);
        let b = self.apply(b);
        if a == b {
            return self.types.unify(a.ty(), b.ty()).is_ok();
        }
        if self.try_pattern(&a, &b) || self.try_pattern(&b, &a) {
            return true;
        }
        match (a.view(), b.view()) {
            (TermView::App(f1, x1), TermView::App(f2, x2)) => {
                self.unify(f1, f2) && self.unify(x1, x2)
            }
            (TermView::Lam(_, ty1, _), TermView::Lam(_, ty2, _)) => {
                if self.types.unify(ty1, ty2).is_err() {
                    return false;
                }
                let avoid: BTreeSet<Name> = a
                    .free_var_names()
                    .union(&b.free_var_names())
                    .cloned()
                    .collect();
                let (var, body_a) = a.open_fresh(&avoid).expect("lambda");
                let body_b = b.beta_apply(&var).expect("lambda");
                self.unify(&body_a, &body_b)
            }
            (TermView::Free(n1, t1), TermView::Free(n2, t2))
            | (TermView::Const(n1, t1), TermView::Const(n2, t2)) => {
                n1 == n2 && self.types.unify(t1, t2).is_ok()
            }
            _ => false,
        }
    }

    /// Solves `?m x1 .. xn =?= b` when the `x_i` are distinct variables.
    fn try_pattern(&mut self, a: &Term, b: &Term) -> bool {
        let (head, args) = a.strip_app();
        let Some((name, head_ty)) = as_meta(head) else {
            return false;
        };
        let name = name.clone();
        let head_ty = head_ty.clone();
        if self.is_solved(&name) {
            return false;
        }
        // Occurs check.
        if b.free_vars().iter().any(|(n, _)| n == &name) {
            return false;
        }
        let mut vars: Vec<Term> = Vec::new();
        for arg in &args {
            match arg.as_free() {
                Some((n, _)) if !is_meta_name(n) && !vars.contains(arg) => {
                    vars.push((*arg).clone())
                }
                _ => return false,
            }
        }
        // The solution's type must agree with the metavariable's.
        let solution_ty = Type::funs(
            &vars.iter().map(|v| v.ty().clone()).collect::<Vec<_>>(),
            b.ty().clone(),
        );
        if self.types.unify(&head_ty, &solution_ty).is_err() {
            return false;
        }
        let solution = match Term::lams(&vars, b) {
            Ok(solution) => solution,
            Err(_) => return false,
        };
        self.bind(&name, solution);
        true
    }
}

/// Beta and eta helpers on terms, used to keep instantiated statements
/// tidy without going through the kernel (these are only used to build
/// terms; the kernel re-checks every theorem derived from them).
pub trait TermNorm {
    fn beta_normalize(&self) -> Term;
    fn eta_reduce(&self) -> Term;
}

impl TermNorm for Term {
    fn beta_normalize(&self) -> Term {
        match self.view() {
            TermView::App(f, x) => {
                let f = f.beta_normalize();
                let x = x.beta_normalize();
                match f.beta_apply(&x) {
                    Ok(reduced) => reduced.beta_normalize(),
                    Err(_) => Term::app(&f, &x).unwrap_or_else(|_| self.clone()),
                }
            }
            TermView::Lam(..) => {
                let (var, body) = self.open_fresh(&BTreeSet::new()).expect("lambda");
                let body = body.beta_normalize();
                Term::lam(&var, &body).unwrap_or_else(|_| self.clone())
            }
            _ => self.clone(),
        }
    }

    /// `fun x => f x` becomes `f` when `x` is not free in `f`.
    fn eta_reduce(&self) -> Term {
        let TermView::Lam(..) = self.view() else {
            return self.clone();
        };
        let (var, body) = self.open_fresh(&BTreeSet::new()).expect("lambda");
        let body = body.eta_reduce();
        if let Some((f, x)) = body.as_app() {
            if x == &var && !f.contains_var(&var) {
                return f.clone();
            }
        }
        Term::lam(&var, &body).unwrap_or_else(|_| self.clone())
    }
}

/// A schematized theorem with its type and term metavariables by
/// parameter name.
pub type Schematized = (Thm, BTreeMap<Name, Type>, BTreeMap<Name, Term>);

/// Replaces the free (non-meta) variables of a theorem's statement by
/// fresh metavariables, and its type variables by fresh type
/// metavariables, so it can be matched against a goal. Returns the
/// instantiated theorem and the mapping from parameter names to metas.
pub fn schematize(
    subst: &mut Subst,
    thm: &Thm,
    type_params: &[Name],
    term_params: &[(Name, Type)],
) -> hol_kernel::Result<Schematized> {
    let mut type_map = hol_kernel::TypeSubst::new();
    let mut type_metas = BTreeMap::new();
    for param in type_params {
        let meta = subst.fresh_type_meta();
        type_map.insert(param.clone(), meta.clone());
        type_metas.insert(param.clone(), meta);
    }
    let thm = inst_type(thm, &type_map);
    let mut bindings = Vec::new();
    let mut term_metas = BTreeMap::new();
    for (name, ty) in term_params {
        let ty = ty.subst(&type_map);
        let meta = subst.fresh_meta(name.as_str(), ty.clone());
        bindings.push((Term::free(name.clone(), ty), meta.clone()));
        term_metas.insert(name.clone(), meta);
    }
    let thm = inst(&thm, &bindings)?;
    Ok((thm, type_metas, term_metas))
}
