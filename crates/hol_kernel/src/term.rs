//! Simply typed lambda terms in locally nameless form.
//!
//! Bound variables are de Bruijn indices; free variables are named. This
//! makes substitution capture-free by construction: a free variable can
//! never be captured by a binder because binders do not bind names.
//!
//! Every term is well typed by construction. The public constructors
//! ([`Term::app`], [`Term::lam`], [`Term::constant`]) check types and
//! reject inputs with dangling bound variables, so any `Term` reachable
//! from outside this module through those constructors is locally
//! closed and well typed. Lambda bodies obtained through [`Term::view`]
//! are not locally closed and are rejected by the public constructors;
//! open them with [`Term::open_fresh`] instead.

use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::error::{bail, Result};
use crate::name::{fresh_name, Name};
use crate::signature::Signature;
use crate::types::{Type, TypeSubst};

#[derive(Clone)]
pub struct Term(Rc<Node>);

struct Node {
    kind: Kind,
    ty: Type,
    /// Number of enclosing binders this term needs before it is closed.
    /// Zero means locally closed.
    loose: u32,
}

enum Kind {
    Free(Name),
    Bound(u32),
    Const(Name),
    App(Term, Term),
    Lam(Name, Type, Term),
}

/// Read-only structural view of a term.
pub enum TermView<'a> {
    Free(&'a Name, &'a Type),
    Bound(u32, &'a Type),
    Const(&'a Name, &'a Type),
    App(&'a Term, &'a Term),
    /// Binder display name, binder type, and the body with `Bound(0)`
    /// referring to the binder. The body is not locally closed.
    Lam(&'a Name, &'a Type, &'a Term),
}

impl Term {
    fn mk(kind: Kind, ty: Type, loose: u32) -> Term {
        Term(Rc::new(Node { kind, ty, loose }))
    }

    /// A free variable. Free variables of a type are assumed to exist,
    /// which is the HOL convention that every type is inhabited.
    pub fn free(name: impl Into<Name>, ty: Type) -> Term {
        Term::mk(Kind::Free(name.into()), ty, 0)
    }

    /// A constant at a type instance of its declared generic type.
    pub fn constant(sig: &Signature, name: impl Into<Name>, ty: Type) -> Result<Term> {
        let name = name.into();
        sig.check_const_instance(&name, &ty)?;
        Ok(Term::mk(Kind::Const(name), ty, 0))
    }

    pub(crate) fn constant_unchecked(name: Name, ty: Type) -> Term {
        Term::mk(Kind::Const(name), ty, 0)
    }

    pub(crate) fn bound(index: u32, ty: Type) -> Term {
        Term::mk(Kind::Bound(index), ty, index + 1)
    }

    /// Application, checked: `f : A -> B` and `x : A`.
    pub fn app(f: &Term, x: &Term) -> Result<Term> {
        f.require_closed("app")?;
        x.require_closed("app")?;
        let Some((dom, _)) = f.ty().as_fun() else {
            bail!(
                "app",
                "cannot apply `{f}` of non-function type `{}` to `{x}`",
                f.ty()
            );
        };
        if dom != x.ty() {
            bail!(
                "app",
                "cannot apply `{f}` to `{x}`: expected an argument of type `{dom}`, but `{x}` has type `{}`",
                x.ty()
            );
        }
        Ok(Term::app_raw(f, x))
    }

    pub(crate) fn app_raw(f: &Term, x: &Term) -> Term {
        let cod = f
            .ty()
            .as_fun()
            .map(|(_, cod)| cod.clone())
            .expect("app_raw on a function type");
        let loose = f.0.loose.max(x.0.loose);
        Term::mk(Kind::App(f.clone(), x.clone()), cod, loose)
    }

    /// `f a1 ... an`.
    pub fn apps(f: &Term, args: &[Term]) -> Result<Term> {
        let mut current = f.clone();
        for arg in args {
            current = Term::app(&current, arg)?;
        }
        Ok(current)
    }

    /// Abstraction over a free variable: `lam(x, body)` is `λx. body`.
    pub fn lam(var: &Term, body: &Term) -> Result<Term> {
        let Some((name, ty)) = var.as_free() else {
            bail!("lam", "binder `{var}` is not a free variable");
        };
        body.require_closed("lam")?;
        let abstracted = body.abstract_at(name, ty, 0);
        Ok(Term::lam_raw(name.clone(), ty.clone(), abstracted))
    }

    /// `λx1 ... xn. body`.
    pub fn lams(vars: &[Term], body: &Term) -> Result<Term> {
        let mut current = body.clone();
        for var in vars.iter().rev() {
            current = Term::lam(var, &current)?;
        }
        Ok(current)
    }

    pub(crate) fn lam_raw(name: Name, ty: Type, body: Term) -> Term {
        let full = Type::fun(ty.clone(), body.ty().clone());
        let loose = body.0.loose.saturating_sub(1);
        Term::mk(Kind::Lam(name, ty, body), full, loose)
    }

    pub fn ty(&self) -> &Type {
        &self.0.ty
    }

    pub fn view(&self) -> TermView<'_> {
        match &self.0.kind {
            Kind::Free(name) => TermView::Free(name, &self.0.ty),
            Kind::Bound(index) => TermView::Bound(*index, &self.0.ty),
            Kind::Const(name) => TermView::Const(name, &self.0.ty),
            Kind::App(f, x) => TermView::App(f, x),
            Kind::Lam(name, ty, body) => TermView::Lam(name, ty, body),
        }
    }

    /// True when the term has no dangling bound variables.
    pub fn is_closed(&self) -> bool {
        self.0.loose == 0
    }

    pub(crate) fn require_closed(&self, rule: &'static str) -> Result<()> {
        if !self.is_closed() {
            bail!(
                rule,
                "term `{self}` has dangling bound variables; open lambda bodies with `open_fresh`"
            );
        }
        Ok(())
    }

    pub fn as_free(&self) -> Option<(&Name, &Type)> {
        match &self.0.kind {
            Kind::Free(name) => Some((name, &self.0.ty)),
            _ => None,
        }
    }

    pub fn as_const(&self) -> Option<(&Name, &Type)> {
        match &self.0.kind {
            Kind::Const(name) => Some((name, &self.0.ty)),
            _ => None,
        }
    }

    pub fn is_const_named(&self, name: &str) -> bool {
        matches!(&self.0.kind, Kind::Const(n) if n.as_str() == name)
    }

    pub fn as_app(&self) -> Option<(&Term, &Term)> {
        match &self.0.kind {
            Kind::App(f, x) => Some((f, x)),
            _ => None,
        }
    }

    pub fn is_lam(&self) -> bool {
        matches!(&self.0.kind, Kind::Lam(..))
    }

    /// The head and arguments of an application spine.
    pub fn strip_app(&self) -> (&Term, Vec<&Term>) {
        let mut args = Vec::new();
        let mut current = self;
        while let Kind::App(f, x) = &current.0.kind {
            args.push(x);
            current = f;
        }
        args.reverse();
        (current, args)
    }

    pub fn free_vars(&self) -> BTreeSet<(Name, Type)> {
        let mut out = BTreeSet::new();
        self.collect_free_vars(&mut out);
        out
    }

    fn collect_free_vars(&self, out: &mut BTreeSet<(Name, Type)>) {
        match &self.0.kind {
            Kind::Free(name) => {
                out.insert((name.clone(), self.0.ty.clone()));
            }
            Kind::Bound(_) | Kind::Const(_) => {}
            Kind::App(f, x) => {
                f.collect_free_vars(out);
                x.collect_free_vars(out);
            }
            Kind::Lam(_, _, body) => body.collect_free_vars(out),
        }
    }

    pub fn free_var_names(&self) -> BTreeSet<Name> {
        self.free_vars().into_iter().map(|(name, _)| name).collect()
    }

    pub fn has_free(&self, name: &Name, ty: &Type) -> bool {
        match &self.0.kind {
            Kind::Free(n) => n == name && &self.0.ty == ty,
            Kind::Bound(_) | Kind::Const(_) => false,
            Kind::App(f, x) => f.has_free(name, ty) || x.has_free(name, ty),
            Kind::Lam(_, _, body) => body.has_free(name, ty),
        }
    }

    /// True when the free variable `var` occurs in the term.
    pub fn contains_var(&self, var: &Term) -> bool {
        match var.as_free() {
            Some((name, ty)) => self.has_free(name, ty),
            None => false,
        }
    }

    pub fn type_vars(&self, out: &mut BTreeSet<Name>) {
        match &self.0.kind {
            Kind::Free(_) | Kind::Bound(_) | Kind::Const(_) => self.0.ty.type_vars(out),
            Kind::App(f, x) => {
                f.type_vars(out);
                x.type_vars(out);
            }
            Kind::Lam(_, ty, body) => {
                ty.type_vars(out);
                body.type_vars(out);
            }
        }
    }

    /// Counts constants named `name` anywhere in the term.
    pub fn count_const(&self, name: &Name) -> usize {
        match &self.0.kind {
            Kind::Const(n) => usize::from(n == name),
            Kind::Free(_) | Kind::Bound(_) => 0,
            Kind::App(f, x) => f.count_const(name) + x.count_const(name),
            Kind::Lam(_, _, body) => body.count_const(name),
        }
    }

    fn abstract_at(&self, name: &Name, ty: &Type, depth: u32) -> Term {
        match &self.0.kind {
            Kind::Free(n) => {
                if n == name && &self.0.ty == ty {
                    Term::bound(depth, ty.clone())
                } else {
                    self.clone()
                }
            }
            Kind::Bound(_) | Kind::Const(_) => self.clone(),
            Kind::App(f, x) => {
                let f2 = f.abstract_at(name, ty, depth);
                let x2 = x.abstract_at(name, ty, depth);
                if Rc::ptr_eq(&f.0, &f2.0) && Rc::ptr_eq(&x.0, &x2.0) {
                    self.clone()
                } else {
                    Term::app_raw(&f2, &x2)
                }
            }
            Kind::Lam(n, t, body) => {
                let body2 = body.abstract_at(name, ty, depth + 1);
                if Rc::ptr_eq(&body.0, &body2.0) {
                    self.clone()
                } else {
                    Term::lam_raw(n.clone(), t.clone(), body2)
                }
            }
        }
    }

    /// Replaces `Bound(depth)` with `arg` and lowers deeper indices by
    /// one, removing one binder level. `arg` must be locally closed.
    fn open_at(&self, depth: u32, arg: &Term) -> Term {
        if self.0.loose <= depth {
            return self.clone();
        }
        match &self.0.kind {
            Kind::Bound(index) => {
                if *index == depth {
                    arg.clone()
                } else if *index > depth {
                    Term::bound(index - 1, self.0.ty.clone())
                } else {
                    self.clone()
                }
            }
            Kind::Free(_) | Kind::Const(_) => self.clone(),
            Kind::App(f, x) => Term::app_raw(&f.open_at(depth, arg), &x.open_at(depth, arg)),
            Kind::Lam(n, t, body) => {
                Term::lam_raw(n.clone(), t.clone(), body.open_at(depth + 1, arg))
            }
        }
    }

    /// Instantiates the body of a lambda with an argument. `body` is the
    /// body from a `Lam` view; `arg` must be locally closed and have the
    /// binder's type.
    pub(crate) fn open_body(body: &Term, arg: &Term) -> Term {
        debug_assert!(arg.is_closed());
        body.open_at(0, arg)
    }

    /// Opens a lambda with a fresh free variable named after its binder,
    /// avoiding the free variables of the body and the names in `avoid`.
    /// Returns the variable and the opened body.
    pub fn open_fresh(&self, avoid: &BTreeSet<Name>) -> Option<(Term, Term)> {
        let Kind::Lam(name, ty, body) = &self.0.kind else {
            return None;
        };
        let body_free = body.free_var_names();
        let fresh = fresh_name(name, |candidate| {
            avoid.contains(candidate) || body_free.contains(candidate)
        });
        let var = Term::free(fresh, ty.clone());
        Some((var.clone(), Term::open_body(body, &var)))
    }

    /// Applies a lambda to an argument by substitution. `self` must be a
    /// lambda whose binder type matches `arg`.
    pub fn beta_apply(&self, arg: &Term) -> Result<Term> {
        arg.require_closed("beta")?;
        let Kind::Lam(_, ty, body) = &self.0.kind else {
            bail!("beta", "`{self}` is not a lambda abstraction");
        };
        if ty != arg.ty() {
            bail!(
                "beta",
                "cannot apply `{self}` to `{arg}`: binder has type `{ty}`, but the argument has type `{}`",
                arg.ty()
            );
        }
        Ok(Term::open_body(body, arg))
    }

    /// If the term is `(λx. b) a`, returns `b[a/x]`.
    pub fn beta_head(&self) -> Option<Term> {
        let (f, x) = self.as_app()?;
        f.beta_apply(x).ok()
    }

    /// Simultaneous substitution of locally closed terms for free
    /// variables. Each key must be a free variable and each value must
    /// have the key's type.
    pub fn subst_free(&self, map: &[(Term, Term)]) -> Result<Term> {
        for (var, value) in map {
            let Some((_, ty)) = var.as_free() else {
                bail!("subst", "substitution key `{var}` is not a free variable");
            };
            value.require_closed("subst")?;
            if value.ty() != ty {
                bail!(
                    "subst",
                    "cannot substitute `{value}` of type `{}` for `{var}` of type `{ty}`",
                    value.ty()
                );
            }
        }
        Ok(self.subst_free_unchecked(map))
    }

    fn subst_free_unchecked(&self, map: &[(Term, Term)]) -> Term {
        match &self.0.kind {
            Kind::Free(name) => {
                for (var, value) in map {
                    if let Some((n, ty)) = var.as_free() {
                        if n == name && ty == &self.0.ty {
                            return value.clone();
                        }
                    }
                }
                self.clone()
            }
            Kind::Bound(_) | Kind::Const(_) => self.clone(),
            Kind::App(f, x) => {
                Term::app_raw(&f.subst_free_unchecked(map), &x.subst_free_unchecked(map))
            }
            Kind::Lam(n, t, body) => {
                Term::lam_raw(n.clone(), t.clone(), body.subst_free_unchecked(map))
            }
        }
    }

    /// Instantiates type variables throughout the term.
    pub fn subst_type(&self, subst: &TypeSubst) -> Term {
        if subst.is_empty() {
            return self.clone();
        }
        match &self.0.kind {
            Kind::Free(name) => Term::free(name.clone(), self.0.ty.subst(subst)),
            Kind::Bound(index) => Term::bound(*index, self.0.ty.subst(subst)),
            Kind::Const(name) => Term::constant_unchecked(name.clone(), self.0.ty.subst(subst)),
            Kind::App(f, x) => Term::app_raw(&f.subst_type(subst), &x.subst_type(subst)),
            Kind::Lam(n, t, body) => {
                Term::lam_raw(n.clone(), t.subst(subst), body.subst_type(subst))
            }
        }
    }

    fn structural_cmp(&self, other: &Term) -> Ordering {
        if Rc::ptr_eq(&self.0, &other.0) {
            return Ordering::Equal;
        }
        fn rank(kind: &Kind) -> u8 {
            match kind {
                Kind::Free(_) => 0,
                Kind::Bound(_) => 1,
                Kind::Const(_) => 2,
                Kind::App(..) => 3,
                Kind::Lam(..) => 4,
            }
        }
        match (&self.0.kind, &other.0.kind) {
            (Kind::Free(a), Kind::Free(b)) | (Kind::Const(a), Kind::Const(b)) => {
                a.cmp(b).then_with(|| self.0.ty.cmp(&other.0.ty))
            }
            (Kind::Bound(a), Kind::Bound(b)) => a.cmp(b),
            (Kind::App(f1, x1), Kind::App(f2, x2)) => {
                f1.structural_cmp(f2).then_with(|| x1.structural_cmp(x2))
            }
            (Kind::Lam(_, t1, b1), Kind::Lam(_, t2, b2)) => {
                t1.cmp(t2).then_with(|| b1.structural_cmp(b2))
            }
            (a, b) => rank(a).cmp(&rank(b)),
        }
    }
}

/// Alpha-equivalence: binder display names are ignored.
impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        self.structural_cmp(other) == Ordering::Equal
    }
}

impl Eq for Term {}

impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Term) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Term {
    fn cmp(&self, other: &Term) -> Ordering {
        self.structural_cmp(other)
    }
}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0.kind {
            Kind::Free(name) => {
                0u8.hash(state);
                name.hash(state);
                self.0.ty.hash(state);
            }
            Kind::Bound(index) => {
                1u8.hash(state);
                index.hash(state);
            }
            Kind::Const(name) => {
                2u8.hash(state);
                name.hash(state);
                self.0.ty.hash(state);
            }
            Kind::App(f, x) => {
                3u8.hash(state);
                f.hash(state);
                x.hash(state);
            }
            Kind::Lam(_, ty, body) => {
                4u8.hash(state);
                ty.hash(state);
                body.hash(state);
            }
        }
    }
}
