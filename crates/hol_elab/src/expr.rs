//! Elaborating surface expressions into kernel terms.
//!
//! Elaboration is bidirectional: an expected type, when known, flows
//! into binders and set literals; otherwise types are synthesized. Type
//! metavariables stand for the type arguments of polymorphic constants
//! and for omitted annotations, and are solved by unification. Tier
//! restrictions are checked here with messages in the tier's vocabulary.

use std::collections::BTreeSet;

use hol_kernel::{Name, Term, Type, MEM, SET_OF};
use hol_syntax::{BinOp, Binder, BinderKind, Expr, Span, Tier};

use crate::diag::{fail, Diagnostic, Result};
use crate::env::{ConstInfo, Env, SymbolKind};
use crate::print::print_term;
use crate::types::{elab_type, TypePosition, TypeScope, Unifier};

/// The largest numeral literal accepted. Numbers are successor towers,
/// and every traversal of a term is recursive, so a numeral's size is a
/// stack depth; this keeps literals within what the browser build's
/// stack can carry.
pub const MAX_NUMERAL: u64 = 500;

/// Term variables in scope, innermost last, plus the type variables.
#[derive(Clone, Debug, Default)]
pub struct Scope {
    pub types: TypeScope,
    vars: Vec<(Name, Term)>,
}

impl Scope {
    pub fn new(types: TypeScope) -> Scope {
        Scope {
            types,
            vars: Vec::new(),
        }
    }

    pub fn lookup(&self, name: &str) -> Option<&Term> {
        self.vars
            .iter()
            .rev()
            .find(|(n, _)| n.as_str() == name)
            .map(|(_, t)| t)
    }

    pub fn push(&mut self, var: Term) {
        let name = var
            .as_free()
            .expect("scope entries are free variables")
            .0
            .clone();
        self.vars.push((name, var));
    }

    /// Binds a name to an arbitrary closed term, as for the recursive
    /// result names of a `defrec` arm.
    pub fn push_named(&mut self, name: Name, term: Term) {
        self.vars.push((name, term));
    }

    pub fn pop(&mut self) {
        self.vars.pop();
    }

    pub fn vars(&self) -> &[(Name, Term)] {
        &self.vars
    }

    pub fn names(&self) -> BTreeSet<Name> {
        self.vars.iter().map(|(n, _)| n.clone()).collect()
    }
}

pub struct Elab<'e> {
    pub env: &'e Env,
    pub unifier: Unifier,
}

impl<'e> Elab<'e> {
    pub fn new(env: &'e Env) -> Elab<'e> {
        Elab {
            env,
            unifier: Unifier::new(),
        }
    }

    /// An elaborator sharing an existing type unifier, so type
    /// metavariables solved elsewhere (for instance by proof-expression
    /// unification) are visible here and vice versa.
    pub fn with_unifier(env: &'e Env, unifier: Unifier) -> Elab<'e> {
        Elab { env, unifier }
    }

    pub fn into_unifier(self) -> Unifier {
        self.unifier
    }

    fn tier(&self) -> Tier {
        self.env.tier
    }

    fn zonk(&self, t: &Term) -> Term {
        self.unifier.zonk_term(t)
    }

    fn show(&self, t: &Term) -> String {
        print_term(self.env, &self.zonk(t))
    }

    /// Zonks a finished term and turns unsolved type metavariables into
    /// fresh rigid type variables, returning their names. Used for
    /// theorem statements, which are implicitly polymorphic in the
    /// types that nothing determines (as in Isabelle).
    pub fn finish_generalizing(
        &mut self,
        term: &Term,
        avoid: &BTreeSet<Name>,
    ) -> (Term, Vec<Name>) {
        let term = self.zonk(term);
        let mut vars = BTreeSet::new();
        term.type_vars(&mut vars);
        let mut fresh = Vec::new();
        let mut counter = 0;
        for meta in vars.into_iter().filter(crate::types::is_meta) {
            let name = loop {
                counter += 1;
                let candidate = Name::new(&format!("T{counter}"));
                if !avoid.contains(&candidate) && !fresh.contains(&candidate) {
                    break candidate;
                }
            };
            let _ = self
                .unifier
                .unify(&Type::Var(meta), &Type::Var(name.clone()));
            fresh.push(name);
        }
        (self.zonk(&term), fresh)
    }

    /// Zonks a finished term and rejects unsolved metavariables.
    pub fn finish(&self, term: &Term, span: Span) -> Result<Term> {
        let term = self.zonk(term);
        let mut vars = BTreeSet::new();
        term.type_vars(&mut vars);
        if vars.iter().any(crate::types::is_meta) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "could not infer every type in `{}`",
                    print_term(self.env, &term)
                ),
            )
            .note("add a type annotation, for example `fun x : T => ...` or `empty(T)`"));
        }
        Ok(term)
    }

    /// A constant at a fresh instance of its generic type.
    pub fn constant_term(&mut self, info: &ConstInfo) -> Term {
        let (ty, _) = self.unifier.instantiate(&info.ty);
        Term::constant(self.env.theory().signature(), &info.name, ty)
            .expect("declared constants are instances of their generic type")
    }

    fn unify_types(
        &mut self,
        actual: &Type,
        expected: &Type,
        span: Span,
        what: impl FnOnce() -> String,
    ) -> Result<()> {
        if self.unifier.unify(actual, expected).is_err() {
            let actual = self.unifier.zonk(actual);
            let expected = self.unifier.zonk(expected);
            return Err(Diagnostic::new(
                span,
                format!(
                    "{} has type `{actual}`, but `{expected}` was expected here",
                    what()
                ),
            ));
        }
        Ok(())
    }

    fn expect(&mut self, term: Term, expected: Option<&Type>, span: Span) -> Result<Term> {
        if let Some(expected) = expected {
            let ty = term.ty().clone();
            let shown = self.show(&term);
            self.unify_types(&ty, expected, span, || format!("`{shown}`"))?;
        }
        Ok(self.zonk(&term))
    }

    fn app(&mut self, f: &Term, x: &Term, span: Span) -> Result<Term> {
        let f = self.zonk(f);
        let Some((dom, _)) = f.ty().as_fun() else {
            fail!(
                span,
                "`{}` is not a function or predicate, so it cannot be applied",
                self.show(&f)
            );
        };
        let dom = dom.clone();
        let x_ty = x.ty().clone();
        let shown = self.show(x);
        self.unify_types(&x_ty, &dom, span, || format!("the argument `{shown}`"))?;
        let f = self.zonk(&f);
        let x = self.zonk(x);
        Term::app(&f, &x).map_err(|e| Diagnostic::new(span, e.message))
    }

    fn lam(&mut self, var: &Term, body: &Term, span: Span) -> Result<Term> {
        let var = self.zonk(var);
        let body = self.zonk(body);
        Term::lam(&var, &body).map_err(|e| Diagnostic::new(span, e.message))
    }

    fn quantifier(
        &mut self,
        kind: BinderKind,
        var: &Term,
        body: &Term,
        span: Span,
    ) -> Result<Term> {
        let var = self.zonk(var);
        let body = self.zonk(body);
        let result = match kind {
            BinderKind::Forall => Term::forall(&var, &body),
            BinderKind::Exists => Term::exists(&var, &body),
            BinderKind::Fun => Term::lam(&var, &body),
        };
        result.map_err(|e| Diagnostic::new(span, e.message))
    }

    /// Elaborates a formula: a term of type `Prop`.
    pub fn formula(&mut self, scope: &mut Scope, expr: &Expr) -> Result<Term> {
        self.expr(scope, expr, Some(&Type::prop()))
    }

    pub fn expr(
        &mut self,
        scope: &mut Scope,
        expr: &Expr,
        expected: Option<&Type>,
    ) -> Result<Term> {
        let span = expr.span();
        match expr {
            Expr::True(_) => self.expect(Term::true_(), expected, span),
            Expr::False(_) => self.expect(Term::false_(), expected, span),
            Expr::Var(ident) => {
                let term = self.variable(scope, &ident.name, expected, span)?;
                self.expect(term, expected, span)
            }
            Expr::Num(n, _) => {
                let term = self.numeral(*n, span)?;
                self.expect(term, expected, span)
            }
            Expr::App(head, args, _) => {
                let term = self.application(scope, head, args, span)?;
                self.expect(term, expected, span)
            }
            Expr::TypeApp(name, ty, _) => {
                let Some(info) = self.env.constant(&name.name).cloned() else {
                    fail!(name.span, "unknown name `{}`", name.name);
                };
                let elem = elab_type(self.env, &scope.types, ty, TypePosition::Declaration)?;
                let term = self.constant_term(&info);
                let want = Type::set(elem);
                self.unify_types(term.ty(), &want, span, || format!("`{}`", name.name))?;
                let term = self.zonk(&term);
                self.expect(term, expected, span)
            }
            Expr::Binder(BinderKind::Fun, binders, body, _) => {
                let term = self.lambda(scope, binders, body, expected, span)?;
                self.expect(term, expected, span)
            }
            Expr::Binder(kind, binders, body, _) => {
                let term = self.quantified(scope, *kind, binders, body, span)?;
                self.expect(term, expected, span)
            }
            Expr::Not(inner, _) => {
                let p = self.formula(scope, inner)?;
                let term = Term::not(&p).map_err(|e| Diagnostic::new(span, e.message))?;
                self.expect(term, expected, span)
            }
            Expr::Binary(op, lhs, rhs, _) => {
                let term = self.binary(scope, *op, lhs, rhs, span)?;
                self.expect(term, expected, span)
            }
            Expr::SetLit(elems, _) => {
                let term = self.set_literal(scope, elems, expected, span)?;
                self.expect(term, expected, span)
            }
            Expr::SetBuilder(var, ty, body, _) => {
                let elem = elab_type(self.env, &scope.types, ty, TypePosition::Binder)?;
                let x = Term::free(var.name.as_str(), elem);
                scope.push(x.clone());
                let body = self.formula(scope, body);
                scope.pop();
                let pred = self.lam(&x, &body?, span)?;
                let term = Term::set_of(&pred).map_err(|e| Diagnostic::new(span, e.message))?;
                self.expect(term, expected, span)
            }
        }
    }

    fn is_predicate_expected(&self, expected: Option<&Type>) -> bool {
        match expected {
            None => false,
            Some(ty) => {
                let ty = self.unifier.zonk(ty);
                let (doms, cod) = ty.strip_fun();
                (!doms.is_empty() && cod.is_prop())
                    || matches!(ty, Type::Var(ref v) if crate::types::is_meta(v))
            }
        }
    }

    fn check_min_tier(&self, info: &ConstInfo, span: Span) -> Result<()> {
        if info.min_tier > self.tier() && !self.env.importing {
            return Err(Diagnostic::new(
                span,
                format!("`{}` needs `logic {}`", info.name, info.min_tier.name()),
            )
            .note(format!(
                "add `logic {}` at the top of the file",
                info.min_tier.name()
            )));
        }
        Ok(())
    }

    fn variable(
        &mut self,
        scope: &Scope,
        name: &str,
        expected: Option<&Type>,
        span: Span,
    ) -> Result<Term> {
        if let Some(var) = scope.lookup(name) {
            return Ok(var.clone());
        }
        if let Some(info) = self.env.constant(name).cloned() {
            self.check_min_tier(&info, span)?;
            if info.arity > 0 && self.tier() < Tier::Hol && !self.is_predicate_expected(expected) {
                let placeholders = (0..info.arity)
                    .map(|i| format!("x{}", i + 1))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "`{name}` is a {} that takes {} argument{}",
                        info.kind.describe(),
                        info.arity,
                        if info.arity == 1 { "" } else { "s" }
                    ),
                )
                .suggest(format!("{name}({placeholders})")));
            }
            return Ok(self.constant_term(&info));
        }
        if self.env.theorem(name).is_some() {
            return Err(
                Diagnostic::new(span, format!("`{name}` is a theorem, not a term")).note(format!(
                    "use it in a proof step, for example `exact {name}` or `apply {name}`"
                )),
            );
        }
        let mut diag = Diagnostic::new(span, format!("unknown name `{name}`"));
        let expects_prop = expected
            .map(|t| self.unifier.zonk(t).is_prop())
            .unwrap_or(false);
        if expects_prop {
            diag = diag.note(format!(
                "declare it as a proposition parameter `({name} : Prop)` or as a predicate with `pred {name}(...)`"
            ));
        } else if name.chars().next().map(char::is_uppercase).unwrap_or(false) {
            diag = diag.note(format!(
                "declare it with `pred {name}(...)`, `def {name} ...`, or `const {name} : T`"
            ));
        } else {
            diag = diag.note(format!(
                "declare it with `const {name} : T`, or bind it with `forall {name} : T, ...` or a theorem parameter `({name} : T)`"
            ));
        }
        Err(diag)
    }

    fn numeral(&mut self, n: u64, span: Span) -> Result<Term> {
        if self.tier() < Tier::FolNat {
            return Err(
                Diagnostic::new(span, format!("the numeral `{n}` needs natural numbers"))
                    .note("add `logic fol_nat` at the top of the file to enable `Nat`"),
            );
        }
        let (Some(zero), Some(succ)) = (
            self.env.constant("zero").cloned(),
            self.env.constant("succ").cloned(),
        ) else {
            fail!(
                span,
                "natural numbers are not available: `Nat` is not declared"
            );
        };
        if n > MAX_NUMERAL {
            return Err(Diagnostic::new(
                span,
                format!("the numeral `{n}` is too large to check"),
            )
            .note(format!(
                "a number is built from `zero` by applying `succ`, one application per unit, so the checker supports numerals up to {MAX_NUMERAL}"
            )));
        }
        let mut term = self.constant_term(&zero);
        let succ = self.constant_term(&succ);
        for _ in 0..n {
            term = self.app(&succ, &term, span)?;
        }
        Ok(term)
    }

    fn application(
        &mut self,
        scope: &mut Scope,
        head: &Expr,
        args: &[Expr],
        span: Span,
    ) -> Result<Term> {
        let (mut func, arity, described): (Term, Option<usize>, String) = match head {
            Expr::Var(ident) => {
                if let Some(var) = scope.lookup(&ident.name) {
                    let arity = var.ty().strip_fun().0.len();
                    (var.clone(), Some(arity), format!("`{}`", ident.name))
                } else if let Some(info) = self.env.constant(&ident.name).cloned() {
                    self.check_min_tier(&info, ident.span)?;
                    let described = format!("{} `{}`", info.kind.describe(), ident.name);
                    (self.constant_term(&info), Some(info.arity), described)
                } else {
                    return Err(self
                        .variable(scope, &ident.name, None, ident.span)
                        .unwrap_err());
                }
            }
            other => {
                if self.tier() < Tier::Hol {
                    fail!(
                        other.span(),
                        "applying an expression that is not a name needs `logic hol`"
                    );
                }
                let f = self.expr(scope, other, None)?;
                (f, None, "the function".to_string())
            }
        };
        if let Some(arity) = arity {
            if args.len() > arity {
                fail!(
                    span,
                    "{described} takes {arity} argument{}, but {} were given",
                    if arity == 1 { "" } else { "s" },
                    args.len()
                );
            }
            if args.len() < arity && self.tier() < Tier::Hol {
                return Err(Diagnostic::new(
                    span,
                    format!(
                        "{described} takes {arity} argument{}, but only {} {} given",
                        if arity == 1 { "" } else { "s" },
                        args.len(),
                        if args.len() == 1 { "was" } else { "were" }
                    ),
                )
                .note("partial application needs `logic hol`"));
            }
        }
        for arg in args {
            let f_ty = self.unifier.zonk(func.ty());
            let Some((dom, _)) = f_ty.as_fun() else {
                fail!(arg.span(), "{described} is applied to too many arguments");
            };
            let dom = dom.clone();
            let x = self.expr(scope, arg, Some(&dom))?;
            func = self.app(&func, &x, arg.span())?;
        }
        Ok(func)
    }

    fn binder_vars(
        &mut self,
        scope: &Scope,
        binders: &[Binder],
        expected_doms: &[Type],
        is_lambda: bool,
    ) -> Result<Vec<Term>> {
        let mut vars = Vec::new();
        let mut index = 0;
        for binder in binders {
            let annotated = match &binder.ty {
                Some(ty) => Some(elab_type(self.env, &scope.types, ty, TypePosition::Binder)?),
                None => None,
            };
            for name in &binder.names {
                let ty = match (&annotated, expected_doms.get(index)) {
                    (Some(ann), Some(exp)) => {
                        let exp = exp.clone();
                        self.unify_types(ann, &exp, name.span, || {
                            format!("the binder `{}`", name.name)
                        })?;
                        ann.clone()
                    }
                    (Some(ann), None) => ann.clone(),
                    (None, Some(exp)) => exp.clone(),
                    (None, None) => {
                        if self.tier() < Tier::Hol {
                            let form = if is_lambda {
                                format!("fun {} : T => ...", name.name)
                            } else {
                                format!("forall {} : T, ...", name.name)
                            };
                            return Err(Diagnostic::new(
                                name.span,
                                format!("the variable `{}` needs a type", name.name),
                            )
                            .suggest(form));
                        }
                        self.unifier.fresh()
                    }
                };
                vars.push(Term::free(name.name.as_str(), ty));
                index += 1;
            }
        }
        Ok(vars)
    }

    fn quantified(
        &mut self,
        scope: &mut Scope,
        kind: BinderKind,
        binders: &[Binder],
        body: &Expr,
        span: Span,
    ) -> Result<Term> {
        let vars = self.binder_vars(scope, binders, &[], false)?;
        for var in &vars {
            scope.push(var.clone());
        }
        let body = self.formula(scope, body);
        for _ in &vars {
            scope.pop();
        }
        let mut term = body?;
        for var in vars.iter().rev() {
            term = self.quantifier(kind, var, &term, span)?;
        }
        Ok(term)
    }

    fn lambda(
        &mut self,
        scope: &mut Scope,
        binders: &[Binder],
        body: &Expr,
        expected: Option<&Type>,
        span: Span,
    ) -> Result<Term> {
        let count: usize = binders.iter().map(|b| b.names.len()).sum();
        let expected = expected.map(|t| self.unifier.zonk(t));
        let (doms, body_expected): (Vec<Type>, Option<Type>) = match &expected {
            Some(ty) => {
                let mut doms = Vec::new();
                let mut current = ty.clone();
                for _ in 0..count {
                    match current.as_fun() {
                        Some((dom, cod)) => {
                            doms.push(dom.clone());
                            current = cod.clone();
                        }
                        None => {
                            if matches!(current, Type::Var(ref v) if crate::types::is_meta(v)) {
                                let dom = self.unifier.fresh();
                                let cod = self.unifier.fresh();
                                let _ = self
                                    .unifier
                                    .unify(&current, &Type::fun(dom.clone(), cod.clone()));
                                doms.push(dom);
                                current = cod;
                            } else {
                                fail!(
                                    span,
                                    "a `fun` with {count} binder{} cannot have type `{ty}`",
                                    if count == 1 { "" } else { "s" }
                                );
                            }
                        }
                    }
                }
                (doms, Some(current))
            }
            None => (Vec::new(), None),
        };
        if self.tier() < Tier::Hol {
            let builds_predicate = body_expected
                .as_ref()
                .map(|t| self.unifier.zonk(t).is_prop())
                .unwrap_or(false);
            if !builds_predicate {
                return Err(Diagnostic::new(
                    span,
                    "a `fun` that builds a function value needs `logic hol`".to_string(),
                )
                .note("in first-order logic, `fun x y : T => ...` only describes a predicate argument such as `Reflexive(fun x y : T => x = y)`"));
            }
        }
        let vars = self.binder_vars(scope, binders, &doms, true)?;
        for var in &vars {
            scope.push(var.clone());
        }
        let body = self.expr(scope, body, body_expected.as_ref());
        for _ in &vars {
            scope.pop();
        }
        let mut term = body?;
        for var in vars.iter().rev() {
            term = self.lam(var, &term, span)?;
        }
        Ok(term)
    }

    fn binary(
        &mut self,
        scope: &mut Scope,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        span: Span,
    ) -> Result<Term> {
        let kernel = |r: hol_kernel::Result<Term>| r.map_err(|e| Diagnostic::new(span, e.message));
        match op {
            BinOp::And | BinOp::Or | BinOp::Imp | BinOp::Iff => {
                let a = self.formula(scope, lhs)?;
                let b = self.formula(scope, rhs)?;
                kernel(match op {
                    BinOp::And => Term::and(&a, &b),
                    BinOp::Or => Term::or(&a, &b),
                    BinOp::Imp => Term::imp(&a, &b),
                    _ => Term::iff(&a, &b),
                })
            }
            BinOp::Eq => {
                let a = self.expr(scope, lhs, None)?;
                let a_ty = a.ty().clone();
                let b = match self.expr(scope, rhs, Some(&a_ty)) {
                    Ok(b) => b,
                    Err(_) => {
                        let b = self.expr(scope, rhs, None)?;
                        fail!(
                            span,
                            "cannot compare `{}` of type `{}` with `{}` of type `{}`",
                            self.show(&a),
                            self.unifier.zonk(a.ty()),
                            self.show(&b),
                            self.unifier.zonk(b.ty())
                        );
                    }
                };
                let a = self.zonk(&a);
                let b = self.zonk(&b);
                if self.tier() < Tier::Hol && a.ty().as_fun().is_some() {
                    fail!(span, "equality between functions needs `logic hol`");
                }
                kernel(Term::eq(&a, &b))
            }
            BinOp::Mem => {
                let x = self.expr(scope, lhs, None)?;
                let want = Type::set(x.ty().clone());
                let set = self.expr(scope, rhs, Some(&want))?;
                let x = self.zonk(&x);
                let mem = self.builtin(MEM, span)?;
                let t = self.app(&mem, &x, span)?;
                self.app(&t, &set, span)
            }
            BinOp::Subset => {
                let elem = self.unifier.fresh();
                let want = Type::set(elem);
                let a = self.expr(scope, lhs, Some(&want))?;
                let b = self.expr(scope, rhs, Some(&want))?;
                let subset = self.builtin("subset", span)?;
                let t = self.app(&subset, &a, span)?;
                self.app(&t, &b, span)
            }
            BinOp::Add | BinOp::Mul | BinOp::Sub | BinOp::Le | BinOp::Lt => {
                if self.tier() < Tier::FolNat {
                    return Err(Diagnostic::new(
                        span,
                        format!("the operator `{}` needs natural numbers", op.symbol()),
                    )
                    .note("add `logic fol_nat` at the top of the file to enable `Nat`"));
                }
                let name = match op {
                    BinOp::Add => "add",
                    BinOp::Mul => "mul",
                    BinOp::Sub => "sub",
                    BinOp::Le => "le",
                    _ => "lt",
                };
                let f = self.builtin(name, span)?;
                let nat = f.ty().as_fun().map(|(d, _)| d.clone()).unwrap();
                let a = self.expr(scope, lhs, Some(&nat))?;
                let b = self.expr(scope, rhs, Some(&nat))?;
                let t = self.app(&f, &a, span)?;
                self.app(&t, &b, span)
            }
        }
    }

    fn builtin(&mut self, name: &str, span: Span) -> Result<Term> {
        let Some(info) = self.env.constant(name).cloned() else {
            fail!(span, "the built-in operation `{name}` is not available");
        };
        Ok(self.constant_term(&info))
    }

    fn set_literal(
        &mut self,
        scope: &mut Scope,
        elems: &[Expr],
        expected: Option<&Type>,
        span: Span,
    ) -> Result<Term> {
        let elem_ty = match expected.map(|t| self.unifier.zonk(t)) {
            Some(Type::Con(name, args)) if name.as_str() == hol_kernel::SET && args.len() == 1 => {
                args[0].clone()
            }
            _ => self.unifier.fresh(),
        };
        let mut terms = Vec::new();
        for elem in elems {
            terms.push(self.expr(scope, elem, Some(&elem_ty))?);
        }
        let singleton = self.builtin("singleton", span)?;
        let union = self.builtin("union", span)?;
        let mut result: Option<Term> = None;
        for elem in terms.iter().rev() {
            let single = self.app(&singleton, elem, span)?;
            result = Some(match result {
                None => single,
                Some(rest) => {
                    let u = self.app(&union, &single, span)?;
                    self.app(&u, &rest, span)?
                }
            });
        }
        Ok(result.expect("non-empty literal"))
    }
}

/// The kernel set-builder constant name, re-exported for the printer and
/// the simplifier.
pub const SET_BUILDER: &str = SET_OF;

impl SymbolKind {
    pub fn is_applicable(self) -> bool {
        !matches!(self, SymbolKind::Const)
    }
}
