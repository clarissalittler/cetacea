//! Surface types to kernel types, and a small unifier with type
//! metavariables for inference of omitted binder annotations and of the
//! type arguments of polymorphic constants.

use std::collections::{BTreeMap, BTreeSet};

use hol_kernel::{Name, Term, Type, TypeSubst, PROP, SET};
use hol_syntax::{Span, Tier, TypeExpr};

use crate::diag::{fail, Diagnostic, Result};
use crate::env::Env;

/// Metavariables are type variables whose name starts with `?`.
pub fn is_meta(name: &Name) -> bool {
    name.as_str().starts_with('?')
}

/// Two types that cannot be unified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypeMismatch;

#[derive(Clone, Debug, Default)]
pub struct Unifier {
    subst: TypeSubst,
    counter: u64,
}

impl Unifier {
    pub fn new() -> Unifier {
        Unifier::default()
    }

    pub fn fresh(&mut self) -> Type {
        self.counter += 1;
        Type::var(format!("?{}", self.counter))
    }

    /// Instantiates the type variables of a generic type with fresh
    /// metavariables.
    pub fn instantiate(&mut self, generic: &Type) -> (Type, TypeSubst) {
        let mut vars = BTreeSet::new();
        generic.type_vars(&mut vars);
        let subst: TypeSubst = vars.into_iter().map(|v| (v, self.fresh())).collect();
        (generic.subst(&subst), subst)
    }

    /// Applies the current substitution.
    pub fn zonk(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(name) => match self.subst.get(name) {
                Some(bound) => self.zonk(bound),
                None => ty.clone(),
            },
            Type::Con(name, args) => {
                Type::Con(name.clone(), args.iter().map(|a| self.zonk(a)).collect())
            }
        }
    }

    pub fn zonk_term(&self, term: &Term) -> Term {
        if self.subst.is_empty() {
            return term.clone();
        }
        let mut full = TypeSubst::new();
        for name in self.subst.keys() {
            full.insert(name.clone(), self.zonk(&Type::Var(name.clone())));
        }
        term.subst_type(&full)
    }

    fn occurs(&self, name: &Name, ty: &Type) -> bool {
        match self.zonk(ty) {
            Type::Var(n) => &n == name,
            Type::Con(_, args) => args.iter().any(|a| self.occurs(name, a)),
        }
    }

    /// Unifies two types. Only metavariables are solved; ordinary type
    /// variables (theorem type parameters) are rigid.
    pub fn unify(&mut self, a: &Type, b: &Type) -> std::result::Result<(), TypeMismatch> {
        let a = self.zonk(a);
        let b = self.zonk(b);
        match (&a, &b) {
            (Type::Var(x), Type::Var(y)) if x == y => Ok(()),
            (Type::Var(x), _) if is_meta(x) => {
                if self.occurs(x, &b) {
                    return Err(TypeMismatch);
                }
                self.subst.insert(x.clone(), b);
                Ok(())
            }
            (_, Type::Var(y)) if is_meta(y) => {
                if self.occurs(y, &a) {
                    return Err(TypeMismatch);
                }
                self.subst.insert(y.clone(), a);
                Ok(())
            }
            (Type::Con(n1, args1), Type::Con(n2, args2))
                if n1 == n2 && args1.len() == args2.len() =>
            {
                for (x, y) in args1.iter().zip(args2) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            _ => Err(TypeMismatch),
        }
    }

    pub fn has_unsolved(&self, ty: &Type) -> bool {
        match self.zonk(ty) {
            Type::Var(name) => is_meta(&name),
            Type::Con(_, args) => args.iter().any(|a| self.has_unsolved(a)),
        }
    }
}

/// Where a type occurs, which determines what a tier allows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypePosition {
    /// A theorem or definition parameter annotation, where predicate
    /// types such as `A -> Prop` are allowed in every tier.
    Param,
    /// A quantifier or lambda binder type.
    Binder,
    /// The result type of a definition, or a declared constant type.
    Declaration,
}

/// Type variables in scope: theorem type parameters and definition type
/// parameters.
#[derive(Clone, Debug, Default)]
pub struct TypeScope {
    pub vars: BTreeSet<Name>,
}

impl TypeScope {
    pub fn with(vars: impl IntoIterator<Item = Name>) -> TypeScope {
        TypeScope {
            vars: vars.into_iter().collect(),
        }
    }
}

pub fn elab_type(
    env: &Env,
    scope: &TypeScope,
    ty: &TypeExpr,
    position: TypePosition,
) -> Result<Type> {
    let out = elab_type_inner(env, scope, ty)?;
    check_tier_type(env, &out, ty.span(), position)?;
    Ok(out)
}

fn elab_type_inner(env: &Env, scope: &TypeScope, ty: &TypeExpr) -> Result<Type> {
    match ty {
        TypeExpr::Fun(dom, cod, _) => Ok(Type::fun(
            elab_type_inner(env, scope, dom)?,
            elab_type_inner(env, scope, cod)?,
        )),
        TypeExpr::Named(name, args, span) => {
            let text = name.name.as_str();
            if text == "Type" {
                fail!(
                    *span,
                    "`Type` is the kind of types and cannot be used as a type here"
                );
            }
            if text == PROP {
                if !args.is_empty() {
                    fail!(*span, "`Prop` takes no arguments");
                }
                return Ok(Type::prop());
            }
            if scope.vars.contains(&Name::new(text)) {
                if !args.is_empty() {
                    fail!(*span, "type parameter `{text}` takes no arguments");
                }
                return Ok(Type::var(text));
            }
            let Some((qualified, arity)) = env.sort(text) else {
                let mut diag = Diagnostic::new(name.span, format!("unknown type `{text}`"));
                if text == "Nat" && env.tier < Tier::FolNat {
                    diag = diag.note("`Nat` is available from `logic fol_nat` up; add that line at the top of the file");
                } else if text == "List" || text == "Tree" {
                    diag = diag.note(format!(
                        "declare `{text}` with `data {text} ...`, which needs `logic hol`"
                    ));
                } else {
                    diag = diag.note(format!(
                        "declare it with `sort {text}` or add `({text} : Type)` to the parameters"
                    ));
                }
                return Err(diag);
            };
            if args.len() != arity {
                fail!(
                    *span,
                    "`{text}` takes {arity} type argument{}, but {} {} given",
                    if arity == 1 { "" } else { "s" },
                    args.len(),
                    if args.len() == 1 { "was" } else { "were" }
                );
            }
            let args = args
                .iter()
                .map(|arg| elab_type_inner(env, scope, arg))
                .collect::<Result<Vec<_>>>()?;
            Ok(Type::con(qualified, args))
        }
    }
}

fn check_tier_type(env: &Env, ty: &Type, span: Span, position: TypePosition) -> Result<()> {
    if env.tier == Tier::Hol {
        return Ok(());
    }
    match position {
        TypePosition::Param => {
            // Predicate parameters `A -> B -> Prop` are first-order
            // schematic predicates; function-valued parameters are not.
            let (doms, cod) = ty.strip_fun();
            if !doms.is_empty() && !cod.is_prop() {
                return Err(Diagnostic::new(
                    span,
                    format!("a parameter of function type `{ty}` needs `logic hol`"),
                )
                .note("in first-order logic, functions are declared with `func` rather than passed as parameters"));
            }
            for dom in doms {
                if dom.as_fun().is_some() {
                    return Err(Diagnostic::new(
                        span,
                        format!("a predicate over functions, `{ty}`, needs `logic hol`"),
                    ));
                }
            }
            Ok(())
        }
        TypePosition::Binder => {
            if ty.as_fun().is_some() {
                return Err(Diagnostic::new(
                    span,
                    format!("quantifying over a function type `{ty}` needs `logic hol`"),
                )
                .note(
                    "in first-order logic, quantifiers range over sorts such as `Person` or `Nat`",
                ));
            }
            if ty.is_prop() {
                return Err(Diagnostic::new(
                    span,
                    "quantifying over propositions needs `logic hol`".to_string(),
                )
                .note("state the proposition as a theorem parameter `(P : Prop)` instead"));
            }
            Ok(())
        }
        TypePosition::Declaration => {
            let (doms, _) = ty.strip_fun();
            for dom in doms {
                if dom.as_fun().is_some() {
                    return Err(Diagnostic::new(
                        span,
                        format!("a higher-order argument type in `{ty}` needs `logic hol`"),
                    ));
                }
            }
            Ok(())
        }
    }
}

/// True for the set type `Set T`.
pub fn is_set_type(ty: &Type) -> bool {
    matches!(ty, Type::Con(name, args) if name.as_str() == SET && args.len() == 1)
}

/// Renders a substitution for diagnostics.
pub fn describe_subst(subst: &BTreeMap<Name, Type>) -> String {
    subst
        .iter()
        .map(|(k, v)| format!("{k} := {v}"))
        .collect::<Vec<_>>()
        .join("; ")
}
