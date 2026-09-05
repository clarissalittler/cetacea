//! Simple types: type variables and applied type constructors.
//!
//! `Prop` is the type of propositions. `A -> B` is the type constructor
//! `fun` applied to two arguments. Every other constructor is declared in
//! a [`crate::Signature`].

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::name::Name;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Type {
    Var(Name),
    Con(Name, Vec<Type>),
}

pub type TypeSubst = BTreeMap<Name, Type>;

pub const PROP: &str = "Prop";
pub const FUN: &str = "fun";
pub const SET: &str = "Set";

impl Type {
    pub fn var(name: impl Into<Name>) -> Type {
        Type::Var(name.into())
    }

    pub fn con(name: impl Into<Name>, args: Vec<Type>) -> Type {
        Type::Con(name.into(), args)
    }

    pub fn prop() -> Type {
        Type::con(PROP, vec![])
    }

    pub fn fun(dom: Type, cod: Type) -> Type {
        Type::con(FUN, vec![dom, cod])
    }

    /// `[a, b] -> r` as `a -> b -> r`.
    pub fn funs(doms: &[Type], cod: Type) -> Type {
        doms.iter()
            .rev()
            .fold(cod, |acc, dom| Type::fun(dom.clone(), acc))
    }

    pub fn set(elem: Type) -> Type {
        Type::con(SET, vec![elem])
    }

    pub fn is_prop(&self) -> bool {
        matches!(self, Type::Con(name, args) if name.as_str() == PROP && args.is_empty())
    }

    pub fn as_fun(&self) -> Option<(&Type, &Type)> {
        match self {
            Type::Con(name, args) if name.as_str() == FUN && args.len() == 2 => {
                Some((&args[0], &args[1]))
            }
            _ => None,
        }
    }

    /// Splits `a -> b -> r` into `([a, b], r)`.
    pub fn strip_fun(&self) -> (Vec<&Type>, &Type) {
        let mut doms = Vec::new();
        let mut current = self;
        while let Some((dom, cod)) = current.as_fun() {
            doms.push(dom);
            current = cod;
        }
        (doms, current)
    }

    pub fn type_vars(&self, out: &mut BTreeSet<Name>) {
        match self {
            Type::Var(name) => {
                out.insert(name.clone());
            }
            Type::Con(_, args) => {
                for arg in args {
                    arg.type_vars(out);
                }
            }
        }
    }

    pub fn has_type_vars(&self) -> bool {
        match self {
            Type::Var(_) => true,
            Type::Con(_, args) => args.iter().any(Type::has_type_vars),
        }
    }

    pub fn subst(&self, subst: &TypeSubst) -> Type {
        if subst.is_empty() {
            return self.clone();
        }
        match self {
            Type::Var(name) => subst.get(name).cloned().unwrap_or_else(|| self.clone()),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter().map(|arg| arg.subst(subst)).collect(),
            ),
        }
    }

    /// One-way matching: binds the variables of `pattern` so that
    /// `pattern.subst(subst) == target`. Existing bindings must agree.
    pub fn match_against(pattern: &Type, target: &Type, subst: &mut TypeSubst) -> bool {
        match (pattern, target) {
            (Type::Var(name), _) => match subst.get(name) {
                Some(bound) => bound == target,
                None => {
                    subst.insert(name.clone(), target.clone());
                    true
                }
            },
            (Type::Con(pname, pargs), Type::Con(tname, targs)) => {
                pname == tname
                    && pargs.len() == targs.len()
                    && pargs
                        .iter()
                        .zip(targs)
                        .all(|(p, t)| Type::match_against(p, t, subst))
            }
            _ => false,
        }
    }

    /// True when `self` is an instance of `generic`.
    pub fn is_instance_of(&self, generic: &Type) -> bool {
        let mut subst = TypeSubst::new();
        Type::match_against(generic, self, &mut subst)
    }

    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: u8) -> fmt::Result {
        match self {
            Type::Var(name) => write!(f, "{name}"),
            Type::Con(name, args) => {
                if let Some((dom, cod)) = self.as_fun() {
                    if prec > 0 {
                        f.write_str("(")?;
                    }
                    dom.fmt_prec(f, 1)?;
                    f.write_str(" -> ")?;
                    cod.fmt_prec(f, 0)?;
                    if prec > 0 {
                        f.write_str(")")?;
                    }
                    return Ok(());
                }
                if args.is_empty() {
                    return write!(f, "{name}");
                }
                if prec > 1 {
                    f.write_str("(")?;
                }
                write!(f, "{name}")?;
                for arg in args {
                    f.write_str(" ")?;
                    arg.fmt_prec(f, 2)?;
                }
                if prec > 1 {
                    f.write_str(")")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
    }
}
