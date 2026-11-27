//! The signature: declared type constructors with arities and declared
//! constants with generic types.

use std::collections::BTreeMap;

use crate::error::{bail, Result};
use crate::name::Name;
use crate::types::{Type, FUN, PROP, SET};

#[derive(Clone, Debug, Default)]
pub struct Signature {
    types: BTreeMap<Name, usize>,
    consts: BTreeMap<Name, Type>,
}

impl Signature {
    pub(crate) fn empty() -> Signature {
        Signature::default()
    }

    pub fn type_arity(&self, name: &Name) -> Option<usize> {
        self.types.get(name).copied()
    }

    pub fn has_type(&self, name: &Name) -> bool {
        self.types.contains_key(name)
    }

    pub fn const_type(&self, name: &Name) -> Option<&Type> {
        self.consts.get(name)
    }

    pub fn has_const(&self, name: &Name) -> bool {
        self.consts.contains_key(name)
    }

    pub fn types(&self) -> impl Iterator<Item = (&Name, usize)> {
        self.types.iter().map(|(name, arity)| (name, *arity))
    }

    pub fn consts(&self) -> impl Iterator<Item = (&Name, &Type)> {
        self.consts.iter()
    }

    pub(crate) fn add_type(&mut self, name: Name, arity: usize) -> Result<()> {
        if self.types.contains_key(&name) {
            bail!("new_type", "type `{name}` is already declared");
        }
        self.types.insert(name, arity);
        Ok(())
    }

    pub(crate) fn add_const(&mut self, name: Name, ty: Type) -> Result<()> {
        if self.consts.contains_key(&name) {
            bail!("new_const", "constant `{name}` is already declared");
        }
        self.check_type(&ty)?;
        self.consts.insert(name, ty);
        Ok(())
    }

    /// A type is well formed when every constructor it mentions is
    /// declared with the arity it is used at.
    pub fn check_type(&self, ty: &Type) -> Result<()> {
        match ty {
            Type::Var(_) => Ok(()),
            Type::Con(name, args) => {
                match self.types.get(name) {
                    None => bail!("check_type", "unknown type constructor `{name}`"),
                    Some(arity) if *arity != args.len() => bail!(
                        "check_type",
                        "type constructor `{name}` takes {arity} argument(s), but it was applied to {}",
                        args.len()
                    ),
                    Some(_) => {}
                }
                for arg in args {
                    self.check_type(arg)?;
                }
                Ok(())
            }
        }
    }

    pub(crate) fn check_const_instance(&self, name: &Name, ty: &Type) -> Result<()> {
        let Some(generic) = self.consts.get(name) else {
            bail!("constant", "unknown constant `{name}`");
        };
        self.check_type(ty)?;
        if !ty.is_instance_of(generic) {
            bail!(
                "constant",
                "type `{ty}` is not an instance of the declared type `{generic}` of `{name}`"
            );
        }
        Ok(())
    }
}

pub(crate) fn base_signature() -> Signature {
    let mut sig = Signature::empty();
    sig.add_type(Name::new(PROP), 0).expect("fresh");
    sig.add_type(Name::new(FUN), 2).expect("fresh");
    sig.add_type(Name::new(SET), 1).expect("fresh");
    sig
}
