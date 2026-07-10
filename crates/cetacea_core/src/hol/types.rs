use std::collections::HashMap;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeParameterId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TypeParameterClass {
    /// May only be instantiated by a first-order data type.
    FirstOrder,
    /// May be instantiated by any simple type, including arrows and `Prop`.
    Any,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeParameter {
    pub id: TypeParameterId,
    pub class: TypeParameterClass,
}

impl TypeParameter {
    pub const fn first_order(id: u32) -> Self {
        Self {
            id: TypeParameterId(id),
            class: TypeParameterClass::FirstOrder,
        }
    }

    pub const fn any(id: u32) -> Self {
        Self {
            id: TypeParameterId(id),
            class: TypeParameterClass::Any,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeConstructorId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CoreType {
    Prop,
    Parameter(TypeParameter),
    Constructor {
        id: TypeConstructorId,
        arguments: Vec<CoreType>,
    },
    Arrow(Box<CoreType>, Box<CoreType>),
    Product(Box<CoreType>, Box<CoreType>),
}

impl CoreType {
    pub fn constructor(id: TypeConstructorId, arguments: Vec<Self>) -> Self {
        Self::Constructor { id, arguments }
    }

    pub fn arrow(domain: Self, codomain: Self) -> Self {
        Self::Arrow(Box::new(domain), Box::new(codomain))
    }

    pub fn product(left: Self, right: Self) -> Self {
        Self::Product(Box::new(left), Box::new(right))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FirstOrderStatus {
    FirstOrder,
    HigherOrder,
}

impl FirstOrderStatus {
    fn combine(self, other: Self) -> Self {
        if self == Self::FirstOrder && other == Self::FirstOrder {
            Self::FirstOrder
        } else {
            Self::HigherOrder
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeError {
    pub message: String,
}

impl TypeError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for TypeError {}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TypeConstructor {
    name: String,
    arity: usize,
    preserves_first_order: bool,
}

/// Resolved type constructors available to the experimental core.
///
/// Names are retained for diagnostics only. Core types refer to constructors by
/// stable IDs, so namespace resolution cannot occur inside the kernel.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypeSignature {
    constructors: Vec<TypeConstructor>,
    names: HashMap<String, TypeConstructorId>,
}

impl TypeSignature {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn declare(
        &mut self,
        name: impl Into<String>,
        arity: usize,
        preserves_first_order: bool,
    ) -> Result<TypeConstructorId, TypeError> {
        let name = name.into();
        if self.names.contains_key(&name) {
            return Err(TypeError::new(format!(
                "type constructor `{name}` is already declared"
            )));
        }
        let raw_id = u32::try_from(self.constructors.len())
            .map_err(|_| TypeError::new("too many type constructors"))?;
        let id = TypeConstructorId(raw_id);
        self.constructors.push(TypeConstructor {
            name: name.clone(),
            arity,
            preserves_first_order,
        });
        self.names.insert(name, id);
        Ok(id)
    }

    pub fn resolve(&self, name: &str) -> Option<TypeConstructorId> {
        self.names.get(name).copied()
    }

    pub fn validate(&self, ty: &CoreType) -> Result<(), TypeError> {
        match ty {
            CoreType::Prop | CoreType::Parameter(_) => Ok(()),
            CoreType::Constructor { id, arguments } => {
                let constructor = self.constructor(*id)?;
                if arguments.len() != constructor.arity {
                    return Err(TypeError::new(format!(
                        "type constructor `{}` expects {} argument(s), but got {}",
                        constructor.name,
                        constructor.arity,
                        arguments.len()
                    )));
                }
                for argument in arguments {
                    self.validate(argument)?;
                }
                Ok(())
            }
            CoreType::Arrow(domain, codomain) | CoreType::Product(domain, codomain) => {
                self.validate(domain)?;
                self.validate(codomain)
            }
        }
    }

    /// Classify whether a type may be used as a first-order quantifier domain.
    ///
    /// `Prop`, arrow types, and unconstrained type parameters are higher-order.
    /// A declared constructor preserves first-orderness only when its
    /// declaration says so and all of its arguments are first-order.
    pub fn first_order_status(&self, ty: &CoreType) -> Result<FirstOrderStatus, TypeError> {
        self.validate(ty)?;
        self.first_order_status_validated(ty)
    }

    fn first_order_status_validated(&self, ty: &CoreType) -> Result<FirstOrderStatus, TypeError> {
        match ty {
            CoreType::Prop | CoreType::Arrow(_, _) => Ok(FirstOrderStatus::HigherOrder),
            CoreType::Parameter(parameter) => Ok(match parameter.class {
                TypeParameterClass::FirstOrder => FirstOrderStatus::FirstOrder,
                TypeParameterClass::Any => FirstOrderStatus::HigherOrder,
            }),
            CoreType::Product(left, right) => Ok(self
                .first_order_status_validated(left)?
                .combine(self.first_order_status_validated(right)?)),
            CoreType::Constructor { id, arguments } => {
                let constructor = self.constructor(*id)?;
                if !constructor.preserves_first_order {
                    return Ok(FirstOrderStatus::HigherOrder);
                }
                let mut status = FirstOrderStatus::FirstOrder;
                for argument in arguments {
                    status = status.combine(self.first_order_status_validated(argument)?);
                }
                Ok(status)
            }
        }
    }

    fn constructor(&self, id: TypeConstructorId) -> Result<&TypeConstructor, TypeError> {
        self.constructors
            .get(id.0 as usize)
            .ok_or_else(|| TypeError::new(format!("unknown type constructor id `{}`", id.0)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn signature() -> (TypeSignature, TypeConstructorId, TypeConstructorId) {
        let mut signature = TypeSignature::new();
        let nat = signature.declare("Nat", 0, true).expect("declare Nat");
        let list = signature.declare("List", 1, true).expect("declare List");
        (signature, nat, list)
    }

    #[test]
    fn resolved_constructors_have_stable_ids_and_checked_arity() {
        let (signature, nat, list) = signature();
        assert_eq!(signature.resolve("Nat"), Some(nat));
        assert_eq!(signature.resolve("List"), Some(list));
        assert_eq!(signature.resolve("Missing"), None);

        let malformed = CoreType::constructor(list, Vec::new());
        let error = signature
            .validate(&malformed)
            .expect_err("List needs an element type");
        assert_eq!(
            error.message,
            "type constructor `List` expects 1 argument(s), but got 0"
        );
    }

    #[test]
    fn duplicate_constructor_names_are_rejected() {
        let mut signature = TypeSignature::new();
        signature.declare("Nat", 0, true).expect("first Nat");
        let error = signature
            .declare("Nat", 0, true)
            .expect_err("duplicate Nat must fail");
        assert_eq!(error.message, "type constructor `Nat` is already declared");
    }

    #[test]
    fn base_and_parameterized_data_types_are_first_order_domains() {
        let (signature, nat, list) = signature();
        let nat = CoreType::constructor(nat, Vec::new());
        let list_nat = CoreType::constructor(list, vec![nat.clone()]);
        assert_eq!(
            signature.first_order_status(&nat),
            Ok(FirstOrderStatus::FirstOrder)
        );
        assert_eq!(
            signature.first_order_status(&list_nat),
            Ok(FirstOrderStatus::FirstOrder)
        );
    }

    #[test]
    fn prop_and_arrow_types_are_higher_order_domains() {
        let (signature, nat, _) = signature();
        let nat = CoreType::constructor(nat, Vec::new());
        let predicate = CoreType::arrow(nat, CoreType::Prop);
        assert_eq!(
            signature.first_order_status(&CoreType::Prop),
            Ok(FirstOrderStatus::HigherOrder)
        );
        assert_eq!(
            signature.first_order_status(&predicate),
            Ok(FirstOrderStatus::HigherOrder)
        );
    }

    #[test]
    fn higher_order_arguments_taint_first_order_preserving_constructors() {
        let (signature, nat, list) = signature();
        let predicate = CoreType::arrow(CoreType::constructor(nat, Vec::new()), CoreType::Prop);
        let list_predicate = CoreType::constructor(list, vec![predicate]);
        assert_eq!(
            signature.first_order_status(&list_predicate),
            Ok(FirstOrderStatus::HigherOrder)
        );
    }

    #[test]
    fn type_parameter_class_controls_conservative_fragment_classification() {
        let (signature, _, _) = signature();
        assert_eq!(
            signature.first_order_status(&CoreType::Parameter(TypeParameter::first_order(0))),
            Ok(FirstOrderStatus::FirstOrder)
        );
        assert_eq!(
            signature.first_order_status(&CoreType::Parameter(TypeParameter::any(0))),
            Ok(FirstOrderStatus::HigherOrder)
        );
    }

    #[test]
    fn non_preserving_type_constructors_are_higher_order() {
        let mut signature = TypeSignature::new();
        let opaque = signature
            .declare("Opaque", 0, false)
            .expect("declare Opaque");
        assert_eq!(
            signature.first_order_status(&CoreType::constructor(opaque, Vec::new())),
            Ok(FirstOrderStatus::HigherOrder)
        );
    }

    #[test]
    fn unknown_constructor_ids_are_rejected() {
        let signature = TypeSignature::new();
        let error = signature
            .validate(&CoreType::constructor(TypeConstructorId(99), Vec::new()))
            .expect_err("unknown constructor must fail");
        assert_eq!(error.message, "unknown type constructor id `99`");
    }
}
