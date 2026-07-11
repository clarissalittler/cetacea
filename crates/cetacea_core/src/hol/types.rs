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
    parameter_classes: Vec<TypeParameterClass>,
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
    legacy_set_constructor: Option<TypeConstructorId>,
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
        self.declare_parameterized(
            name,
            vec![TypeParameterClass::Any; arity],
            preserves_first_order,
        )
    }

    pub fn declare_parameterized(
        &mut self,
        name: impl Into<String>,
        parameter_classes: Vec<TypeParameterClass>,
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
            parameter_classes,
            preserves_first_order,
        });
        self.names.insert(name, id);
        Ok(id)
    }

    /// Declare the distinguished first-order `Set A` wrapper used by the
    /// compatibility language. Its element parameter is restricted to
    /// first-order data, so sets never become an encoding of `A -> Prop`.
    pub fn declare_legacy_set(
        &mut self,
        name: impl Into<String>,
    ) -> Result<TypeConstructorId, TypeError> {
        if self.legacy_set_constructor.is_some() {
            return Err(TypeError::new(
                "the legacy set type constructor is already declared",
            ));
        }
        let mut staged = self.clone();
        let id = staged.declare_parameterized(name, vec![TypeParameterClass::FirstOrder], true)?;
        staged.legacy_set_constructor = Some(id);
        *self = staged;
        Ok(id)
    }

    pub fn legacy_set_constructor(&self) -> Option<TypeConstructorId> {
        self.legacy_set_constructor
    }

    pub fn legacy_set_type(&self, element: CoreType) -> Result<CoreType, TypeError> {
        let constructor = self.legacy_set_constructor.ok_or_else(|| {
            TypeError::new("the legacy set type constructor has not been declared")
        })?;
        let set = CoreType::constructor(constructor, vec![element]);
        self.validate(&set)?;
        Ok(set)
    }

    pub fn legacy_set_element<'a>(
        &self,
        ty: &'a CoreType,
    ) -> Result<Option<&'a CoreType>, TypeError> {
        self.validate(ty)?;
        let Some(set_constructor) = self.legacy_set_constructor else {
            return Ok(None);
        };
        match ty {
            CoreType::Constructor { id, arguments }
                if *id == set_constructor && arguments.len() == 1 =>
            {
                Ok(arguments.first())
            }
            _ => Ok(None),
        }
    }

    pub fn resolve(&self, name: &str) -> Option<TypeConstructorId> {
        self.names.get(name).copied()
    }

    pub fn constructor_arity(&self, id: TypeConstructorId) -> Result<usize, TypeError> {
        Ok(self.constructor(id)?.parameter_classes.len())
    }

    pub fn validate(&self, ty: &CoreType) -> Result<(), TypeError> {
        match ty {
            CoreType::Prop | CoreType::Parameter(_) => Ok(()),
            CoreType::Constructor { id, arguments } => {
                let constructor = self.constructor(*id)?;
                if arguments.len() != constructor.parameter_classes.len() {
                    return Err(TypeError::new(format!(
                        "type constructor `{}` expects {} argument(s), but got {}",
                        constructor.name,
                        constructor.parameter_classes.len(),
                        arguments.len()
                    )));
                }
                for argument in arguments {
                    self.validate(argument)?;
                }
                for (index, (class, argument)) in constructor
                    .parameter_classes
                    .iter()
                    .zip(arguments)
                    .enumerate()
                {
                    if *class == TypeParameterClass::FirstOrder
                        && self.first_order_status_validated(argument)?
                            != FirstOrderStatus::FirstOrder
                    {
                        return Err(TypeError::new(format!(
                            "type argument {index} of constructor `{}` must be first-order, but got `{argument:?}`",
                            constructor.name
                        )));
                    }
                }
                Ok(())
            }
            CoreType::Arrow(domain, codomain) | CoreType::Product(domain, codomain) => {
                self.validate(domain)?;
                self.validate(codomain)
            }
        }
    }

    /// Validate a rank-1 type scheme.
    ///
    /// Every type parameter occurring in the body must be declared by the
    /// scheme, with the same class. Unused parameters are permitted so the
    /// inductive layer can represent phantom parameters without special cases.
    pub fn validate_scheme(
        &self,
        parameters: &[TypeParameter],
        body: &CoreType,
    ) -> Result<(), TypeError> {
        self.validate(body)?;
        let mut declared = HashMap::new();
        for parameter in parameters {
            if declared.insert(parameter.id, parameter.class).is_some() {
                return Err(TypeError::new(format!(
                    "type scheme repeats parameter id `{}`",
                    parameter.id.0
                )));
            }
        }
        validate_scheme_parameters(body, &declared)
    }

    /// Instantiate a checked rank-1 type scheme with explicit type arguments.
    pub fn instantiate_scheme(
        &self,
        parameters: &[TypeParameter],
        body: &CoreType,
        arguments: &[CoreType],
    ) -> Result<CoreType, TypeError> {
        self.validate_scheme(parameters, body)?;
        if parameters.len() != arguments.len() {
            return Err(TypeError::new(format!(
                "type scheme expects {} type argument(s), but got {}",
                parameters.len(),
                arguments.len()
            )));
        }

        let mut substitution = HashMap::new();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            self.validate(argument)?;
            if parameter.class == TypeParameterClass::FirstOrder
                && self.first_order_status(argument)? != FirstOrderStatus::FirstOrder
            {
                return Err(TypeError::new(format!(
                    "type argument `{argument:?}` for parameter `{}` must be first-order",
                    parameter.id.0
                )));
            }
            substitution.insert(parameter.id, argument.clone());
        }
        Ok(substitute_type_parameters(body, &substitution))
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

fn validate_scheme_parameters(
    ty: &CoreType,
    declared: &HashMap<TypeParameterId, TypeParameterClass>,
) -> Result<(), TypeError> {
    match ty {
        CoreType::Prop => Ok(()),
        CoreType::Parameter(parameter) => match declared.get(&parameter.id) {
            Some(class) if *class == parameter.class => Ok(()),
            Some(class) => Err(TypeError::new(format!(
                "type parameter `{}` is used with class `{:?}`, but declared with class `{class:?}`",
                parameter.id.0, parameter.class
            ))),
            None => Err(TypeError::new(format!(
                "type parameter `{}` is not declared by this type scheme",
                parameter.id.0
            ))),
        },
        CoreType::Constructor { arguments, .. } => {
            for argument in arguments {
                validate_scheme_parameters(argument, declared)?;
            }
            Ok(())
        }
        CoreType::Arrow(domain, codomain) | CoreType::Product(domain, codomain) => {
            validate_scheme_parameters(domain, declared)?;
            validate_scheme_parameters(codomain, declared)
        }
    }
}

fn substitute_type_parameters(
    ty: &CoreType,
    substitution: &HashMap<TypeParameterId, CoreType>,
) -> CoreType {
    match ty {
        CoreType::Prop => CoreType::Prop,
        CoreType::Parameter(parameter) => substitution
            .get(&parameter.id)
            .cloned()
            .unwrap_or_else(|| CoreType::Parameter(*parameter)),
        CoreType::Constructor { id, arguments } => CoreType::constructor(
            *id,
            arguments
                .iter()
                .map(|argument| substitute_type_parameters(argument, substitution))
                .collect(),
        ),
        CoreType::Arrow(domain, codomain) => CoreType::arrow(
            substitute_type_parameters(domain, substitution),
            substitute_type_parameters(codomain, substitution),
        ),
        CoreType::Product(left, right) => CoreType::product(
            substitute_type_parameters(left, substitution),
            substitute_type_parameters(right, substitution),
        ),
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

    #[test]
    fn rank_one_schemes_substitute_through_nested_types() {
        let (signature, nat, list) = signature();
        let parameter = TypeParameter::any(7);
        let body = CoreType::arrow(
            CoreType::Parameter(parameter),
            CoreType::constructor(list, vec![CoreType::Parameter(parameter)]),
        );
        let nat = CoreType::constructor(nat, Vec::new());
        assert_eq!(
            signature.instantiate_scheme(&[parameter], &body, std::slice::from_ref(&nat)),
            Ok(CoreType::arrow(
                nat.clone(),
                CoreType::constructor(list, vec![nat])
            ))
        );
    }

    #[test]
    fn rank_one_schemes_reject_free_and_duplicate_parameters() {
        let (signature, _, _) = signature();
        let parameter = TypeParameter::any(3);
        let free_error = signature
            .validate_scheme(&[], &CoreType::Parameter(parameter))
            .expect_err("free parameter must fail");
        assert!(free_error.message.contains("is not declared"));

        let duplicate_error = signature
            .validate_scheme(&[parameter, parameter], &CoreType::Prop)
            .expect_err("duplicate parameter must fail");
        assert!(duplicate_error.message.contains("repeats parameter id"));
    }

    #[test]
    fn first_order_scheme_parameters_reject_higher_order_arguments() {
        let (signature, nat, _) = signature();
        let parameter = TypeParameter::first_order(0);
        let body = CoreType::Parameter(parameter);
        let predicate = CoreType::arrow(CoreType::constructor(nat, Vec::new()), CoreType::Prop);
        let error = signature
            .instantiate_scheme(&[parameter], &body, &[predicate])
            .expect_err("first-order parameter cannot receive a predicate type");
        assert!(error.message.contains("must be first-order"));
    }

    #[test]
    fn scheme_instantiation_checks_type_argument_arity() {
        let (signature, _, _) = signature();
        let parameter = TypeParameter::any(0);
        let error = signature
            .instantiate_scheme(&[parameter], &CoreType::Parameter(parameter), &[])
            .expect_err("missing type argument must fail");
        assert_eq!(
            error.message,
            "type scheme expects 1 type argument(s), but got 0"
        );
    }

    #[test]
    fn type_constructor_parameter_classes_are_enforced_at_every_use() {
        let mut signature = TypeSignature::new();
        let nat = signature.declare("Nat", 0, true).expect("Nat");
        let finite = signature
            .declare_parameterized("Finite", vec![TypeParameterClass::FirstOrder], true)
            .expect("Finite");
        let nat = CoreType::constructor(nat, Vec::new());
        let predicate = CoreType::arrow(nat.clone(), CoreType::Prop);
        assert_eq!(
            signature.validate(&CoreType::constructor(finite, vec![nat])),
            Ok(())
        );
        let error = signature
            .validate(&CoreType::constructor(finite, vec![predicate]))
            .expect_err("first-order constructor parameter cannot be bypassed");
        assert!(error.message.contains("must be first-order"));
    }

    #[test]
    fn legacy_sets_are_first_order_wrappers_not_predicate_types() {
        let (mut signature, nat, _) = signature();
        let set = signature.declare_legacy_set("Set").expect("legacy Set");
        let nat = CoreType::constructor(nat, Vec::new());
        let set_nat = signature.legacy_set_type(nat.clone()).expect("Set Nat");
        assert_eq!(set_nat, CoreType::constructor(set, vec![nat.clone()]));
        assert_eq!(
            signature.first_order_status(&set_nat),
            Ok(FirstOrderStatus::FirstOrder)
        );
        assert_eq!(
            signature
                .legacy_set_element(&set_nat)
                .expect("valid set type"),
            Some(&nat)
        );
        assert_eq!(
            signature.first_order_status(
                &signature
                    .legacy_set_type(set_nat)
                    .expect("sets of sets remain first-order")
            ),
            Ok(FirstOrderStatus::FirstOrder)
        );

        let predicate = CoreType::arrow(nat, CoreType::Prop);
        let rejected = signature
            .legacy_set_type(predicate)
            .expect_err("Set cannot wrap a predicate type");
        assert!(rejected.message.contains("must be first-order"));

        let duplicate = signature
            .declare_legacy_set("OtherSet")
            .expect_err("there is one distinguished compatibility Set");
        assert!(duplicate.message.contains("already declared"));
        assert_eq!(signature.resolve("OtherSet"), None);
    }
}
