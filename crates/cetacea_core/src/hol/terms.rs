use std::collections::HashMap;
use std::fmt;

use super::types::{CoreType, TypeError, TypeSignature};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstantId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CoreTerm {
    /// A de Bruijn index: zero is the nearest enclosing binder.
    Bound(u32),
    Constant(ConstantId),
    Lambda {
        parameter_type: CoreType,
        body: Box<CoreTerm>,
    },
    Apply {
        function: Box<CoreTerm>,
        argument: Box<CoreTerm>,
    },
    Truth,
    Falsity,
    And(Box<CoreTerm>, Box<CoreTerm>),
    Or(Box<CoreTerm>, Box<CoreTerm>),
    Implies(Box<CoreTerm>, Box<CoreTerm>),
    Equality {
        ty: CoreType,
        left: Box<CoreTerm>,
        right: Box<CoreTerm>,
    },
    Forall {
        domain: CoreType,
        body: Box<CoreTerm>,
    },
    Exists {
        domain: CoreType,
        body: Box<CoreTerm>,
    },
}

impl CoreTerm {
    pub fn lambda(parameter_type: CoreType, body: Self) -> Self {
        Self::Lambda {
            parameter_type,
            body: Box::new(body),
        }
    }

    pub fn apply(function: Self, argument: Self) -> Self {
        Self::Apply {
            function: Box::new(function),
            argument: Box::new(argument),
        }
    }

    pub fn and(left: Self, right: Self) -> Self {
        Self::And(Box::new(left), Box::new(right))
    }

    pub fn or(left: Self, right: Self) -> Self {
        Self::Or(Box::new(left), Box::new(right))
    }

    pub fn implies(premise: Self, conclusion: Self) -> Self {
        Self::Implies(Box::new(premise), Box::new(conclusion))
    }

    pub fn equality(ty: CoreType, left: Self, right: Self) -> Self {
        Self::Equality {
            ty,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    pub fn forall(domain: CoreType, body: Self) -> Self {
        Self::Forall {
            domain,
            body: Box::new(body),
        }
    }

    pub fn exists(domain: CoreType, body: Self) -> Self {
        Self::Exists {
            domain,
            body: Box::new(body),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermError {
    pub message: String,
}

impl TermError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for TermError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for TermError {}

impl From<TypeError> for TermError {
    fn from(error: TypeError) -> Self {
        Self::new(error.message)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Constant {
    name: String,
    ty: CoreType,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TermSignature {
    constants: Vec<Constant>,
    names: HashMap<String, ConstantId>,
}

impl TermSignature {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn declare(
        &mut self,
        types: &TypeSignature,
        name: impl Into<String>,
        ty: CoreType,
    ) -> Result<ConstantId, TermError> {
        types.validate(&ty)?;
        let name = name.into();
        if self.names.contains_key(&name) {
            return Err(TermError::new(format!(
                "constant `{name}` is already declared"
            )));
        }
        let raw_id = u32::try_from(self.constants.len())
            .map_err(|_| TermError::new("too many constants"))?;
        let id = ConstantId(raw_id);
        self.constants.push(Constant {
            name: name.clone(),
            ty,
        });
        self.names.insert(name, id);
        Ok(id)
    }

    pub fn resolve(&self, name: &str) -> Option<ConstantId> {
        self.names.get(name).copied()
    }

    fn constant(&self, id: ConstantId) -> Result<&Constant, TermError> {
        self.constants
            .get(id.0 as usize)
            .ok_or_else(|| TermError::new(format!("unknown constant id `{}`", id.0)))
    }
}

/// Types of surrounding binders, nearest binder first.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TermContext {
    bound: Vec<CoreType>,
}

impl TermContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_bound(mut self, ty: CoreType) -> Self {
        self.bound.insert(0, ty);
        self
    }

    fn lookup(&self, index: u32) -> Result<&CoreType, TermError> {
        self.bound.get(index as usize).ok_or_else(|| {
            TermError::new(format!(
                "unbound de Bruijn index `{index}` in context of depth {}",
                self.bound.len()
            ))
        })
    }
}

pub fn infer_type(
    types: &TypeSignature,
    constants: &TermSignature,
    context: &TermContext,
    term: &CoreTerm,
) -> Result<CoreType, TermError> {
    match term {
        CoreTerm::Bound(index) => Ok(context.lookup(*index)?.clone()),
        CoreTerm::Constant(id) => Ok(constants.constant(*id)?.ty.clone()),
        CoreTerm::Lambda {
            parameter_type,
            body,
        } => {
            types.validate(parameter_type)?;
            let body_context = context.clone().with_bound(parameter_type.clone());
            let body_type = infer_type(types, constants, &body_context, body)?;
            Ok(CoreType::arrow(parameter_type.clone(), body_type))
        }
        CoreTerm::Apply { function, argument } => {
            let function_type = infer_type(types, constants, context, function)?;
            let argument_type = infer_type(types, constants, context, argument)?;
            let CoreType::Arrow(domain, codomain) = function_type else {
                return Err(TermError::new(format!(
                    "application expects a function, but the function position has type `{function_type:?}`"
                )));
            };
            if *domain != argument_type {
                return Err(TermError::new(format!(
                    "application argument has type `{argument_type:?}`, but expected `{domain:?}`"
                )));
            }
            Ok(*codomain)
        }
        CoreTerm::Truth | CoreTerm::Falsity => Ok(CoreType::Prop),
        CoreTerm::And(left, right) | CoreTerm::Or(left, right) | CoreTerm::Implies(left, right) => {
            expect_prop(types, constants, context, left, "left operand")?;
            expect_prop(types, constants, context, right, "right operand")?;
            Ok(CoreType::Prop)
        }
        CoreTerm::Equality { ty, left, right } => {
            types.validate(ty)?;
            let left_type = infer_type(types, constants, context, left)?;
            let right_type = infer_type(types, constants, context, right)?;
            if left_type != *ty || right_type != *ty {
                return Err(TermError::new(format!(
                    "equality at type `{ty:?}` has operand types `{left_type:?}` and `{right_type:?}`"
                )));
            }
            Ok(CoreType::Prop)
        }
        CoreTerm::Forall { domain, body } | CoreTerm::Exists { domain, body } => {
            types.validate(domain)?;
            let body_context = context.clone().with_bound(domain.clone());
            expect_prop(types, constants, &body_context, body, "quantifier body")?;
            Ok(CoreType::Prop)
        }
    }
}

fn expect_prop(
    types: &TypeSignature,
    constants: &TermSignature,
    context: &TermContext,
    term: &CoreTerm,
    role: &str,
) -> Result<(), TermError> {
    let actual = infer_type(types, constants, context, term)?;
    if actual == CoreType::Prop {
        Ok(())
    } else {
        Err(TermError::new(format!(
            "{role} must have type `Prop`, but has type `{actual:?}`"
        )))
    }
}

/// Normalize a well-typed simply typed term by beta reduction.
///
/// Type checking occurs first, so untyped self-application cannot turn this
/// total operation into general evaluation.
pub fn normalize(
    types: &TypeSignature,
    constants: &TermSignature,
    context: &TermContext,
    term: &CoreTerm,
) -> Result<CoreTerm, TermError> {
    infer_type(types, constants, context, term)?;
    normalize_typed(term)
}

pub fn definitionally_equal(
    types: &TypeSignature,
    constants: &TermSignature,
    context: &TermContext,
    left: &CoreTerm,
    right: &CoreTerm,
) -> Result<bool, TermError> {
    let left_type = infer_type(types, constants, context, left)?;
    let right_type = infer_type(types, constants, context, right)?;
    if left_type != right_type {
        return Ok(false);
    }
    Ok(normalize_typed(left)? == normalize_typed(right)?)
}

pub fn instantiate_binder(
    types: &TypeSignature,
    constants: &TermSignature,
    context: &TermContext,
    domain: &CoreType,
    body: &CoreTerm,
    argument: &CoreTerm,
) -> Result<CoreTerm, TermError> {
    types.validate(domain)?;
    let argument_type = infer_type(types, constants, context, argument)?;
    if argument_type != *domain {
        return Err(TermError::new(format!(
            "binder argument has type `{argument_type:?}`, but expected `{domain:?}`"
        )));
    }
    let body_context = context.clone().with_bound(domain.clone());
    expect_prop(types, constants, &body_context, body, "binder body")?;
    let instantiated = substitute_top(argument, body)?;
    expect_prop(
        types,
        constants,
        context,
        &instantiated,
        "instantiated body",
    )?;
    Ok(instantiated)
}

fn normalize_typed(term: &CoreTerm) -> Result<CoreTerm, TermError> {
    match term {
        CoreTerm::Bound(_) | CoreTerm::Constant(_) | CoreTerm::Truth | CoreTerm::Falsity => {
            Ok(term.clone())
        }
        CoreTerm::Lambda {
            parameter_type,
            body,
        } => Ok(CoreTerm::lambda(
            parameter_type.clone(),
            normalize_typed(body)?,
        )),
        CoreTerm::Apply { function, argument } => {
            let function = normalize_typed(function)?;
            let argument = normalize_typed(argument)?;
            if let CoreTerm::Lambda { body, .. } = function {
                normalize_typed(&substitute_top(&argument, &body)?)
            } else {
                Ok(CoreTerm::apply(function, argument))
            }
        }
        CoreTerm::And(left, right) => Ok(CoreTerm::and(
            normalize_typed(left)?,
            normalize_typed(right)?,
        )),
        CoreTerm::Or(left, right) => Ok(CoreTerm::or(
            normalize_typed(left)?,
            normalize_typed(right)?,
        )),
        CoreTerm::Implies(premise, conclusion) => Ok(CoreTerm::implies(
            normalize_typed(premise)?,
            normalize_typed(conclusion)?,
        )),
        CoreTerm::Equality { ty, left, right } => Ok(CoreTerm::equality(
            ty.clone(),
            normalize_typed(left)?,
            normalize_typed(right)?,
        )),
        CoreTerm::Forall { domain, body } => {
            Ok(CoreTerm::forall(domain.clone(), normalize_typed(body)?))
        }
        CoreTerm::Exists { domain, body } => {
            Ok(CoreTerm::exists(domain.clone(), normalize_typed(body)?))
        }
    }
}

fn substitute_top(argument: &CoreTerm, body: &CoreTerm) -> Result<CoreTerm, TermError> {
    let lifted_argument = shift(argument, 1, 0)?;
    let substituted = substitute(body, 0, &lifted_argument)?;
    shift(&substituted, -1, 0)
}

fn substitute(term: &CoreTerm, target: u32, replacement: &CoreTerm) -> Result<CoreTerm, TermError> {
    match term {
        CoreTerm::Bound(index) if *index == target => Ok(replacement.clone()),
        CoreTerm::Bound(_) | CoreTerm::Constant(_) | CoreTerm::Truth | CoreTerm::Falsity => {
            Ok(term.clone())
        }
        CoreTerm::Lambda {
            parameter_type,
            body,
        } => Ok(CoreTerm::lambda(
            parameter_type.clone(),
            substitute(body, target + 1, &shift(replacement, 1, 0)?)?,
        )),
        CoreTerm::Apply { function, argument } => Ok(CoreTerm::apply(
            substitute(function, target, replacement)?,
            substitute(argument, target, replacement)?,
        )),
        CoreTerm::And(left, right) => Ok(CoreTerm::and(
            substitute(left, target, replacement)?,
            substitute(right, target, replacement)?,
        )),
        CoreTerm::Or(left, right) => Ok(CoreTerm::or(
            substitute(left, target, replacement)?,
            substitute(right, target, replacement)?,
        )),
        CoreTerm::Implies(premise, conclusion) => Ok(CoreTerm::implies(
            substitute(premise, target, replacement)?,
            substitute(conclusion, target, replacement)?,
        )),
        CoreTerm::Equality { ty, left, right } => Ok(CoreTerm::equality(
            ty.clone(),
            substitute(left, target, replacement)?,
            substitute(right, target, replacement)?,
        )),
        CoreTerm::Forall { domain, body } => Ok(CoreTerm::forall(
            domain.clone(),
            substitute(body, target + 1, &shift(replacement, 1, 0)?)?,
        )),
        CoreTerm::Exists { domain, body } => Ok(CoreTerm::exists(
            domain.clone(),
            substitute(body, target + 1, &shift(replacement, 1, 0)?)?,
        )),
    }
}

fn shift(term: &CoreTerm, amount: i32, cutoff: u32) -> Result<CoreTerm, TermError> {
    match term {
        CoreTerm::Bound(index) if *index >= cutoff => {
            let shifted = i64::from(*index) + i64::from(amount);
            if shifted < 0 || shifted > i64::from(u32::MAX) {
                return Err(TermError::new("invalid de Bruijn index shift"));
            }
            Ok(CoreTerm::Bound(shifted as u32))
        }
        CoreTerm::Bound(_) | CoreTerm::Constant(_) | CoreTerm::Truth | CoreTerm::Falsity => {
            Ok(term.clone())
        }
        CoreTerm::Lambda {
            parameter_type,
            body,
        } => Ok(CoreTerm::lambda(
            parameter_type.clone(),
            shift(body, amount, cutoff + 1)?,
        )),
        CoreTerm::Apply { function, argument } => Ok(CoreTerm::apply(
            shift(function, amount, cutoff)?,
            shift(argument, amount, cutoff)?,
        )),
        CoreTerm::And(left, right) => Ok(CoreTerm::and(
            shift(left, amount, cutoff)?,
            shift(right, amount, cutoff)?,
        )),
        CoreTerm::Or(left, right) => Ok(CoreTerm::or(
            shift(left, amount, cutoff)?,
            shift(right, amount, cutoff)?,
        )),
        CoreTerm::Implies(premise, conclusion) => Ok(CoreTerm::implies(
            shift(premise, amount, cutoff)?,
            shift(conclusion, amount, cutoff)?,
        )),
        CoreTerm::Equality { ty, left, right } => Ok(CoreTerm::equality(
            ty.clone(),
            shift(left, amount, cutoff)?,
            shift(right, amount, cutoff)?,
        )),
        CoreTerm::Forall { domain, body } => Ok(CoreTerm::forall(
            domain.clone(),
            shift(body, amount, cutoff + 1)?,
        )),
        CoreTerm::Exists { domain, body } => Ok(CoreTerm::exists(
            domain.clone(),
            shift(body, amount, cutoff + 1)?,
        )),
    }
}

pub(super) fn shift_under_new_binder(term: &CoreTerm) -> Result<CoreTerm, TermError> {
    shift(term, 1, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::types::TypeConstructorId;

    fn signatures() -> (TypeSignature, TermSignature, CoreType, ConstantId) {
        let mut types = TypeSignature::new();
        let nat_id = types.declare("Nat", 0, true).expect("declare Nat");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let mut terms = TermSignature::new();
        let zero = terms
            .declare(&types, "zero", nat.clone())
            .expect("declare zero");
        (types, terms, nat, zero)
    }

    #[test]
    fn identity_lambda_has_an_arrow_type() {
        let (types, terms, nat, _) = signatures();
        let identity = CoreTerm::lambda(nat.clone(), CoreTerm::Bound(0));
        assert_eq!(
            infer_type(&types, &terms, &TermContext::new(), &identity),
            Ok(CoreType::arrow(nat.clone(), nat))
        );
    }

    #[test]
    fn beta_reduction_is_definitionally_equal_to_its_argument() {
        let (types, terms, nat, zero) = signatures();
        let identity = CoreTerm::lambda(nat, CoreTerm::Bound(0));
        let application = CoreTerm::apply(identity, CoreTerm::Constant(zero));
        assert_eq!(
            normalize(&types, &terms, &TermContext::new(), &application),
            Ok(CoreTerm::Constant(zero))
        );
        assert_eq!(
            definitionally_equal(
                &types,
                &terms,
                &TermContext::new(),
                &application,
                &CoreTerm::Constant(zero),
            ),
            Ok(true)
        );
    }

    #[test]
    fn beta_reduction_avoids_capture_under_nested_lambdas() {
        let (types, terms, nat, _) = signatures();
        // In a context containing y : Nat, reduce
        //   (fun x => fun z => x) y
        // to
        //   fun z => y.
        // Inside the result lambda, y is index 1 rather than the bound z at 0.
        let context = TermContext::new().with_bound(nat.clone());
        let function = CoreTerm::lambda(
            nat.clone(),
            CoreTerm::lambda(nat.clone(), CoreTerm::Bound(1)),
        );
        let application = CoreTerm::apply(function, CoreTerm::Bound(0));
        assert_eq!(
            normalize(&types, &terms, &context, &application),
            Ok(CoreTerm::lambda(nat, CoreTerm::Bound(1)))
        );
    }

    #[test]
    fn bad_application_argument_types_are_rejected() {
        let (types, terms, nat, _) = signatures();
        let predicate = CoreTerm::lambda(
            nat,
            CoreTerm::Constant(terms.resolve("zero").expect("zero exists")),
        );
        let application = CoreTerm::apply(
            predicate,
            CoreTerm::lambda(CoreType::Prop, CoreTerm::Bound(0)),
        );
        let error = infer_type(&types, &terms, &TermContext::new(), &application)
            .expect_err("argument type mismatch must fail");
        assert!(error.message.contains("application argument has type"));
    }

    #[test]
    fn applying_a_non_function_is_rejected() {
        let (types, terms, _, zero) = signatures();
        let application = CoreTerm::apply(CoreTerm::Constant(zero), CoreTerm::Constant(zero));
        let error = infer_type(&types, &terms, &TermContext::new(), &application)
            .expect_err("zero is not a function");
        assert!(error.message.contains("application expects a function"));
    }

    #[test]
    fn malformed_bound_indices_are_rejected_before_normalization() {
        let (types, terms, _, _) = signatures();
        let error = normalize(&types, &terms, &TermContext::new(), &CoreTerm::Bound(0))
            .expect_err("free de Bruijn index must fail");
        assert_eq!(
            error.message,
            "unbound de Bruijn index `0` in context of depth 0"
        );
    }

    #[test]
    fn unknown_constants_are_rejected() {
        let (types, terms, _, _) = signatures();
        let error = infer_type(
            &types,
            &terms,
            &TermContext::new(),
            &CoreTerm::Constant(ConstantId(99)),
        )
        .expect_err("unknown constant must fail");
        assert_eq!(error.message, "unknown constant id `99`");
    }

    #[test]
    fn duplicate_constant_names_are_rejected() {
        let (types, mut terms, nat, _) = signatures();
        let error = terms
            .declare(&types, "zero", nat)
            .expect_err("duplicate zero must fail");
        assert_eq!(error.message, "constant `zero` is already declared");
    }

    #[test]
    fn malformed_constant_types_are_rejected_at_declaration() {
        let types = TypeSignature::new();
        let mut terms = TermSignature::new();
        let error = terms
            .declare(
                &types,
                "bad",
                CoreType::constructor(TypeConstructorId(44), Vec::new()),
            )
            .expect_err("unknown type constructor must fail");
        assert_eq!(error.message, "unknown type constructor id `44`");
    }

    #[test]
    fn normalization_is_idempotent_for_typed_terms() {
        let (types, terms, nat, zero) = signatures();
        let nested = CoreTerm::apply(
            CoreTerm::lambda(nat, CoreTerm::Bound(0)),
            CoreTerm::Constant(zero),
        );
        let once = normalize(&types, &terms, &TermContext::new(), &nested).expect("normalize once");
        let twice = normalize(&types, &terms, &TermContext::new(), &once).expect("normalize twice");
        assert_eq!(once, twice);
    }

    #[test]
    fn logical_forms_have_type_prop() {
        let (types, terms, nat, zero) = signatures();
        let equality = CoreTerm::equality(
            nat.clone(),
            CoreTerm::Constant(zero),
            CoreTerm::Constant(zero),
        );
        let proposition = CoreTerm::forall(
            nat,
            CoreTerm::implies(equality.clone(), CoreTerm::or(equality, CoreTerm::Falsity)),
        );
        assert_eq!(
            infer_type(&types, &terms, &TermContext::new(), &proposition),
            Ok(CoreType::Prop)
        );
    }

    #[test]
    fn logical_connectives_reject_data_operands() {
        let (types, terms, _, zero) = signatures();
        let malformed = CoreTerm::and(CoreTerm::Truth, CoreTerm::Constant(zero));
        let error = infer_type(&types, &terms, &TermContext::new(), &malformed)
            .expect_err("and needs propositions");
        assert!(error
            .message
            .contains("right operand must have type `Prop`"));
    }

    #[test]
    fn typed_equality_rejects_mismatched_operands() {
        let (types, terms, nat, zero) = signatures();
        let malformed = CoreTerm::equality(
            nat,
            CoreTerm::Constant(zero),
            CoreTerm::lambda(CoreType::Prop, CoreTerm::Bound(0)),
        );
        let error = infer_type(&types, &terms, &TermContext::new(), &malformed)
            .expect_err("equality operands must match its type");
        assert!(error.message.contains("equality at type"));
    }

    #[test]
    fn quantifiers_reject_non_propositional_bodies() {
        let (types, terms, nat, _) = signatures();
        let malformed = CoreTerm::forall(nat, CoreTerm::Bound(0));
        let error = infer_type(&types, &terms, &TermContext::new(), &malformed)
            .expect_err("forall body must be a proposition");
        assert!(error
            .message
            .contains("quantifier body must have type `Prop`"));
    }

    #[test]
    fn binder_instantiation_substitutes_without_capture() {
        let (types, terms, nat, _) = signatures();
        // forall x, forall y, x = y; instantiate x with an outer variable z.
        let context = TermContext::new().with_bound(nat.clone());
        let body = CoreTerm::forall(
            nat.clone(),
            CoreTerm::equality(nat.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
        );
        let instantiated =
            instantiate_binder(&types, &terms, &context, &nat, &body, &CoreTerm::Bound(0))
                .expect("instantiate outer forall");
        assert_eq!(
            instantiated,
            CoreTerm::forall(
                nat.clone(),
                CoreTerm::equality(nat, CoreTerm::Bound(1), CoreTerm::Bound(0))
            )
        );
    }

    #[test]
    fn binder_instantiation_checks_argument_type() {
        let (types, terms, nat, _) = signatures();
        let error = instantiate_binder(
            &types,
            &terms,
            &TermContext::new(),
            &nat,
            &CoreTerm::Truth,
            &CoreTerm::Truth,
        )
        .expect_err("Prop is not a Nat witness");
        assert!(error.message.contains("binder argument has type"));
    }
}
