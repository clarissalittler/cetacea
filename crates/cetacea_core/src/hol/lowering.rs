//! Parser-independent lowering from the legacy AST to resolved HOL core terms.
//!
//! This module intentionally starts below imports, declarations, tactics, and
//! source diagnostics. Callers supply already resolved symbol descriptors;
//! lowering then inserts explicit rank-one type applications, converts local
//! names to de Bruijn indices, and checks every produced core term immediately.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::{Formula, LambdaParam, Term, Type};

use super::prelude::CompatibilityPrelude;
use super::terms::{infer_type, ConstantId, CoreTerm, TermContext, TermError, TermSignature};
use super::types::{
    CoreType, FirstOrderStatus, TypeConstructorId, TypeError, TypeParameter, TypeParameterClass,
    TypeParameterId, TypeSignature,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoweringError {
    pub message: String,
}

impl LoweringError {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for LoweringError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for LoweringError {}

impl From<TypeError> for LoweringError {
    fn from(error: TypeError) -> Self {
        Self::new(error.message)
    }
}

impl From<TermError> for LoweringError {
    fn from(error: TermError) -> Self {
        Self::new(error.message)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CompatibilitySymbol {
    constant: ConstantId,
    type_parameters: Vec<TypeParameter>,
    /// One entry per surface argument. An entry may itself be an arrow type
    /// when the corresponding legacy parameter is a predicate schema.
    parameter_types: Vec<CoreType>,
    result_type: CoreType,
}

impl CompatibilitySymbol {
    fn full_type(&self) -> CoreType {
        self.parameter_types
            .iter()
            .rev()
            .fold(self.result_type.clone(), |result, parameter| {
                CoreType::arrow(parameter.clone(), result)
            })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LocalBinding {
    name: String,
    ty: CoreType,
    parameter_types: Vec<CoreType>,
    result_type: CoreType,
}

/// A checked compatibility-lowering scope.
///
/// The object borrows immutable kernel signatures. Declaration lowering will
/// create a fresh scope after each transactional signature update, so no core
/// IDs can become stale while an AST is being lowered.
#[derive(Clone)]
pub struct CompatibilityLowerer<'a> {
    types: &'a TypeSignature,
    constants: &'a TermSignature,
    prelude: &'a CompatibilityPrelude,
    type_constructors: HashMap<String, TypeConstructorId>,
    type_parameters: HashMap<String, TypeParameter>,
    symbols: HashMap<String, CompatibilitySymbol>,
    bindings: Vec<LocalBinding>,
}

impl<'a> CompatibilityLowerer<'a> {
    pub fn new(
        types: &'a TypeSignature,
        constants: &'a TermSignature,
        prelude: &'a CompatibilityPrelude,
    ) -> Result<Self, LoweringError> {
        let mut lowerer = Self {
            types,
            constants,
            prelude,
            type_constructors: HashMap::new(),
            type_parameters: HashMap::new(),
            symbols: HashMap::new(),
            bindings: Vec::new(),
        };
        lowerer.validate_prelude()?;
        lowerer.register_symbol(
            "le",
            prelude.less_equal(),
            Vec::new(),
            vec![prelude.nat_type(), prelude.nat_type()],
            CoreType::Prop,
        )?;
        Ok(lowerer)
    }

    pub fn register_type_constructor(
        &mut self,
        name: impl Into<String>,
        constructor: TypeConstructorId,
    ) -> Result<(), LoweringError> {
        let name = name.into();
        self.types.constructor_arity(constructor)?;
        if self.type_constructors.contains_key(&name) || self.type_parameters.contains_key(&name) {
            return Err(LoweringError::new(format!(
                "compatibility type name `{name}` is already registered"
            )));
        }
        self.type_constructors.insert(name, constructor);
        Ok(())
    }

    /// Register one already-declared global surface symbol.
    ///
    /// `parameter_types` records surface arity, which cannot in general be
    /// recovered by splitting the curried core type: a predicate-schema
    /// parameter has an arrow type but is still one legacy argument.
    pub fn register_symbol(
        &mut self,
        name: impl Into<String>,
        constant: ConstantId,
        type_parameters: Vec<TypeParameter>,
        parameter_types: Vec<CoreType>,
        result_type: CoreType,
    ) -> Result<(), LoweringError> {
        let name = name.into();
        if self.symbols.contains_key(&name) {
            return Err(LoweringError::new(format!(
                "compatibility symbol `{name}` is already registered"
            )));
        }
        let symbol = CompatibilitySymbol {
            constant,
            type_parameters,
            parameter_types,
            result_type,
        };
        self.types
            .validate_scheme(&symbol.type_parameters, &symbol.full_type())?;
        let schematic_arguments = symbol
            .type_parameters
            .iter()
            .copied()
            .map(CoreType::Parameter)
            .collect::<Vec<_>>();
        let head = CoreTerm::instantiate_constant(constant, schematic_arguments);
        let actual = infer_type(self.types, self.constants, &TermContext::new(), &head)?;
        let expected = symbol.full_type();
        if actual != expected {
            return Err(LoweringError::new(format!(
                "compatibility symbol `{name}` describes type `{expected:?}`, but core constant `{}` has type `{actual:?}`",
                constant.0
            )));
        }
        self.symbols.insert(name, symbol);
        Ok(())
    }

    /// Add a legacy `(A : Type)` schema parameter.
    ///
    /// Legacy type parameters range only over first-order data types. Accepting
    /// an unrestricted parameter here would let a surface schema smuggle an
    /// arrow or `Prop` into a nominally FOL declaration.
    pub fn bind_type_parameter(
        &mut self,
        name: impl Into<String>,
        parameter: TypeParameter,
    ) -> Result<(), LoweringError> {
        let name = name.into();
        if parameter.class != TypeParameterClass::FirstOrder {
            return Err(LoweringError::new(format!(
                "legacy type parameter `{name}` must be first-order"
            )));
        }
        if self.type_constructors.contains_key(&name) {
            return Err(LoweringError::new(format!(
                "legacy type parameter `{name}` conflicts with a registered type constructor"
            )));
        }
        if self
            .type_parameters
            .insert(name.clone(), parameter)
            .is_some()
        {
            return Err(LoweringError::new(format!(
                "legacy type parameter `{name}` is repeated"
            )));
        }
        Ok(())
    }

    pub fn bind_term_parameter(
        &mut self,
        name: impl Into<String>,
        ty: CoreType,
    ) -> Result<(), LoweringError> {
        self.require_first_order_type(&ty, "legacy term parameter")?;
        self.bind_root(LocalBinding {
            name: name.into(),
            ty: ty.clone(),
            parameter_types: Vec::new(),
            result_type: ty,
        })
    }

    pub fn bind_proposition_parameter(
        &mut self,
        name: impl Into<String>,
    ) -> Result<(), LoweringError> {
        self.bind_root(LocalBinding {
            name: name.into(),
            ty: CoreType::Prop,
            parameter_types: Vec::new(),
            result_type: CoreType::Prop,
        })
    }

    pub fn bind_predicate_parameter(
        &mut self,
        name: impl Into<String>,
        domains: Vec<CoreType>,
    ) -> Result<(), LoweringError> {
        for domain in &domains {
            self.require_first_order_type(domain, "legacy predicate domain")?;
        }
        let ty = domains.iter().rev().fold(CoreType::Prop, |result, domain| {
            CoreType::arrow(domain.clone(), result)
        });
        self.bind_root(LocalBinding {
            name: name.into(),
            ty,
            parameter_types: domains,
            result_type: CoreType::Prop,
        })
    }

    pub fn lower_type(&self, ty: &Type) -> Result<CoreType, LoweringError> {
        let lowered = match ty {
            Type::Nat => self.prelude.nat_type(),
            Type::Named(name) => {
                if let Some(parameter) = self.type_parameters.get(name) {
                    CoreType::Parameter(*parameter)
                } else {
                    let constructor = self
                        .type_constructors
                        .get(name)
                        .copied()
                        .or_else(|| self.types.resolve(name))
                        .ok_or_else(|| {
                            LoweringError::new(format!("unknown compatibility type `{name}`"))
                        })?;
                    CoreType::constructor(constructor, Vec::new())
                }
            }
            Type::App(name, arguments) => {
                if self.type_parameters.contains_key(name) {
                    return Err(LoweringError::new(format!(
                        "rank-one type parameter `{name}` cannot be applied to type arguments"
                    )));
                }
                let constructor = self
                    .type_constructors
                    .get(name)
                    .copied()
                    .or_else(|| self.types.resolve(name))
                    .ok_or_else(|| {
                        LoweringError::new(format!(
                            "unknown compatibility type constructor `{name}`"
                        ))
                    })?;
                CoreType::constructor(
                    constructor,
                    arguments
                        .iter()
                        .map(|argument| self.lower_type(argument))
                        .collect::<Result<Vec<_>, _>>()?,
                )
            }
            Type::Prod(left, right) => {
                CoreType::product(self.lower_type(left)?, self.lower_type(right)?)
            }
            Type::Set(element) => self.types.legacy_set_type(self.lower_type(element)?)?,
        };
        self.types.validate(&lowered)?;
        Ok(lowered)
    }

    /// Lower a legacy first-order term.
    pub fn lower_term(&mut self, term: &Term) -> Result<CoreTerm, LoweringError> {
        let lowered = self.lower_term_raw(term, None)?;
        let ty = self.infer(&lowered)?;
        self.require_first_order_type(&ty, "legacy term")?;
        Ok(lowered)
    }

    /// Lower a term already accepted by the legacy proof checker without
    /// imposing the compatibility facade's declaration-wide FOL restriction.
    ///
    /// This is used only for proof evidence such as reflexivity over an
    /// imported rank-one HOL instance. The HOL kernel still checks the term,
    /// and receipt classification remains responsible for exposing a
    /// higher-order instance.
    pub(crate) fn lower_proof_term(&mut self, term: &Term) -> Result<CoreTerm, LoweringError> {
        self.lower_term_raw(term, None).map_err(|error| {
            LoweringError::new(format!(
                "{} while lowering proof term `{term}`",
                error.message
            ))
        })
    }

    /// Lower a term in a schema position with an explicit expected type.
    /// This is the entry point used for proposition arguments, named predicate
    /// arguments, and predicate lambdas.
    pub fn lower_term_at_type(
        &mut self,
        term: &Term,
        expected: &CoreType,
    ) -> Result<CoreTerm, LoweringError> {
        self.types.validate(expected)?;
        self.lower_term_raw(term, Some(expected))
    }

    pub fn lower_formula(&mut self, formula: &Formula) -> Result<CoreTerm, LoweringError> {
        self.lower_formula_with_term_policy(formula, true)
    }

    /// Lower a formula already accepted as proof evidence. Imported generic
    /// HOL theorems may introduce intermediate equalities over an unrestricted
    /// rank-one parameter even when the surrounding source declaration uses
    /// the compatibility facade.
    pub(crate) fn lower_proof_formula(
        &mut self,
        formula: &Formula,
    ) -> Result<CoreTerm, LoweringError> {
        self.lower_formula_with_term_policy(formula, false)
    }

    fn lower_formula_with_term_policy(
        &mut self,
        formula: &Formula,
        require_first_order_terms: bool,
    ) -> Result<CoreTerm, LoweringError> {
        let lowered = match formula {
            Formula::True => CoreTerm::Truth,
            Formula::False => CoreTerm::Falsity,
            Formula::Atom(name) => {
                self.lower_named_application(name, &[], Some(&CoreType::Prop))?
            }
            Formula::PredApp(name, arguments) => {
                self.lower_named_application(name, arguments, Some(&CoreType::Prop))?
            }
            Formula::Eq(left, right) => {
                let (left, right) = if matches!(right, Term::Ascribed { .. })
                    && !matches!(left, Term::Ascribed { .. })
                {
                    let right = self.lower_formula_term(right, None, require_first_order_terms)?;
                    let right_type = self.infer(&right)?;
                    let left = self.lower_formula_term(
                        left,
                        Some(&right_type),
                        require_first_order_terms,
                    )?;
                    (left, right)
                } else {
                    let left = self.lower_formula_term(left, None, require_first_order_terms)?;
                    let left_type = self.infer(&left)?;
                    let right = self.lower_formula_term(
                        right,
                        Some(&left_type),
                        require_first_order_terms,
                    )?;
                    (left, right)
                };
                let left_type = self.infer(&left)?;
                let right_type = self.infer(&right)?;
                if left_type != right_type {
                    return Err(LoweringError::new(format!(
                        "legacy equality compares core types `{left_type:?}` and `{right_type:?}`"
                    )));
                }
                CoreTerm::equality(left_type, left, right)
            }
            Formula::In(element, set) => {
                let element = if require_first_order_terms {
                    self.lower_term(element)?
                } else {
                    self.lower_proof_term(element)?
                };
                let set = if require_first_order_terms {
                    self.lower_term(set)?
                } else {
                    self.lower_proof_term(set)?
                };
                let element_type = self.infer(&element)?;
                let set_type = self.infer(&set)?;
                let expected = self
                    .types
                    .legacy_set_element(&set_type)?
                    .cloned()
                    .ok_or_else(|| {
                        LoweringError::new(format!(
                            "right side of legacy membership has core type `{set_type:?}`, not a set"
                        ))
                    })?;
                if element_type != expected {
                    return Err(LoweringError::new(format!(
                        "legacy membership has element type `{element_type:?}`, but the set contains `{expected:?}`"
                    )));
                }
                CoreTerm::membership(element_type, element, set)
            }
            Formula::Subset(left, right) => {
                let left = if require_first_order_terms {
                    self.lower_term(left)?
                } else {
                    self.lower_proof_term(left)?
                };
                let right = if require_first_order_terms {
                    self.lower_term(right)?
                } else {
                    self.lower_proof_term(right)?
                };
                let left_element = self.set_element_type(&left, "left subset argument")?;
                let right_element = self.set_element_type(&right, "right subset argument")?;
                if left_element != right_element {
                    return Err(LoweringError::new(format!(
                        "legacy subset compares element types `{left_element:?}` and `{right_element:?}`"
                    )));
                }
                CoreTerm::subset(left_element, left, right)
            }
            Formula::And(left, right) => CoreTerm::and(
                self.lower_formula_with_term_policy(left, require_first_order_terms)?,
                self.lower_formula_with_term_policy(right, require_first_order_terms)?,
            ),
            Formula::Or(left, right) => CoreTerm::or(
                self.lower_formula_with_term_policy(left, require_first_order_terms)?,
                self.lower_formula_with_term_policy(right, require_first_order_terms)?,
            ),
            Formula::Implies(premise, conclusion) => CoreTerm::implies(
                self.lower_formula_with_term_policy(premise, require_first_order_terms)?,
                self.lower_formula_with_term_policy(conclusion, require_first_order_terms)?,
            ),
            Formula::Forall {
                var,
                var_type,
                body,
            } => {
                let domain = self.lower_type(var_type)?;
                if require_first_order_terms {
                    self.require_first_order_type(&domain, "legacy universal domain")?;
                }
                let body = self.lower_under_term_binder(var, domain.clone(), |lowerer| {
                    lowerer.lower_formula_with_term_policy(body, require_first_order_terms)
                })?;
                CoreTerm::forall(domain, body)
            }
            Formula::Exists {
                var,
                var_type,
                body,
            } => {
                let domain = self.lower_type(var_type)?;
                if require_first_order_terms {
                    self.require_first_order_type(&domain, "legacy existential domain")?;
                }
                let body = self.lower_under_term_binder(var, domain.clone(), |lowerer| {
                    lowerer.lower_formula_with_term_policy(body, require_first_order_terms)
                })?;
                CoreTerm::exists(domain, body)
            }
        };
        let actual = self.infer(&lowered)?;
        if actual != CoreType::Prop {
            return Err(LoweringError::new(format!(
                "lowered legacy formula has core type `{actual:?}`, not `Prop`"
            )));
        }
        Ok(lowered)
    }

    fn lower_formula_term(
        &mut self,
        term: &Term,
        expected: Option<&CoreType>,
        require_first_order: bool,
    ) -> Result<CoreTerm, LoweringError> {
        let lowered = self.lower_term_raw(term, expected).map_err(|error| {
            LoweringError::new(format!(
                "{} while lowering formula term `{term}`",
                error.message
            ))
        })?;
        if require_first_order {
            let ty = self.infer(&lowered)?;
            self.require_first_order_type(&ty, "legacy term")?;
        }
        Ok(lowered)
    }

    fn lower_term_raw(
        &mut self,
        term: &Term,
        expected: Option<&CoreType>,
    ) -> Result<CoreTerm, LoweringError> {
        let lowered = match term {
            Term::Var(name) => self.lower_named_value(name, expected)?,
            Term::App(name, arguments) => {
                self.lower_named_application(name, arguments, expected)?
            }
            Term::Ascribed { term, ty } => {
                let ascribed_type = self.lower_type(ty)?;
                if let Some(expected) = expected {
                    if *expected != ascribed_type {
                        return Err(LoweringError::new(format!(
                            "term ascription has core type `{ascribed_type:?}`, but the context expects `{expected:?}`"
                        )));
                    }
                }
                self.lower_term_raw(term, Some(&ascribed_type))?
            }
            Term::PredLambda { params, body } => {
                let expected = expected.ok_or_else(|| {
                    LoweringError::new(
                        "predicate lambda needs an expected predicate type during HOL lowering",
                    )
                })?;
                self.lower_predicate_lambda(params, body, expected)?
            }
            Term::Zero => CoreTerm::Constant(self.prelude.zero()),
            Term::Succ(argument) => CoreTerm::apply(
                CoreTerm::Constant(self.prelude.successor()),
                self.lower_term_raw(argument, Some(&self.prelude.nat_type()))?,
            ),
            Term::Add(left, right) => self.lower_builtin_binary(
                self.prelude.addition(),
                left,
                right,
                &self.prelude.nat_type(),
            )?,
            Term::Mul(left, right) => self.lower_builtin_binary(
                self.prelude.multiplication(),
                left,
                right,
                &self.prelude.nat_type(),
            )?,
            Term::Sub(left, right) => self.lower_builtin_binary(
                self.prelude.subtraction(),
                left,
                right,
                &self.prelude.nat_type(),
            )?,
            Term::Pair(left, right) => CoreTerm::pair(
                self.lower_term_raw(left, None)?,
                self.lower_term_raw(right, None)?,
            ),
            Term::Fst(pair) => CoreTerm::first(self.lower_term_raw(pair, None)?),
            Term::Snd(pair) => CoreTerm::second(self.lower_term_raw(pair, None)?),
            Term::EmptySet(element_type) => CoreTerm::empty_set(self.lower_type(element_type)?),
            Term::Universe(element_type) => CoreTerm::universe_set(self.lower_type(element_type)?),
            Term::Singleton(element) => {
                CoreTerm::singleton_set(self.lower_term_raw(element, None)?)
            }
            Term::Union(left, right) => CoreTerm::set_union(
                self.lower_term_raw(left, None)?,
                self.lower_term_raw(right, None)?,
            ),
            Term::Inter(left, right) => CoreTerm::set_intersection(
                self.lower_term_raw(left, None)?,
                self.lower_term_raw(right, None)?,
            ),
            Term::Diff(left, right) => CoreTerm::set_difference(
                self.lower_term_raw(left, None)?,
                self.lower_term_raw(right, None)?,
            ),
            Term::Complement(set) => CoreTerm::set_complement(self.lower_term_raw(set, None)?),
            Term::CartProd(left, right) => CoreTerm::set_product(
                self.lower_term_raw(left, None)?,
                self.lower_term_raw(right, None)?,
            ),
            Term::Powerset(set) => {
                let set = self.lower_term_raw(set, None)?;
                let element_type = self.set_element_type(&set, "powerset argument")?;
                CoreTerm::powerset(element_type, set)
            }
            Term::SetBuilder {
                var,
                var_type,
                body,
            } => {
                let element_type = self.lower_type(var_type)?;
                self.require_first_order_type(&element_type, "legacy set-builder domain")?;
                let body = self.lower_under_term_binder(var, element_type.clone(), |lowerer| {
                    lowerer.lower_formula(body)
                })?;
                CoreTerm::set_builder(element_type, body)
            }
        };
        let actual = self.infer(&lowered)?;
        if let Some(expected) = expected {
            if actual != *expected {
                return Err(LoweringError::new(format!(
                    "lowered legacy term has core type `{actual:?}`, but expected `{expected:?}`"
                )));
            }
        }
        Ok(lowered)
    }

    fn lower_builtin_binary(
        &mut self,
        function: ConstantId,
        left: &Term,
        right: &Term,
        argument_type: &CoreType,
    ) -> Result<CoreTerm, LoweringError> {
        Ok(CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::Constant(function),
                self.lower_term_raw(left, Some(argument_type))?,
            ),
            self.lower_term_raw(right, Some(argument_type))?,
        ))
    }

    fn lower_predicate_lambda(
        &mut self,
        params: &[LambdaParam],
        body: &Formula,
        expected: &CoreType,
    ) -> Result<CoreTerm, LoweringError> {
        let (domains, result) = split_surface_arguments(expected, params.len()).ok_or_else(|| {
            LoweringError::new(format!(
                "predicate lambda with {} parameter(s) does not match expected core type `{expected:?}`",
                params.len()
            ))
        })?;
        if result != CoreType::Prop {
            return Err(LoweringError::new(format!(
                "predicate lambda must return `Prop`, but expected result is `{result:?}`"
            )));
        }
        let mut seen = HashSet::new();
        for (parameter, domain) in params.iter().zip(&domains) {
            if !seen.insert(parameter.name.as_str()) {
                return Err(LoweringError::new(format!(
                    "predicate lambda parameter `{}` is repeated",
                    parameter.name
                )));
            }
            self.require_first_order_type(domain, "predicate lambda domain")?;
            if let Some(annotation) = &parameter.ty {
                let annotation = self.lower_type(annotation)?;
                if annotation != *domain {
                    return Err(LoweringError::new(format!(
                        "predicate lambda parameter `{}` has core type `{annotation:?}`, but expected `{domain:?}`",
                        parameter.name
                    )));
                }
            }
        }

        let original_depth = self.bindings.len();
        for (parameter, domain) in params.iter().zip(&domains) {
            self.bindings.push(LocalBinding {
                name: parameter.name.clone(),
                ty: domain.clone(),
                parameter_types: Vec::new(),
                result_type: domain.clone(),
            });
        }
        let body_result = self.lower_formula(body);
        self.bindings.truncate(original_depth);
        let mut lowered = body_result?;
        for domain in domains.into_iter().rev() {
            lowered = CoreTerm::lambda(domain, lowered);
        }
        Ok(lowered)
    }

    fn lower_named_value(
        &mut self,
        name: &str,
        expected: Option<&CoreType>,
    ) -> Result<CoreTerm, LoweringError> {
        if let Some((index, binding)) = self.resolve_binding(name) {
            let binding = binding.clone();
            if !binding.parameter_types.is_empty() && expected != Some(&binding.ty) {
                return Err(LoweringError::new(format!(
                    "predicate symbol `{name}` needs its expected full type when passed as an argument"
                )));
            }
            if let Some(expected) = expected {
                if binding.ty != *expected {
                    return Err(LoweringError::new(format!(
                        "local symbol `{name}` has core type `{:?}`, but expected `{expected:?}`",
                        binding.ty
                    )));
                }
            }
            return Ok(CoreTerm::Bound(index));
        }
        let symbol = self.symbols.get(name).cloned().ok_or_else(|| {
            LoweringError::new(format!("unknown compatibility term or symbol `{name}`"))
        })?;
        if !symbol.parameter_types.is_empty() && expected.is_none() {
            return Err(LoweringError::new(format!(
                "global symbol `{name}` cannot be partially applied as a legacy first-order term"
            )));
        }
        let expected_full = expected.or_else(|| {
            symbol
                .parameter_types
                .is_empty()
                .then_some(&symbol.result_type)
        });
        let type_arguments = self.infer_symbol_types(&symbol, &[], expected_full, true)?;
        let value = CoreTerm::instantiate_constant(symbol.constant, type_arguments);
        let actual = self.infer(&value)?;
        if let Some(expected) = expected {
            if actual != *expected {
                return Err(LoweringError::new(format!(
                    "global symbol `{name}` has instantiated type `{actual:?}`, but expected `{expected:?}`"
                )));
            }
        }
        Ok(value)
    }

    fn lower_named_application(
        &mut self,
        name: &str,
        arguments: &[Term],
        expected_result: Option<&CoreType>,
    ) -> Result<CoreTerm, LoweringError> {
        if let Some((index, binding)) = self.resolve_binding(name) {
            let binding = binding.clone();
            if binding.parameter_types.len() != arguments.len() {
                return Err(LoweringError::new(format!(
                    "local symbol `{name}` expects {} argument(s), but got {}",
                    binding.parameter_types.len(),
                    arguments.len()
                )));
            }
            if let Some(expected) = expected_result {
                if binding.result_type != *expected {
                    return Err(LoweringError::new(format!(
                        "local symbol `{name}` returns `{:?}`, but expected `{expected:?}`",
                        binding.result_type
                    )));
                }
            }
            let mut application = CoreTerm::Bound(index);
            for (argument, parameter_type) in arguments.iter().zip(&binding.parameter_types) {
                application = CoreTerm::apply(
                    application,
                    self.lower_term_raw(argument, Some(parameter_type))?,
                );
            }
            self.infer(&application)?;
            return Ok(application);
        }

        let symbol = self.symbols.get(name).cloned().ok_or_else(|| {
            LoweringError::new(format!(
                "unknown compatibility function or predicate `{name}`"
            ))
        })?;
        if symbol.parameter_types.len() != arguments.len() {
            return Err(LoweringError::new(format!(
                "global symbol `{name}` expects {} argument(s), but got {}",
                symbol.parameter_types.len(),
                arguments.len()
            )));
        }

        let type_arguments = self.infer_symbol_types(&symbol, arguments, expected_result, false)?;
        let parameter_types = symbol
            .parameter_types
            .iter()
            .map(|parameter| {
                self.types
                    .instantiate_scheme(&symbol.type_parameters, parameter, &type_arguments)
                    .map_err(Into::into)
            })
            .collect::<Result<Vec<_>, LoweringError>>()?;
        let result_type = self.types.instantiate_scheme(
            &symbol.type_parameters,
            &symbol.result_type,
            &type_arguments,
        )?;
        if let Some(expected) = expected_result {
            if result_type != *expected {
                return Err(LoweringError::new(format!(
                    "global symbol `{name}` returns `{result_type:?}`, but expected `{expected:?}`"
                )));
            }
        }
        let mut application = CoreTerm::instantiate_constant(symbol.constant, type_arguments);
        for (argument, parameter_type) in arguments.iter().zip(&parameter_types) {
            application = CoreTerm::apply(
                application,
                self.lower_term_raw(argument, Some(parameter_type))?,
            );
        }
        let actual = self.infer(&application)?;
        if actual != result_type {
            return Err(LoweringError::new(format!(
                "lowered application of `{name}` has core type `{actual:?}`, but its instantiated declaration returns `{result_type:?}`"
            )));
        }
        Ok(application)
    }

    fn infer_symbol_types(
        &mut self,
        symbol: &CompatibilitySymbol,
        arguments: &[Term],
        expected: Option<&CoreType>,
        expected_is_full_type: bool,
    ) -> Result<Vec<CoreType>, LoweringError> {
        let declared = symbol
            .type_parameters
            .iter()
            .map(|parameter| (parameter.id, *parameter))
            .collect::<HashMap<_, _>>();
        let mut substitution = HashMap::new();
        if let Some(expected) = expected {
            let pattern = if expected_is_full_type {
                symbol.full_type()
            } else {
                symbol.result_type.clone()
            };
            self.unify_type_scheme(&pattern, expected, &declared, &mut substitution)?;
        }
        if !expected_is_full_type {
            for (argument, pattern) in arguments.iter().zip(&symbol.parameter_types) {
                if let Some(actual) = self.argument_type_hint(argument)? {
                    self.unify_type_scheme(pattern, &actual, &declared, &mut substitution)?;
                }
            }
        }

        symbol
            .type_parameters
            .iter()
            .map(|parameter| {
                substitution.get(&parameter.id).cloned().ok_or_else(|| {
                    LoweringError::new(format!(
                        "cannot infer compatibility type argument `{}` for core constant `{}`",
                        parameter.id.0, symbol.constant.0
                    ))
                })
            })
            .collect()
    }

    fn argument_type_hint(&mut self, argument: &Term) -> Result<Option<CoreType>, LoweringError> {
        match argument {
            Term::PredLambda { params, .. } => {
                let mut domains = Vec::with_capacity(params.len());
                for parameter in params {
                    let Some(annotation) = &parameter.ty else {
                        return Ok(None);
                    };
                    domains.push(self.lower_type(annotation)?);
                }
                Ok(Some(
                    domains
                        .into_iter()
                        .rev()
                        .fold(CoreType::Prop, |result, domain| {
                            CoreType::arrow(domain, result)
                        }),
                ))
            }
            Term::Var(name) => {
                if let Some((index, binding)) = self.resolve_binding(name) {
                    let value = CoreTerm::Bound(index);
                    let actual = self.infer(&value)?;
                    debug_assert_eq!(actual, binding.ty);
                    return Ok(Some(actual));
                }
                let Some(symbol) = self.symbols.get(name).cloned() else {
                    return Err(LoweringError::new(format!(
                        "unknown compatibility term or symbol `{name}`"
                    )));
                };
                if symbol.type_parameters.is_empty() {
                    Ok(Some(symbol.full_type()))
                } else {
                    Ok(None)
                }
            }
            _ => {
                // A nested polymorphic application can be ambiguous in
                // isolation while an enclosing symbol still determines its
                // expected type. Defer only that inference failure; the
                // application is lowered again at the instantiated parameter
                // type once the enclosing symbol has been resolved.
                let lowered = match self.lower_term_raw(argument, None) {
                    Ok(lowered) => lowered,
                    Err(error)
                        if error
                            .message
                            .contains("cannot infer compatibility type argument") =>
                    {
                        return Ok(None);
                    }
                    Err(error) => return Err(error),
                };
                Ok(Some(self.infer(&lowered)?))
            }
        }
    }

    fn unify_type_scheme(
        &self,
        pattern: &CoreType,
        actual: &CoreType,
        declared: &HashMap<TypeParameterId, TypeParameter>,
        substitution: &mut HashMap<TypeParameterId, CoreType>,
    ) -> Result<(), LoweringError> {
        self.types.validate(actual)?;
        match pattern {
            CoreType::Parameter(parameter) if declared.get(&parameter.id) == Some(parameter) => {
                if parameter.class == TypeParameterClass::FirstOrder
                    && self.types.first_order_status(actual)? != FirstOrderStatus::FirstOrder
                {
                    return Err(LoweringError::new(format!(
                        "compatibility type parameter `{}` requires first-order data, but inferred `{actual:?}`",
                        parameter.id.0
                    )));
                }
                if let Some(previous) = substitution.get(&parameter.id) {
                    if previous != actual {
                        return Err(LoweringError::new(format!(
                            "compatibility type parameter `{}` is inferred as both `{previous:?}` and `{actual:?}`",
                            parameter.id.0
                        )));
                    }
                } else {
                    substitution.insert(parameter.id, actual.clone());
                }
                Ok(())
            }
            CoreType::Prop if actual == &CoreType::Prop => Ok(()),
            CoreType::Parameter(_) if pattern == actual => Ok(()),
            CoreType::Constructor {
                id: pattern_id,
                arguments: pattern_arguments,
            } => {
                let CoreType::Constructor {
                    id: actual_id,
                    arguments: actual_arguments,
                } = actual
                else {
                    return Err(type_mismatch(pattern, actual));
                };
                if pattern_id != actual_id || pattern_arguments.len() != actual_arguments.len() {
                    return Err(type_mismatch(pattern, actual));
                }
                for (pattern, actual) in pattern_arguments.iter().zip(actual_arguments) {
                    self.unify_type_scheme(pattern, actual, declared, substitution)?;
                }
                Ok(())
            }
            CoreType::Arrow(pattern_domain, pattern_result) => {
                let CoreType::Arrow(actual_domain, actual_result) = actual else {
                    return Err(type_mismatch(pattern, actual));
                };
                self.unify_type_scheme(pattern_domain, actual_domain, declared, substitution)?;
                self.unify_type_scheme(pattern_result, actual_result, declared, substitution)
            }
            CoreType::Product(pattern_left, pattern_right) => {
                let CoreType::Product(actual_left, actual_right) = actual else {
                    return Err(type_mismatch(pattern, actual));
                };
                self.unify_type_scheme(pattern_left, actual_left, declared, substitution)?;
                self.unify_type_scheme(pattern_right, actual_right, declared, substitution)
            }
            _ => Err(type_mismatch(pattern, actual)),
        }
    }

    fn lower_under_term_binder<T>(
        &mut self,
        name: &str,
        ty: CoreType,
        lower: impl FnOnce(&mut Self) -> Result<T, LoweringError>,
    ) -> Result<T, LoweringError> {
        let original_depth = self.bindings.len();
        self.bindings.push(LocalBinding {
            name: name.to_string(),
            ty: ty.clone(),
            parameter_types: Vec::new(),
            result_type: ty,
        });
        let result = lower(self);
        self.bindings.truncate(original_depth);
        result
    }

    fn bind_root(&mut self, binding: LocalBinding) -> Result<(), LoweringError> {
        if self
            .bindings
            .iter()
            .any(|existing| existing.name == binding.name)
        {
            return Err(LoweringError::new(format!(
                "legacy schema parameter `{}` is repeated",
                binding.name
            )));
        }
        self.types.validate(&binding.ty)?;
        self.bindings.push(binding);
        Ok(())
    }

    fn resolve_binding(&self, name: &str) -> Option<(u32, &LocalBinding)> {
        self.bindings
            .iter()
            .rev()
            .enumerate()
            .find(|(_, binding)| binding.name == name)
            .and_then(|(index, binding)| u32::try_from(index).ok().map(|index| (index, binding)))
    }

    fn context(&self) -> TermContext {
        self.bindings
            .iter()
            .fold(TermContext::new(), |context, binding| {
                context.with_bound(binding.ty.clone())
            })
    }

    pub(crate) fn core_context(&self) -> TermContext {
        self.context()
    }

    pub(crate) fn infer_core(&self, term: &CoreTerm) -> Result<CoreType, LoweringError> {
        self.infer(term)
    }

    pub(crate) fn resolve_local_term(&self, name: &str) -> Option<(u32, CoreType)> {
        self.resolve_binding(name)
            .map(|(index, binding)| (index, binding.ty.clone()))
    }

    fn infer(&self, term: &CoreTerm) -> Result<CoreType, LoweringError> {
        Ok(infer_type(
            self.types,
            self.constants,
            &self.context(),
            term,
        )?)
    }

    fn set_element_type(&self, term: &CoreTerm, role: &str) -> Result<CoreType, LoweringError> {
        let ty = self.infer(term)?;
        self.types
            .legacy_set_element(&ty)?
            .cloned()
            .ok_or_else(|| LoweringError::new(format!("{role} has core type `{ty:?}`, not a set")))
    }

    fn require_first_order_type(&self, ty: &CoreType, role: &str) -> Result<(), LoweringError> {
        if self.types.first_order_status(ty)? == FirstOrderStatus::FirstOrder {
            Ok(())
        } else {
            Err(LoweringError::new(format!(
                "{role} must have a first-order data type, but has `{ty:?}`"
            )))
        }
    }

    fn validate_prelude(&self) -> Result<(), LoweringError> {
        if self.types.resolve("Nat") != Some(self.prelude.nat_constructor()) {
            return Err(LoweringError::new(
                "compatibility prelude Nat ID does not belong to this type signature",
            ));
        }
        if self.types.legacy_set_constructor() != Some(self.prelude.set_constructor()) {
            return Err(LoweringError::new(
                "compatibility prelude Set ID does not belong to this type signature",
            ));
        }
        let nat = self.prelude.nat_type();
        let expected = [
            (self.prelude.zero(), nat.clone()),
            (
                self.prelude.successor(),
                CoreType::arrow(nat.clone(), nat.clone()),
            ),
            (
                self.prelude.addition(),
                CoreType::arrow(nat.clone(), CoreType::arrow(nat.clone(), nat.clone())),
            ),
            (
                self.prelude.multiplication(),
                CoreType::arrow(nat.clone(), CoreType::arrow(nat.clone(), nat.clone())),
            ),
            (
                self.prelude.subtraction(),
                CoreType::arrow(nat.clone(), CoreType::arrow(nat.clone(), nat.clone())),
            ),
            (
                self.prelude.less_equal(),
                CoreType::arrow(nat.clone(), CoreType::arrow(nat, CoreType::Prop)),
            ),
        ];
        for (constant, expected) in expected {
            let actual = infer_type(
                self.types,
                self.constants,
                &TermContext::new(),
                &CoreTerm::Constant(constant),
            )?;
            if actual != expected {
                return Err(LoweringError::new(format!(
                    "compatibility prelude constant `{}` has type `{actual:?}`, but expected `{expected:?}`",
                    constant.0
                )));
            }
        }
        Ok(())
    }
}

fn split_surface_arguments(ty: &CoreType, count: usize) -> Option<(Vec<CoreType>, CoreType)> {
    let mut domains = Vec::with_capacity(count);
    let mut current = ty;
    for _ in 0..count {
        let CoreType::Arrow(domain, result) = current else {
            return None;
        };
        domains.push((**domain).clone());
        current = result;
    }
    Some((domains, current.clone()))
}

fn type_mismatch(pattern: &CoreType, actual: &CoreType) -> LoweringError {
    LoweringError::new(format!(
        "cannot match compatibility type scheme `{pattern:?}` with `{actual:?}`"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::library::ListLibrary;
    use crate::hol::prelude::CompatibilityPrelude;
    use crate::hol::spike::SpikeElaborator;

    struct Fixture {
        elaborator: SpikeElaborator,
        prelude: CompatibilityPrelude,
        person: CoreType,
        alice: ConstantId,
        next: ConstantId,
        likes: ConstantId,
        atom: ConstantId,
        accepts_predicate: ConstantId,
    }

    impl Fixture {
        fn new() -> Self {
            let mut elaborator = SpikeElaborator::new();
            let prelude = CompatibilityPrelude::install(&mut elaborator).expect("prelude");
            let person_id = elaborator
                .declare_base_type("Person", true)
                .expect("Person");
            let person = CoreType::constructor(person_id, Vec::new());
            let nat = prelude.nat_type();
            let alice = elaborator
                .declare_constant("alice", person.clone())
                .expect("alice");
            let next = elaborator
                .declare_constant("next", CoreType::arrow(nat.clone(), nat.clone()))
                .expect("next");
            let likes = elaborator
                .declare_constant(
                    "Likes",
                    CoreType::arrow(
                        person.clone(),
                        CoreType::arrow(person.clone(), CoreType::Prop),
                    ),
                )
                .expect("Likes");
            let atom = elaborator.declare_constant("P", CoreType::Prop).expect("P");
            let predicate = CoreType::arrow(nat.clone(), CoreType::Prop);
            let accepts_predicate = elaborator
                .declare_constant(
                    "AcceptsPredicate",
                    CoreType::arrow(predicate, CoreType::arrow(nat.clone(), CoreType::Prop)),
                )
                .expect("AcceptsPredicate");
            Self {
                elaborator,
                prelude,
                person,
                alice,
                next,
                likes,
                atom,
                accepts_predicate,
            }
        }

        fn lowerer(&self) -> CompatibilityLowerer<'_> {
            let mut lowerer = CompatibilityLowerer::new(
                self.elaborator.types(),
                self.elaborator.constants(),
                &self.prelude,
            )
            .expect("lowerer");
            let nat = self.prelude.nat_type();
            lowerer
                .register_symbol(
                    "alice",
                    self.alice,
                    Vec::new(),
                    Vec::new(),
                    self.person.clone(),
                )
                .expect("register alice");
            lowerer
                .register_symbol(
                    "next",
                    self.next,
                    Vec::new(),
                    vec![nat.clone()],
                    nat.clone(),
                )
                .expect("register next");
            lowerer
                .register_symbol(
                    "Likes",
                    self.likes,
                    Vec::new(),
                    vec![self.person.clone(), self.person.clone()],
                    CoreType::Prop,
                )
                .expect("register Likes");
            lowerer
                .register_symbol("P", self.atom, Vec::new(), Vec::new(), CoreType::Prop)
                .expect("register P");
            lowerer
                .register_symbol(
                    "AcceptsPredicate",
                    self.accepts_predicate,
                    Vec::new(),
                    vec![CoreType::arrow(nat.clone(), CoreType::Prop), nat],
                    CoreType::Prop,
                )
                .expect("register predicate consumer");
            lowerer
        }
    }

    fn var(name: &str) -> Term {
        Term::Var(name.to_string())
    }

    fn zero() -> Term {
        Term::Zero
    }

    fn singleton_zero() -> Term {
        Term::Singleton(Box::new(zero()))
    }

    #[test]
    fn lowers_every_legacy_type_form() {
        let fixture = Fixture::new();
        let mut lowerer = fixture.lowerer();
        let parameter = TypeParameter::first_order(700);
        lowerer
            .bind_type_parameter("A", parameter)
            .expect("type parameter");
        let nat = fixture.prelude.nat_type();
        assert_eq!(lowerer.lower_type(&Type::Nat), Ok(nat.clone()));
        assert_eq!(
            lowerer.lower_type(&Type::Named("Person".to_string())),
            Ok(fixture.person.clone())
        );
        assert_eq!(
            lowerer.lower_type(&Type::Named("A".to_string())),
            Ok(CoreType::Parameter(parameter))
        );
        assert_eq!(
            lowerer.lower_type(&Type::Prod(
                Box::new(Type::Nat),
                Box::new(Type::Named("Person".to_string())),
            )),
            Ok(CoreType::product(nat.clone(), fixture.person.clone()))
        );
        assert_eq!(
            lowerer.lower_type(&Type::Set(Box::new(Type::Nat))),
            fixture
                .elaborator
                .types()
                .legacy_set_type(nat)
                .map_err(Into::into)
        );
    }

    #[test]
    fn lowers_explicit_rank_one_type_constructor_applications() {
        let mut elaborator = SpikeElaborator::new();
        let prelude = CompatibilityPrelude::install(&mut elaborator).expect("prelude");
        let lists = ListLibrary::install(&mut elaborator).expect("generic List");
        let mut lowerer =
            CompatibilityLowerer::new(elaborator.types(), elaborator.constants(), &prelude)
                .expect("lowerer");
        let nat = prelude.nat_type();
        assert_eq!(
            lowerer.lower_type(&Type::App("List".to_string(), vec![Type::Nat])),
            Ok(lists.list_type(nat.clone()))
        );
        let parameter = TypeParameter::first_order(701);
        lowerer
            .bind_type_parameter("A", parameter)
            .expect("type parameter");
        let parameter_error = lowerer
            .lower_type(&Type::App("A".to_string(), vec![Type::Nat]))
            .expect_err("rank-one parameters are not higher-kinded");
        assert!(parameter_error.message.contains("cannot be applied"));
        let arity_error = lowerer
            .lower_type(&Type::App("Nat".to_string(), vec![Type::Nat]))
            .expect_err("monomorphic constructors reject arguments");
        assert!(arity_error.message.contains("expects 0 argument"));
    }

    #[test]
    fn lowers_every_first_order_term_form() {
        let fixture = Fixture::new();
        let mut lowerer = fixture.lowerer();
        lowerer
            .bind_term_parameter("n", fixture.prelude.nat_type())
            .expect("n");

        let terms = vec![
            var("n"),
            Term::App("next".to_string(), vec![var("n")]),
            zero(),
            Term::Succ(Box::new(zero())),
            Term::Add(Box::new(zero()), Box::new(zero())),
            Term::Mul(Box::new(zero()), Box::new(zero())),
            Term::Sub(Box::new(zero()), Box::new(zero())),
            Term::Pair(Box::new(zero()), Box::new(var("alice"))),
            Term::Fst(Box::new(Term::Pair(
                Box::new(zero()),
                Box::new(var("alice")),
            ))),
            Term::Snd(Box::new(Term::Pair(
                Box::new(zero()),
                Box::new(var("alice")),
            ))),
            Term::EmptySet(Type::Nat),
            Term::Universe(Type::Nat),
            singleton_zero(),
            Term::Union(Box::new(singleton_zero()), Box::new(singleton_zero())),
            Term::Inter(Box::new(singleton_zero()), Box::new(singleton_zero())),
            Term::Diff(Box::new(singleton_zero()), Box::new(singleton_zero())),
            Term::Complement(Box::new(singleton_zero())),
            Term::CartProd(
                Box::new(singleton_zero()),
                Box::new(Term::Singleton(Box::new(var("alice")))),
            ),
            Term::Powerset(Box::new(singleton_zero())),
            Term::SetBuilder {
                var: "x".to_string(),
                var_type: Type::Nat,
                body: Box::new(Formula::Eq(var("x"), var("n"))),
            },
        ];
        for term in terms {
            let lowered = lowerer
                .lower_term(&term)
                .unwrap_or_else(|error| panic!("failed to lower `{term}`: {error}"));
            assert_eq!(
                fixture
                    .elaborator
                    .types()
                    .first_order_status(&lowerer.infer(&lowered).expect("lowered type")),
                Ok(FirstOrderStatus::FirstOrder),
                "`{term}` must remain first-order"
            );
        }
    }

    #[test]
    fn lowers_predicate_lambdas_with_expected_types_and_de_bruijn_scope() {
        let fixture = Fixture::new();
        let mut lowerer = fixture.lowerer();
        let nat = fixture.prelude.nat_type();
        let lambda = Term::PredLambda {
            params: vec![LambdaParam {
                name: "x".to_string(),
                ty: None,
            }],
            body: Box::new(Formula::Eq(var("x"), zero())),
        };
        let formula = Formula::PredApp(
            "AcceptsPredicate".to_string(),
            vec![lambda.clone(), Term::Succ(Box::new(zero()))],
        );
        let lowered = lowerer
            .lower_formula(&formula)
            .expect("predicate application");
        assert_eq!(lowerer.infer(&lowered), Ok(CoreType::Prop));

        let predicate = lowerer
            .lower_term_at_type(&lambda, &CoreType::arrow(nat.clone(), CoreType::Prop))
            .expect("expected type guides omitted annotation");
        assert_eq!(
            predicate,
            CoreTerm::lambda(
                nat.clone(),
                CoreTerm::equality(
                    nat,
                    CoreTerm::Bound(0),
                    CoreTerm::Constant(fixture.prelude.zero()),
                ),
            )
        );
        assert!(lowerer.lower_term(&lambda).is_err());
    }

    #[test]
    fn lowers_every_formula_form_and_preserves_shadowing() {
        let fixture = Fixture::new();
        let mut lowerer = fixture.lowerer();
        let formulas = vec![
            Formula::True,
            Formula::False,
            Formula::Atom("P".to_string()),
            Formula::PredApp("Likes".to_string(), vec![var("alice"), var("alice")]),
            Formula::Eq(zero(), zero()),
            Formula::In(zero(), singleton_zero()),
            Formula::Subset(singleton_zero(), Term::Universe(Type::Nat)),
            Formula::And(Box::new(Formula::True), Box::new(Formula::False)),
            Formula::Or(Box::new(Formula::True), Box::new(Formula::False)),
            Formula::Implies(Box::new(Formula::True), Box::new(Formula::False)),
            Formula::Forall {
                var: "x".to_string(),
                var_type: Type::Nat,
                body: Box::new(Formula::Eq(var("x"), zero())),
            },
            Formula::Exists {
                var: "x".to_string(),
                var_type: Type::Nat,
                body: Box::new(Formula::Eq(var("x"), zero())),
            },
        ];
        for formula in formulas {
            let lowered = lowerer
                .lower_formula(&formula)
                .unwrap_or_else(|error| panic!("failed to lower `{formula}`: {error}"));
            assert_eq!(lowerer.infer(&lowered), Ok(CoreType::Prop));
        }

        let nested = Formula::Forall {
            var: "x".to_string(),
            var_type: Type::Nat,
            body: Box::new(Formula::Exists {
                var: "y".to_string(),
                var_type: Type::Nat,
                body: Box::new(Formula::Eq(var("x"), var("y"))),
            }),
        };
        let nat = fixture.prelude.nat_type();
        assert_eq!(
            lowerer.lower_formula(&nested),
            Ok(CoreTerm::forall(
                nat.clone(),
                CoreTerm::exists(
                    nat.clone(),
                    CoreTerm::equality(nat, CoreTerm::Bound(1), CoreTerm::Bound(0)),
                ),
            ))
        );

        let shadowed = Formula::Forall {
            var: "x".to_string(),
            var_type: Type::Nat,
            body: Box::new(Formula::Forall {
                var: "x".to_string(),
                var_type: Type::Nat,
                body: Box::new(Formula::Eq(var("x"), var("x"))),
            }),
        };
        let lowered = lowerer.lower_formula(&shadowed).expect("shadowing");
        let CoreTerm::Forall { body, .. } = lowered else {
            panic!("outer forall");
        };
        let CoreTerm::Forall { body, .. } = *body else {
            panic!("inner forall");
        };
        let CoreTerm::Equality { left, right, .. } = *body else {
            panic!("equality body");
        };
        assert_eq!((*left, *right), (CoreTerm::Bound(0), CoreTerm::Bound(0)));
    }

    #[test]
    fn infers_explicit_rank_one_type_applications() {
        let mut fixture = Fixture::new();
        let parameter = TypeParameter::first_order(900);
        let parameter_type = CoreType::Parameter(parameter);
        let identity = fixture
            .elaborator
            .declare_polymorphic_constant(
                "identity",
                vec![parameter],
                CoreType::arrow(parameter_type.clone(), parameter_type.clone()),
            )
            .expect("generic identity");
        let mut lowerer = fixture.lowerer();
        lowerer
            .register_symbol(
                "identity",
                identity,
                vec![parameter],
                vec![parameter_type.clone()],
                parameter_type,
            )
            .expect("register identity");
        let lowered = lowerer
            .lower_term(&Term::App("identity".to_string(), vec![zero()]))
            .expect("infer Nat instance");
        let CoreTerm::Apply { function, .. } = lowered else {
            panic!("identity application");
        };
        assert_eq!(
            *function,
            CoreTerm::instantiate_constant(identity, vec![fixture.prelude.nat_type()])
        );
    }

    #[test]
    fn local_schema_symbols_are_saturated_and_checked() {
        let fixture = Fixture::new();
        let mut lowerer = fixture.lowerer();
        let nat = fixture.prelude.nat_type();
        lowerer
            .bind_proposition_parameter("Q")
            .expect("proposition parameter");
        lowerer
            .bind_predicate_parameter("R", vec![nat.clone(), nat])
            .expect("predicate parameter");
        assert_eq!(
            lowerer.lower_formula(&Formula::Atom("Q".to_string())),
            Ok(CoreTerm::Bound(1))
        );
        assert_eq!(
            lowerer.lower_formula(&Formula::PredApp("R".to_string(), vec![zero(), zero()],)),
            Ok(CoreTerm::apply(
                CoreTerm::apply(
                    CoreTerm::Bound(0),
                    CoreTerm::Constant(fixture.prelude.zero())
                ),
                CoreTerm::Constant(fixture.prelude.zero()),
            ))
        );
        assert!(lowerer
            .lower_formula(&Formula::PredApp("R".to_string(), vec![zero()]))
            .is_err());
    }

    #[test]
    fn rejects_unknown_ill_typed_partial_and_mismatched_forms() {
        let fixture = Fixture::new();
        let mut lowerer = fixture.lowerer();
        assert!(lowerer.lower_term(&var("missing")).is_err());
        assert!(lowerer
            .lower_term(&Term::App("next".to_string(), Vec::new()))
            .is_err());
        assert!(lowerer
            .lower_formula(&Formula::PredApp(
                "Likes".to_string(),
                vec![zero(), var("alice")],
            ))
            .is_err());
        assert!(lowerer
            .lower_formula(&Formula::Eq(zero(), var("alice")))
            .is_err());
        assert!(lowerer
            .lower_formula(&Formula::In(var("alice"), singleton_zero()))
            .is_err());
        assert!(lowerer
            .lower_formula(&Formula::Subset(
                singleton_zero(),
                Term::Singleton(Box::new(var("alice"))),
            ))
            .is_err());
        assert!(lowerer
            .bind_type_parameter("Bad", TypeParameter::any(901))
            .is_err());
        assert!(lowerer
            .register_symbol("P", fixture.atom, Vec::new(), Vec::new(), CoreType::Prop,)
            .is_err());
    }
}
