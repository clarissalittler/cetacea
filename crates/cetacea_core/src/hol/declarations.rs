//! Transactional lowering of legacy declarations into the parallel HOL core.
//!
//! Imports, axioms, theorems, and proof evidence deliberately remain outside
//! this first declaration slice. The supported forms are enough to build a
//! resolved signature, user datatypes, transparent definitions, and checked
//! structural recursion before any production-driver integration.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::{DataDef, DataRecDef, Formula, FormulaDef, Param, ParamKind, Term, TermDef, Type};

use super::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
use super::lowering::{CompatibilityLowerer, LoweringError};
use super::prelude::CompatibilityPrelude;
use super::recursion::{StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{ConstantId, CoreTerm};
use super::types::{CoreType, TypeConstructorId, TypeParameter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompatibilityDeclarationError {
    pub message: String,
}

impl CompatibilityDeclarationError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for CompatibilityDeclarationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for CompatibilityDeclarationError {}

impl From<LoweringError> for CompatibilityDeclarationError {
    fn from(error: LoweringError) -> Self {
        Self::new(error.message)
    }
}

impl From<SpikeError> for CompatibilityDeclarationError {
    fn from(error: SpikeError) -> Self {
        Self::new(error.message)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SymbolRegistration {
    name: String,
    constant: ConstantId,
    type_parameters: Vec<TypeParameter>,
    parameter_types: Vec<CoreType>,
    result_type: CoreType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DataRegistration {
    source: DataDef,
    datatype: TypeConstructorId,
    constructors: Vec<ConstantId>,
}

/// Parser-independent declaration environment for the HOL compatibility path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompatibilityElaborator {
    core: SpikeElaborator,
    prelude: CompatibilityPrelude,
    names: HashSet<String>,
    symbols: Vec<SymbolRegistration>,
    data: HashMap<String, DataRegistration>,
    next_type_parameter: u32,
}

impl CompatibilityElaborator {
    pub fn new() -> Result<Self, CompatibilityDeclarationError> {
        let mut core = SpikeElaborator::new();
        let prelude = CompatibilityPrelude::install(&mut core)?;
        let builtin_nat = DataDef {
            name: "Nat".to_string(),
            ctors: vec![
                crate::DataCtor {
                    name: "zero".to_string(),
                    arg_types: Vec::new(),
                },
                crate::DataCtor {
                    name: "succ".to_string(),
                    arg_types: vec![Type::Nat],
                },
            ],
        };
        let data = HashMap::from([(
            "Nat".to_string(),
            DataRegistration {
                source: builtin_nat,
                datatype: prelude.nat_constructor(),
                constructors: vec![prelude.zero(), prelude.successor()],
            },
        )]);
        let names = [
            "Nat",
            "Set",
            "zero",
            "succ",
            "add",
            "mul",
            "sub",
            "le",
            "empty",
            "singleton",
            "union",
            "inter",
            "diff",
            "powerset",
        ]
        .into_iter()
        .map(str::to_string)
        .collect();
        Ok(Self {
            core,
            prelude,
            names,
            symbols: Vec::new(),
            data,
            next_type_parameter: 0,
        })
    }

    pub fn core(&self) -> &SpikeElaborator {
        &self.core
    }

    pub fn prelude(&self) -> &CompatibilityPrelude {
        &self.prelude
    }

    pub fn lowering_scope(&self) -> Result<CompatibilityLowerer<'_>, LoweringError> {
        let mut lowerer =
            CompatibilityLowerer::new(self.core.types(), self.core.constants(), &self.prelude)?;
        for symbol in &self.symbols {
            lowerer.register_symbol(
                symbol.name.clone(),
                symbol.constant,
                symbol.type_parameters.clone(),
                symbol.parameter_types.clone(),
                symbol.result_type.clone(),
            )?;
        }
        Ok(lowerer)
    }

    pub fn lower_type(&self, ty: &Type) -> Result<CoreType, CompatibilityDeclarationError> {
        Ok(self.lowering_scope()?.lower_type(ty)?)
    }

    pub fn lower_term(&self, term: &Term) -> Result<CoreTerm, CompatibilityDeclarationError> {
        Ok(self.lowering_scope()?.lower_term(term)?)
    }

    pub fn lower_formula(
        &self,
        formula: &Formula,
    ) -> Result<CoreTerm, CompatibilityDeclarationError> {
        Ok(self.lowering_scope()?.lower_formula(formula)?)
    }

    pub fn declare_sort(
        &mut self,
        name: impl Into<String>,
    ) -> Result<TypeConstructorId, CompatibilityDeclarationError> {
        let name = name.into();
        self.ensure_name_free(&name)?;
        let mut staged = self.clone();
        let id = staged.core.declare_base_type(name.clone(), true)?;
        staged.names.insert(name);
        *self = staged;
        Ok(id)
    }

    pub fn declare_constant(
        &mut self,
        name: impl Into<String>,
        ty: &Type,
    ) -> Result<ConstantId, CompatibilityDeclarationError> {
        let name = name.into();
        self.ensure_name_free(&name)?;
        let ty = self.lower_type(ty)?;
        let mut staged = self.clone();
        let constant = staged.core.declare_constant(name.clone(), ty.clone())?;
        staged.finish_symbol(SymbolRegistration {
            name,
            constant,
            type_parameters: Vec::new(),
            parameter_types: Vec::new(),
            result_type: ty,
        })?;
        *self = staged;
        Ok(constant)
    }

    pub fn declare_function(
        &mut self,
        name: impl Into<String>,
        arguments: &[Type],
        result: &Type,
    ) -> Result<ConstantId, CompatibilityDeclarationError> {
        let name = name.into();
        self.ensure_name_free(&name)?;
        let lowerer = self.lowering_scope()?;
        let arguments = arguments
            .iter()
            .map(|argument| lowerer.lower_type(argument))
            .collect::<Result<Vec<_>, _>>()?;
        let result = lowerer.lower_type(result)?;
        let ty = abstract_type(&arguments, result.clone());
        let mut staged = self.clone();
        let constant = staged.core.declare_constant(name.clone(), ty)?;
        staged.finish_symbol(SymbolRegistration {
            name,
            constant,
            type_parameters: Vec::new(),
            parameter_types: arguments,
            result_type: result,
        })?;
        *self = staged;
        Ok(constant)
    }

    pub fn declare_predicate(
        &mut self,
        name: impl Into<String>,
        arguments: &[Type],
    ) -> Result<ConstantId, CompatibilityDeclarationError> {
        let name = name.into();
        self.ensure_name_free(&name)?;
        let lowerer = self.lowering_scope()?;
        let arguments = arguments
            .iter()
            .map(|argument| lowerer.lower_type(argument))
            .collect::<Result<Vec<_>, _>>()?;
        let ty = abstract_type(&arguments, CoreType::Prop);
        let mut staged = self.clone();
        let constant = staged.core.declare_constant(name.clone(), ty)?;
        staged.finish_symbol(SymbolRegistration {
            name,
            constant,
            type_parameters: Vec::new(),
            parameter_types: arguments,
            result_type: CoreType::Prop,
        })?;
        *self = staged;
        Ok(constant)
    }

    pub fn declare_formula_definition(
        &mut self,
        definition: &FormulaDef,
    ) -> Result<ConstantId, CompatibilityDeclarationError> {
        self.ensure_name_free(&definition.name)?;
        let lowered = self.lower_definition_parameters(&definition.params, |lowerer| {
            lowerer.lower_formula(&definition.body)
        })?;
        let body = abstract_term(&lowered.parameter_types, lowered.body);
        let ty = abstract_type(&lowered.parameter_types, CoreType::Prop);
        let mut staged = self.clone();
        let constant = staged.core.declare_polymorphic_transparent_definition(
            definition.name.clone(),
            lowered.type_parameters.clone(),
            ty,
            body,
        )?;
        staged.next_type_parameter = lowered.next_type_parameter;
        staged.finish_symbol(SymbolRegistration {
            name: definition.name.clone(),
            constant,
            type_parameters: lowered.type_parameters,
            parameter_types: lowered.parameter_types,
            result_type: CoreType::Prop,
        })?;
        *self = staged;
        Ok(constant)
    }

    pub fn declare_term_definition(
        &mut self,
        definition: &TermDef,
    ) -> Result<ConstantId, CompatibilityDeclarationError> {
        self.ensure_name_free(&definition.name)?;
        let lowered = self.lower_definition_parameters(&definition.params, |lowerer| {
            let result = lowerer.lower_type(&definition.ty)?;
            let body = lowerer.lower_term_at_type(&definition.body, &result)?;
            Ok((result, body))
        })?;
        let (result_type, body) = lowered.body;
        let body = abstract_term(&lowered.parameter_types, body);
        let ty = abstract_type(&lowered.parameter_types, result_type.clone());
        let mut staged = self.clone();
        let constant = staged.core.declare_polymorphic_transparent_definition(
            definition.name.clone(),
            lowered.type_parameters.clone(),
            ty,
            body,
        )?;
        staged.next_type_parameter = lowered.next_type_parameter;
        staged.finish_symbol(SymbolRegistration {
            name: definition.name.clone(),
            constant,
            type_parameters: lowered.type_parameters,
            parameter_types: lowered.parameter_types,
            result_type,
        })?;
        *self = staged;
        Ok(constant)
    }

    pub fn declare_data(
        &mut self,
        definition: &DataDef,
    ) -> Result<TypeConstructorId, CompatibilityDeclarationError> {
        self.ensure_name_free(&definition.name)?;
        let mut constructor_names = HashSet::new();
        for constructor in &definition.ctors {
            self.ensure_name_free(&constructor.name)?;
            if !constructor_names.insert(constructor.name.as_str()) {
                return Err(CompatibilityDeclarationError::new(format!(
                    "data type `{}` repeats constructor `{}`",
                    definition.name, constructor.name
                )));
            }
        }

        let lowerer = self.lowering_scope()?;
        let constructors = definition
            .ctors
            .iter()
            .map(|constructor| {
                let fields = constructor
                    .arg_types
                    .iter()
                    .map(|field| lower_inductive_field(&lowerer, &definition.name, field))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(InductiveConstructorSpec::new(
                    constructor.name.clone(),
                    fields,
                ))
            })
            .collect::<Result<Vec<_>, CompatibilityDeclarationError>>()?;

        let mut staged = self.clone();
        let datatype = staged.core.declare_inductive(InductiveSpec::new(
            definition.name.clone(),
            Vec::new(),
            constructors,
        ))?;
        let data_type = CoreType::constructor(datatype, Vec::new());
        let staged_lowerer = staged.lowering_scope()?;
        let mut constructor_ids = Vec::with_capacity(definition.ctors.len());
        let mut registrations = Vec::with_capacity(definition.ctors.len());
        for constructor in &definition.ctors {
            let constant = staged.core.resolve_constant(&constructor.name)?;
            let parameter_types = constructor
                .arg_types
                .iter()
                .map(|field| staged_lowerer.lower_type(field))
                .collect::<Result<Vec<_>, _>>()?;
            constructor_ids.push(constant);
            registrations.push(SymbolRegistration {
                name: constructor.name.clone(),
                constant,
                type_parameters: Vec::new(),
                parameter_types,
                result_type: data_type.clone(),
            });
        }
        drop(staged_lowerer);
        staged.names.insert(definition.name.clone());
        for registration in registrations {
            staged.finish_symbol(registration)?;
        }
        staged.data.insert(
            definition.name.clone(),
            DataRegistration {
                source: definition.clone(),
                datatype,
                constructors: constructor_ids,
            },
        );
        *self = staged;
        Ok(datatype)
    }

    pub fn declare_structural_definition(
        &mut self,
        definition: &DataRecDef,
    ) -> Result<ConstantId, CompatibilityDeclarationError> {
        self.ensure_name_free(&definition.name)?;
        let data = self
            .data
            .get(&definition.data_name)
            .cloned()
            .ok_or_else(|| {
                CompatibilityDeclarationError::new(format!(
                    "recursive definition `{}` uses unknown data type `{}`",
                    definition.name, definition.data_name
                ))
            })?;
        if definition.arms.len() != data.source.ctors.len() {
            return Err(CompatibilityDeclarationError::new(format!(
                "recursive definition `{}` needs {} arm(s), but got {}",
                definition.name,
                data.source.ctors.len(),
                definition.arms.len()
            )));
        }
        let mut parameter_names = HashSet::new();
        if !parameter_names.insert(definition.param.as_str()) {
            unreachable!("an empty set accepts the recursive parameter")
        }
        for (name, _) in &definition.extra_params {
            if !parameter_names.insert(name.as_str()) {
                return Err(CompatibilityDeclarationError::new(format!(
                    "recursive definition `{}` repeats parameter `{name}`",
                    definition.name
                )));
            }
        }

        let lowerer = self.lowering_scope()?;
        let fixed_parameter_types = definition
            .extra_params
            .iter()
            .map(|(_, ty)| lowerer.lower_type(ty))
            .collect::<Result<Vec<_>, _>>()?;
        let result_type = lowerer.lower_type(&definition.result_type)?;
        drop(lowerer);

        let mut arms = Vec::with_capacity(definition.arms.len());
        for (arm_index, (arm, constructor)) in
            definition.arms.iter().zip(&data.source.ctors).enumerate()
        {
            if arm.ctor != constructor.name {
                return Err(CompatibilityDeclarationError::new(format!(
                    "recursive definition `{}` arm `{}` is out of order; expected `{}`",
                    definition.name, arm.ctor, constructor.name
                )));
            }
            let recursive_fields = constructor
                .arg_types
                .iter()
                .filter(|ty| is_direct_recursive_type(ty, &definition.data_name))
                .count();
            if arm.arg_names.len() != constructor.arg_types.len()
                || arm.rec_names.len() != recursive_fields
            {
                return Err(CompatibilityDeclarationError::new(format!(
                    "recursive definition `{}` arm `{}` has inconsistent binder metadata",
                    definition.name, arm.ctor
                )));
            }
            let mut binder_names = HashSet::new();
            for name in arm
                .arg_names
                .iter()
                .chain(&arm.rec_names)
                .chain(definition.extra_params.iter().map(|(name, _)| name))
            {
                if !binder_names.insert(name.as_str()) {
                    return Err(CompatibilityDeclarationError::new(format!(
                        "recursive definition `{}` arm `{}` repeats binder `{name}`",
                        definition.name, arm.ctor
                    )));
                }
            }

            let mut arm_lowerer = self.lowering_scope()?;
            for (name, ty) in definition.extra_params.iter().rev() {
                let ty = arm_lowerer.lower_type(ty)?;
                arm_lowerer.bind_term_parameter(name.clone(), ty)?;
            }
            for name in arm.rec_names.iter().rev() {
                arm_lowerer.bind_term_parameter(name.clone(), result_type.clone())?;
            }
            for (name, ty) in arm.arg_names.iter().zip(&constructor.arg_types).rev() {
                let ty = arm_lowerer.lower_type(ty)?;
                arm_lowerer.bind_term_parameter(name.clone(), ty)?;
            }
            let body = arm_lowerer.lower_term_at_type(&arm.body, &result_type)?;
            arms.push(StructuralArmSpec::new(data.constructors[arm_index], body));
        }

        let datatype_type = CoreType::constructor(data.datatype, Vec::new());
        let mut staged = self.clone();
        let constant = staged
            .core
            .declare_structural_definition(StructuralDefinitionSpec {
                name: definition.name.clone(),
                type_parameters: Vec::new(),
                datatype: data.datatype,
                datatype_arguments: Vec::new(),
                recursive_argument_index: 0,
                fixed_parameter_types: fixed_parameter_types.clone(),
                result_type: result_type.clone(),
                arms,
            })?;
        let mut parameter_types = vec![datatype_type];
        parameter_types.extend(fixed_parameter_types);
        staged.finish_symbol(SymbolRegistration {
            name: definition.name.clone(),
            constant,
            type_parameters: Vec::new(),
            parameter_types,
            result_type,
        })?;
        *self = staged;
        Ok(constant)
    }

    fn lower_definition_parameters<T>(
        &self,
        parameters: &[Param],
        lower_body: impl FnOnce(&mut CompatibilityLowerer<'_>) -> Result<T, LoweringError>,
    ) -> Result<LoweredDefinition<T>, CompatibilityDeclarationError> {
        let mut seen = HashSet::new();
        for parameter in parameters {
            if self.names.contains(&parameter.name) {
                return Err(CompatibilityDeclarationError::new(format!(
                    "definition parameter `{}` conflicts with a top-level name",
                    parameter.name
                )));
            }
            if !seen.insert(parameter.name.as_str()) {
                return Err(CompatibilityDeclarationError::new(format!(
                    "definition parameter `{}` is repeated",
                    parameter.name
                )));
            }
        }

        let mut lowerer = self.lowering_scope()?;
        let mut next_type_parameter = self.next_type_parameter;
        let mut type_parameters = Vec::new();
        let mut parameter_types = Vec::new();
        for parameter in parameters {
            match &parameter.kind {
                ParamKind::Type => {
                    let core_parameter = TypeParameter::first_order(next_type_parameter);
                    next_type_parameter = next_type_parameter.checked_add(1).ok_or_else(|| {
                        CompatibilityDeclarationError::new("too many compatibility type parameters")
                    })?;
                    lowerer.bind_type_parameter(parameter.name.clone(), core_parameter)?;
                    type_parameters.push(core_parameter);
                }
                ParamKind::Term(ty) => {
                    let ty = lowerer.lower_type(ty)?;
                    lowerer.bind_term_parameter(parameter.name.clone(), ty.clone())?;
                    parameter_types.push(ty);
                }
                ParamKind::Prop => {
                    lowerer.bind_proposition_parameter(parameter.name.clone())?;
                    parameter_types.push(CoreType::Prop);
                }
                ParamKind::Predicate(domains) => {
                    let domains = domains
                        .iter()
                        .map(|domain| lowerer.lower_type(domain))
                        .collect::<Result<Vec<_>, _>>()?;
                    let predicate_type = abstract_type(&domains, CoreType::Prop);
                    lowerer.bind_predicate_parameter(parameter.name.clone(), domains)?;
                    parameter_types.push(predicate_type);
                }
            }
        }
        let body = lower_body(&mut lowerer)?;
        Ok(LoweredDefinition {
            type_parameters,
            parameter_types,
            body,
            next_type_parameter,
        })
    }

    fn ensure_name_free(&self, name: &str) -> Result<(), CompatibilityDeclarationError> {
        if self.names.contains(name) {
            Err(CompatibilityDeclarationError::new(format!(
                "compatibility name `{name}` is already declared"
            )))
        } else {
            Ok(())
        }
    }

    fn finish_symbol(
        &mut self,
        registration: SymbolRegistration,
    ) -> Result<(), CompatibilityDeclarationError> {
        self.names.insert(registration.name.clone());
        self.symbols.push(registration);
        // Reconstructing the scope verifies the persistent surface descriptor
        // against the just-declared core constant before the staged state is
        // committed.
        self.lowering_scope()?;
        Ok(())
    }
}

struct LoweredDefinition<T> {
    type_parameters: Vec<TypeParameter>,
    parameter_types: Vec<CoreType>,
    body: T,
    next_type_parameter: u32,
}

fn lower_inductive_field(
    lowerer: &CompatibilityLowerer<'_>,
    datatype: &str,
    ty: &Type,
) -> Result<InductiveFieldType, CompatibilityDeclarationError> {
    if is_direct_recursive_type(ty, datatype) {
        return Ok(InductiveFieldType::Recursive);
    }
    if !type_mentions_name(ty, datatype) {
        return Ok(InductiveFieldType::existing(lowerer.lower_type(ty)?));
    }
    match ty {
        Type::Prod(left, right) => Ok(InductiveFieldType::product(
            lower_inductive_field(lowerer, datatype, left)?,
            lower_inductive_field(lowerer, datatype, right)?,
        )),
        Type::Set(_) => Err(CompatibilityDeclarationError::new(format!(
            "data type `{datatype}` uses unsupported nested recursion under `Set`"
        ))),
        Type::Named(_) | Type::Nat => unreachable!("direct recursion handled above"),
    }
}

fn is_direct_recursive_type(ty: &Type, datatype: &str) -> bool {
    matches!(ty, Type::Named(name) if name == datatype)
        || matches!(ty, Type::Nat if datatype == "Nat")
}

fn type_mentions_name(ty: &Type, name: &str) -> bool {
    match ty {
        Type::Named(candidate) => candidate == name,
        Type::Nat => name == "Nat",
        Type::Prod(left, right) => {
            type_mentions_name(left, name) || type_mentions_name(right, name)
        }
        Type::Set(element) => type_mentions_name(element, name),
    }
}

fn abstract_type(parameters: &[CoreType], result: CoreType) -> CoreType {
    parameters.iter().rev().fold(result, |result, parameter| {
        CoreType::arrow(parameter.clone(), result)
    })
}

fn abstract_term(parameters: &[CoreType], body: CoreTerm) -> CoreTerm {
    parameters.iter().rev().fold(body, |body, parameter| {
        CoreTerm::lambda(parameter.clone(), body)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::terms::{definitionally_equal, infer_type, normalize, TermContext};
    use crate::{DataCtor, DataRecArm};

    fn var(name: &str) -> Term {
        Term::Var(name.to_string())
    }

    fn list_definition() -> DataDef {
        DataDef {
            name: "List".to_string(),
            ctors: vec![
                DataCtor {
                    name: "nil".to_string(),
                    arg_types: Vec::new(),
                },
                DataCtor {
                    name: "cons".to_string(),
                    arg_types: vec![Type::Nat, Type::Named("List".to_string())],
                },
            ],
        }
    }

    #[test]
    fn lowers_basic_declarations_into_a_persistent_resolved_scope() {
        let mut elaborator = CompatibilityElaborator::new().expect("compatibility elaborator");
        let person = elaborator.declare_sort("Person").expect("Person");
        let alice = elaborator
            .declare_constant("alice", &Type::Named("Person".to_string()))
            .expect("alice");
        let next = elaborator
            .declare_function("next", &[Type::Nat], &Type::Nat)
            .expect("next");
        let likes = elaborator
            .declare_predicate(
                "Likes",
                &[
                    Type::Named("Person".to_string()),
                    Type::Named("Person".to_string()),
                ],
            )
            .expect("Likes");

        assert_eq!(elaborator.core().types().resolve("Person"), Some(person));
        assert_eq!(elaborator.core().constants().resolve("alice"), Some(alice));
        assert_eq!(elaborator.core().constants().resolve("next"), Some(next));
        assert_eq!(elaborator.core().constants().resolve("Likes"), Some(likes));
        let formula = Formula::PredApp("Likes".to_string(), vec![var("alice"), var("alice")]);
        let lowered = elaborator
            .lower_formula(&formula)
            .expect("resolved formula");
        assert_eq!(
            infer_type(
                elaborator.core().types(),
                elaborator.core().constants(),
                &TermContext::new(),
                &lowered,
            ),
            Ok(CoreType::Prop)
        );
    }

    #[test]
    fn data_and_defrec_lower_with_the_legacy_binder_layout() {
        let mut elaborator = CompatibilityElaborator::new().expect("compatibility elaborator");
        let list = elaborator
            .declare_data(&list_definition())
            .expect("List data");
        let length = DataRecDef {
            name: "length".to_string(),
            param: "l".to_string(),
            data_name: "List".to_string(),
            extra_params: Vec::new(),
            result_type: Type::Nat,
            arms: vec![
                DataRecArm {
                    ctor: "nil".to_string(),
                    arg_names: Vec::new(),
                    rec_names: Vec::new(),
                    body: Term::Zero,
                },
                DataRecArm {
                    ctor: "cons".to_string(),
                    arg_names: vec!["head".to_string(), "tail".to_string()],
                    rec_names: vec!["rec".to_string()],
                    body: Term::Succ(Box::new(var("rec"))),
                },
            ],
        };
        let length_id = elaborator
            .declare_structural_definition(&length)
            .expect("length");

        let append = DataRecDef {
            name: "append".to_string(),
            param: "left".to_string(),
            data_name: "List".to_string(),
            extra_params: vec![("right".to_string(), Type::Named("List".to_string()))],
            result_type: Type::Named("List".to_string()),
            arms: vec![
                DataRecArm {
                    ctor: "nil".to_string(),
                    arg_names: Vec::new(),
                    rec_names: Vec::new(),
                    body: var("right"),
                },
                DataRecArm {
                    ctor: "cons".to_string(),
                    arg_names: vec!["head".to_string(), "tail".to_string()],
                    rec_names: vec!["rec".to_string()],
                    body: Term::App("cons".to_string(), vec![var("head"), var("rec")]),
                },
            ],
        };
        let append_id = elaborator
            .declare_structural_definition(&append)
            .expect("append");
        let nil = Term::Var("nil".to_string());
        let singleton = Term::App("cons".to_string(), vec![Term::Zero, nil.clone()]);
        let lowered_singleton = elaborator.lower_term(&singleton).expect("singleton");
        let lowered_length = elaborator
            .lower_term(&Term::App("length".to_string(), vec![singleton.clone()]))
            .expect("length singleton");
        let one = CoreTerm::apply(
            CoreTerm::Constant(elaborator.prelude().successor()),
            CoreTerm::Constant(elaborator.prelude().zero()),
        );
        assert!(definitionally_equal(
            elaborator.core().types(),
            elaborator.core().constants(),
            &TermContext::new(),
            &lowered_length,
            &one,
        )
        .expect("length computes"));
        let lowered_append = elaborator
            .lower_term(&Term::App("append".to_string(), vec![singleton, nil]))
            .expect("append singleton nil");
        assert!(definitionally_equal(
            elaborator.core().types(),
            elaborator.core().constants(),
            &TermContext::new(),
            &lowered_append,
            &lowered_singleton,
        )
        .expect("append computes at recursive argument zero"));
        assert_eq!(
            elaborator
                .core()
                .recursion()
                .definition(length_id)
                .map(|definition| definition.recursive_argument_index),
            Some(0)
        );
        assert_eq!(
            elaborator
                .core()
                .recursion()
                .definition(append_id)
                .map(|definition| definition.recursive_argument_index),
            Some(0)
        );
        assert_eq!(elaborator.core().types().resolve("List"), Some(list));
    }

    #[test]
    fn transparent_definitions_lower_schema_parameters_and_predicate_lambdas() {
        let mut elaborator = CompatibilityElaborator::new().expect("compatibility elaborator");
        elaborator.declare_sort("Person").expect("Person");
        elaborator
            .declare_constant("alice", &Type::Named("Person".to_string()))
            .expect("alice");

        let identity = TermDef {
            name: "identity".to_string(),
            params: vec![
                Param {
                    name: "A".to_string(),
                    kind: ParamKind::Type,
                },
                Param {
                    name: "x".to_string(),
                    kind: ParamKind::Term(Type::Named("A".to_string())),
                },
            ],
            ty: Type::Named("A".to_string()),
            body: var("x"),
        };
        let identity_id = elaborator
            .declare_term_definition(&identity)
            .expect("identity");
        let identity_alice = elaborator
            .lower_term(&Term::App("identity".to_string(), vec![var("alice")]))
            .expect("identity Person instance");
        let alice = elaborator.lower_term(&var("alice")).expect("alice");
        assert!(definitionally_equal(
            elaborator.core().types(),
            elaborator.core().constants(),
            &TermContext::new(),
            &identity_alice,
            &alice,
        )
        .expect("identity delta/beta computes"));
        assert!(elaborator
            .core()
            .constants()
            .transparent_definition(identity_id)
            .is_some());

        let apply_predicate = FormulaDef {
            name: "ApplyPredicate".to_string(),
            params: vec![
                Param {
                    name: "A".to_string(),
                    kind: ParamKind::Type,
                },
                Param {
                    name: "P".to_string(),
                    kind: ParamKind::Predicate(vec![Type::Named("A".to_string())]),
                },
                Param {
                    name: "x".to_string(),
                    kind: ParamKind::Term(Type::Named("A".to_string())),
                },
            ],
            body: Formula::PredApp("P".to_string(), vec![var("x")]),
        };
        elaborator
            .declare_formula_definition(&apply_predicate)
            .expect("ApplyPredicate");
        let formula = Formula::PredApp(
            "ApplyPredicate".to_string(),
            vec![
                Term::PredLambda {
                    params: vec![crate::LambdaParam {
                        name: "p".to_string(),
                        ty: Some(Type::Named("Person".to_string())),
                    }],
                    body: Box::new(Formula::Eq(var("p"), var("p"))),
                },
                var("alice"),
            ],
        );
        let lowered = elaborator
            .lower_formula(&formula)
            .expect("generic formula use");
        let normalized = normalize(
            elaborator.core().types(),
            elaborator.core().constants(),
            &TermContext::new(),
            &lowered,
        )
        .expect("normalize ApplyPredicate");
        assert_eq!(
            normalized,
            CoreTerm::equality(
                elaborator
                    .lower_type(&Type::Named("Person".to_string()))
                    .expect("Person type"),
                alice.clone(),
                alice,
            )
        );
    }

    #[test]
    fn failed_declarations_leave_every_catalog_unchanged() {
        let mut elaborator = CompatibilityElaborator::new().expect("compatibility elaborator");
        elaborator.declare_sort("Person").expect("Person");
        let before = elaborator.clone();
        let bad = TermDef {
            name: "bad".to_string(),
            params: Vec::new(),
            ty: Type::Nat,
            body: Term::Universe(Type::Nat),
        };
        assert!(elaborator.declare_term_definition(&bad).is_err());
        assert_eq!(elaborator, before);
        elaborator
            .declare_constant("bad", &Type::Nat)
            .expect("failed definition did not reserve its name");

        let recursive_product = DataDef {
            name: "Nested".to_string(),
            ctors: vec![DataCtor {
                name: "nest".to_string(),
                arg_types: vec![Type::Prod(
                    Box::new(Type::Named("Nested".to_string())),
                    Box::new(Type::Nat),
                )],
            }],
        };
        let before_nested = elaborator.clone();
        assert!(elaborator.declare_data(&recursive_product).is_err());
        assert_eq!(elaborator, before_nested);
    }
}
