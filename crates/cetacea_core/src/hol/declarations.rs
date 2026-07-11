//! Transactional lowering of legacy declarations into the parallel HOL core.
//!
//! This module remains parser-independent: the production driver supplies
//! canonical declarations after ordinary legacy name resolution. The opt-in
//! HOL shadow runner owns one persistent elaborator across commands, imports,
//! and aliases, while this layer transactionally covers resolved signatures,
//! user datatypes, transparent/structural definitions, theorem status
//! boundaries, every legacy proof-object variant, and checked compatibility
//! conversion.

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::{
    ClassicalRule, DataDef, DataRecDef, DraftProof as LegacyDraftProof, Formula, FormulaDef, Param,
    ParamKind, PredicateArg, SchemaSubst, Term, TermDef, Type,
};

use super::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
use super::library_registry::{
    HolLibraryRegistry, InstalledCardinalityLibrary, InstalledFiniteLibrary, InstalledListLibrary,
};
use super::lowering::{CompatibilityLowerer, LoweringError};
use super::prelude::CompatibilityPrelude;
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{
    definitionally_equal, instantiate_binder, instantiate_term_parameters_under_binders, normalize,
    shift_under_new_binder, ConstantId, CoreTerm,
};
use super::theorems::TheoremId;
use super::types::{CoreType, TypeConstructorId, TypeParameter};
use super::{DeclarationReceipt, StatementFragment};

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

#[derive(Clone, Debug, PartialEq, Eq)]
struct TheoremRegistration {
    name: String,
    theorem: TheoremId,
    parameters: Vec<Param>,
    type_parameters: Vec<TypeParameter>,
    parameter_types: Vec<CoreType>,
}

/// Parser-independent declaration environment for the HOL compatibility path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompatibilityElaborator {
    core: SpikeElaborator,
    prelude: CompatibilityPrelude,
    names: HashSet<String>,
    symbols: Vec<SymbolRegistration>,
    data: HashMap<String, DataRegistration>,
    theorems: Vec<TheoremRegistration>,
    libraries: HolLibraryRegistry,
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
            theorems: Vec::new(),
            libraries: HolLibraryRegistry::default(),
            next_type_parameter: 0,
        })
    }

    pub fn core(&self) -> &SpikeElaborator {
        &self.core
    }

    pub fn prelude(&self) -> &CompatibilityPrelude {
        &self.prelude
    }

    pub fn libraries(&self) -> &HolLibraryRegistry {
        &self.libraries
    }

    /// Install the versioned built-in generic List package into the same
    /// persistent core owned by compatibility checking. Its reserved core
    /// namespace is intentionally not added to the legacy surface scope.
    pub fn install_builtin_list_v1(
        &mut self,
    ) -> Result<InstalledListLibrary, CompatibilityDeclarationError> {
        let natural_type = self.prelude.nat_type();
        let zero = self.prelude.zero();
        let successor = self.prelude.successor();
        Ok(self
            .libraries
            .install_builtin_list_v1(&mut self.core, natural_type, zero, successor)?)
    }

    /// Install the versioned cardinality-transport package and its generic
    /// List dependency without adding either package to the legacy surface.
    pub fn install_builtin_cardinality_v1(
        &mut self,
    ) -> Result<InstalledCardinalityLibrary, CompatibilityDeclarationError> {
        let natural_type = self.prelude.nat_type();
        let zero = self.prelude.zero();
        let successor = self.prelude.successor();
        Ok(self.libraries.install_builtin_cardinality_v1(
            &mut self.core,
            natural_type,
            zero,
            successor,
        )?)
    }

    /// Install the versioned finite-enumeration predicate and its generic List
    /// dependency without adding `HasCard` to the legacy surface.
    pub fn install_builtin_finite_v1(
        &mut self,
    ) -> Result<InstalledFiniteLibrary, CompatibilityDeclarationError> {
        let natural_type = self.prelude.nat_type();
        let zero = self.prelude.zero();
        let successor = self.prelude.successor();
        Ok(self.libraries.install_builtin_finite_v1(
            &mut self.core,
            natural_type,
            zero,
            successor,
        )?)
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

    pub fn declare_trusted_axiom(
        &mut self,
        name: impl Into<String>,
        parameters: &[Param],
        statement: &Formula,
    ) -> Result<(TheoremId, DeclarationReceipt), CompatibilityDeclarationError> {
        let name = name.into();
        self.ensure_name_free(&name)?;
        let lowered = self
            .lower_definition_parameters(parameters, |lowerer| lowerer.lower_formula(statement))?;
        let mut staged = self.clone();
        let (theorem, receipt) = staged.core.declare_trusted_axiom_with_parameters(
            name.clone(),
            lowered.type_parameters.clone(),
            lowered.parameter_types.clone(),
            lowered.body,
        )?;
        staged.next_type_parameter = lowered.next_type_parameter;
        staged.finish_theorem(TheoremRegistration {
            name,
            theorem,
            parameters: parameters.to_vec(),
            type_parameters: lowered.type_parameters,
            parameter_types: lowered.parameter_types,
        });
        *self = staged;
        Ok((theorem, receipt))
    }

    /// Lower and classify a canonical legacy theorem signature without
    /// declaring it or requiring proof evidence. This is the pre-receipt seam
    /// used to certify model-search eligibility for failed proofs.
    pub fn classify_legacy_statement(
        &self,
        parameters: &[Param],
        statement: &Formula,
    ) -> Result<StatementFragment, CompatibilityDeclarationError> {
        let lowered = self
            .lower_definition_parameters(parameters, |lowerer| lowerer.lower_formula(statement))?;
        Ok(self
            .core
            .classify_with_parameters(&lowered.parameter_types, &lowered.body)?)
    }

    /// Store a checked theorem template after lowering its legacy parameters
    /// and statement. Proof-node lowering is intentionally a separate layer;
    /// this entry point receives explicit HOL evidence in the same open term
    /// parameter context as the lowered statement.
    pub fn declare_checked_theorem(
        &mut self,
        name: impl Into<String>,
        parameters: &[Param],
        statement: &Formula,
        proof: HolDraftProof,
    ) -> Result<(TheoremId, DeclarationReceipt), CompatibilityDeclarationError> {
        let name = name.into();
        self.ensure_name_free(&name)?;
        let lowered = self
            .lower_definition_parameters(parameters, |lowerer| lowerer.lower_formula(statement))?;
        let mut staged = self.clone();
        let (theorem, receipt) = staged.core.declare_theorem_with_parameters(
            name.clone(),
            lowered.type_parameters.clone(),
            lowered.parameter_types.clone(),
            lowered.body,
            proof,
        )?;
        staged.next_type_parameter = lowered.next_type_parameter;
        staged.finish_theorem(TheoremRegistration {
            name,
            theorem,
            parameters: parameters.to_vec(),
            type_parameters: lowered.type_parameters,
            parameter_types: lowered.parameter_types,
        });
        *self = staged;
        Ok((theorem, receipt))
    }

    pub fn declare_incomplete_theorem(
        &mut self,
        name: impl Into<String>,
        parameters: &[Param],
        statement: &Formula,
        proof: HolDraftProof,
    ) -> Result<(TheoremId, DeclarationReceipt), CompatibilityDeclarationError> {
        let name = name.into();
        self.ensure_name_free(&name)?;
        let lowered = self
            .lower_definition_parameters(parameters, |lowerer| lowerer.lower_formula(statement))?;
        let mut staged = self.clone();
        let (theorem, receipt) = staged.core.declare_incomplete_theorem_with_parameters(
            name.clone(),
            lowered.type_parameters.clone(),
            lowered.parameter_types.clone(),
            lowered.body,
            proof,
        )?;
        staged.next_type_parameter = lowered.next_type_parameter;
        staged.finish_theorem(TheoremRegistration {
            name,
            theorem,
            parameters: parameters.to_vec(),
            type_parameters: lowered.type_parameters,
            parameter_types: lowered.parameter_types,
        });
        *self = staged;
        Ok((theorem, receipt))
    }

    /// Lower a complete legacy proof object and store the resulting checked
    /// theorem transactionally. Legacy arithmetic conversion is reconstructed
    /// from checked compatibility theorems rather than admitted as reduction.
    pub fn declare_legacy_checked_theorem(
        &mut self,
        name: impl Into<String>,
        parameters: &[Param],
        statement: &Formula,
        proof: &LegacyDraftProof,
    ) -> Result<(TheoremId, DeclarationReceipt), CompatibilityDeclarationError> {
        let name = name.into();
        self.ensure_name_free(&name)?;
        let lowered = self.lower_definition_parameters(parameters, |lowerer| {
            let statement = lowerer.lower_formula(statement)?;
            let proof = lower_legacy_proof(self, lowerer.clone(), proof, false)?;
            ensure_same_proposition(self, lowerer, &proof.proposition, &statement)?;
            Ok((statement, proof.proof))
        })?;
        let (statement, proof) = lowered.body;
        let mut staged = self.clone();
        let (theorem, receipt) = staged.core.declare_theorem_with_parameters(
            name.clone(),
            lowered.type_parameters.clone(),
            lowered.parameter_types.clone(),
            statement,
            proof,
        )?;
        staged.next_type_parameter = lowered.next_type_parameter;
        staged.finish_theorem(TheoremRegistration {
            name,
            theorem,
            parameters: parameters.to_vec(),
            type_parameters: lowered.type_parameters,
            parameter_types: lowered.parameter_types,
        });
        *self = staged;
        Ok((theorem, receipt))
    }

    pub fn declare_legacy_incomplete_theorem(
        &mut self,
        name: impl Into<String>,
        parameters: &[Param],
        statement: &Formula,
        proof: &LegacyDraftProof,
    ) -> Result<(TheoremId, DeclarationReceipt), CompatibilityDeclarationError> {
        let name = name.into();
        self.ensure_name_free(&name)?;
        let lowered = self.lower_definition_parameters(parameters, |lowerer| {
            let statement = lowerer.lower_formula(statement)?;
            let proof = lower_legacy_proof(self, lowerer.clone(), proof, true)?;
            ensure_same_proposition(self, lowerer, &proof.proposition, &statement)?;
            Ok((statement, proof.proof))
        })?;
        let (statement, proof) = lowered.body;
        let mut staged = self.clone();
        let (theorem, receipt) = staged.core.declare_incomplete_theorem_with_parameters(
            name.clone(),
            lowered.type_parameters.clone(),
            lowered.parameter_types.clone(),
            statement,
            proof,
        )?;
        staged.next_type_parameter = lowered.next_type_parameter;
        staged.finish_theorem(TheoremRegistration {
            name,
            theorem,
            parameters: parameters.to_vec(),
            type_parameters: lowered.type_parameters,
            parameter_types: lowered.parameter_types,
        });
        *self = staged;
        Ok((theorem, receipt))
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

    fn finish_theorem(&mut self, registration: TheoremRegistration) {
        self.names.insert(registration.name.clone());
        self.theorems.push(registration);
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

struct LoweredLegacyProof {
    proof: HolDraftProof,
    proposition: CoreTerm,
}

#[derive(Clone)]
struct CompatibilityArithmeticRewrite {
    ty: CoreType,
    from: CoreTerm,
    to: CoreTerm,
    proof: HolDraftProof,
}

#[derive(Clone)]
struct CompatibilityArithmeticStep {
    before: CoreTerm,
    after: CoreTerm,
    rewrite: CompatibilityArithmeticRewrite,
}

#[derive(Clone)]
struct LegacyProofLowerer<'a> {
    environment: &'a CompatibilityElaborator,
    lowerer: CompatibilityLowerer<'a>,
    hypotheses: Vec<(String, CoreTerm)>,
    allow_incomplete: bool,
}

fn lower_legacy_proof<'a>(
    environment: &'a CompatibilityElaborator,
    lowerer: CompatibilityLowerer<'a>,
    proof: &LegacyDraftProof,
    allow_incomplete: bool,
) -> Result<LoweredLegacyProof, LoweringError> {
    LegacyProofLowerer {
        environment,
        lowerer,
        hypotheses: Vec::new(),
        allow_incomplete,
    }
    .lower(proof)
}

impl LegacyProofLowerer<'_> {
    fn lower(&mut self, proof: &LegacyDraftProof) -> Result<LoweredLegacyProof, LoweringError> {
        match proof {
            LegacyDraftProof::Hyp(name) => {
                let (index, (_, proposition)) = self
                    .hypotheses
                    .iter()
                    .rev()
                    .enumerate()
                    .find(|(_, (candidate, _))| candidate == name)
                    .ok_or_else(|| {
                        LoweringError::new(format!(
                            "unknown legacy proof hypothesis `{name}` during HOL lowering"
                        ))
                    })?;
                let index = u32::try_from(index)
                    .map_err(|_| LoweringError::new("too many compatibility hypotheses"))?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::Hypothesis(index),
                    proposition: proposition.clone(),
                })
            }
            LegacyDraftProof::TrueIntro => Ok(LoweredLegacyProof {
                proof: HolDraftProof::TruthIntro,
                proposition: CoreTerm::Truth,
            }),
            LegacyDraftProof::FalseElim {
                proof_false,
                target,
            } => {
                let proof_false = self.lower(proof_false)?;
                self.expect_normalized_shape(
                    &proof_false.proposition,
                    |term| matches!(term, CoreTerm::Falsity),
                    "false elimination needs a proof of falsity",
                )?;
                let target = self.lowerer.lower_formula(target)?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::FalseElim {
                        proof_false: Box::new(proof_false.proof),
                        target: target.clone(),
                    },
                    proposition: target,
                })
            }
            LegacyDraftProof::AndIntro(left, right) => {
                let left = self.lower(left)?;
                let right = self.lower(right)?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::AndIntro(Box::new(left.proof), Box::new(right.proof)),
                    proposition: CoreTerm::and(left.proposition, right.proposition),
                })
            }
            LegacyDraftProof::AndElimLeft(proof_and)
            | LegacyDraftProof::AndElimRight(proof_and) => {
                let proof_and = self.lower(proof_and)?;
                let normalized = self.normalize(&proof_and.proposition)?;
                let CoreTerm::And(left, right) = normalized else {
                    return Err(LoweringError::new(
                        "conjunction elimination needs a proof of a conjunction",
                    ));
                };
                let (proof, proposition) = if matches!(proof, LegacyDraftProof::AndElimLeft(_)) {
                    (HolDraftProof::AndElimLeft(Box::new(proof_and.proof)), *left)
                } else {
                    (
                        HolDraftProof::AndElimRight(Box::new(proof_and.proof)),
                        *right,
                    )
                };
                Ok(LoweredLegacyProof { proof, proposition })
            }
            LegacyDraftProof::OrIntroLeft {
                proof_left,
                right_formula,
            } => {
                let left = self.lower(proof_left)?;
                let right = self.lowerer.lower_formula(right_formula)?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::OrIntroLeft {
                        proof_left: Box::new(left.proof),
                        right: right.clone(),
                    },
                    proposition: CoreTerm::or(left.proposition, right),
                })
            }
            LegacyDraftProof::OrIntroRight {
                left_formula,
                proof_right,
            } => {
                let left = self.lowerer.lower_formula(left_formula)?;
                let right = self.lower(proof_right)?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::OrIntroRight {
                        left: left.clone(),
                        proof_right: Box::new(right.proof),
                    },
                    proposition: CoreTerm::or(left, right.proposition),
                })
            }
            LegacyDraftProof::OrElim {
                proof_or,
                left_name,
                left_case,
                right_name,
                right_case,
                target,
            } => {
                let proof_or = self.lower(proof_or)?;
                let normalized = self.normalize(&proof_or.proposition)?;
                let CoreTerm::Or(left, right) = normalized else {
                    return Err(LoweringError::new(
                        "disjunction elimination needs a proof of a disjunction",
                    ));
                };
                let target = self.lowerer.lower_formula(target)?;
                let mut left_scope = self.clone();
                left_scope
                    .hypotheses
                    .push((left_name.clone(), (*left).clone()));
                let left_case = left_scope.lower(left_case)?;
                ensure_same_proposition(
                    self.environment,
                    &self.lowerer,
                    &left_case.proposition,
                    &target,
                )?;
                let mut right_scope = self.clone();
                right_scope
                    .hypotheses
                    .push((right_name.clone(), (*right).clone()));
                let right_case = right_scope.lower(right_case)?;
                ensure_same_proposition(
                    self.environment,
                    &self.lowerer,
                    &right_case.proposition,
                    &target,
                )?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::OrElim {
                        proof_or: Box::new(proof_or.proof),
                        left_case: Box::new(left_case.proof),
                        right_case: Box::new(right_case.proof),
                        target: target.clone(),
                    },
                    proposition: target,
                })
            }
            LegacyDraftProof::ImpIntro {
                hyp_name,
                hyp_formula,
                body,
            } => {
                let premise = self.lowerer.lower_formula(hyp_formula)?;
                let mut body_scope = self.clone();
                body_scope
                    .hypotheses
                    .push((hyp_name.clone(), premise.clone()));
                let body = body_scope.lower(body)?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::ImpIntro {
                        premise: premise.clone(),
                        body: Box::new(body.proof),
                    },
                    proposition: CoreTerm::implies(premise, body.proposition),
                })
            }
            LegacyDraftProof::ImpElim {
                proof_imp,
                proof_arg,
            } => {
                let implication = self.lower(proof_imp)?;
                let normalized = self.normalize(&implication.proposition)?;
                let CoreTerm::Implies(premise, conclusion) = normalized else {
                    return Err(LoweringError::new(
                        "implication elimination needs an implication proof",
                    ));
                };
                let argument = self.lower(proof_arg)?;
                ensure_same_proposition(
                    self.environment,
                    &self.lowerer,
                    &argument.proposition,
                    &premise,
                )?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::ImpElim {
                        proof_implication: Box::new(implication.proof),
                        proof_argument: Box::new(argument.proof),
                    },
                    proposition: *conclusion,
                })
            }
            LegacyDraftProof::EqRefl(term) => {
                let term = self.lowerer.lower_term(term)?;
                let ty = self.lowerer.infer_core(&term)?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::EqualityRefl(term.clone()),
                    proposition: CoreTerm::equality(ty, term.clone(), term),
                })
            }
            LegacyDraftProof::EqSubst {
                eq_proof,
                proof_body,
                target,
            } => {
                let equality = self.lower(eq_proof)?;
                let normalized = self.normalize(&equality.proposition)?;
                let CoreTerm::Equality { ty, left, right } = normalized else {
                    return Err(LoweringError::new(
                        "legacy equality substitution needs an equality proof",
                    ));
                };
                let proof_body = self.lower(proof_body)?;
                let target = self.lowerer.lower_formula(target)?;
                if let Some(motive) =
                    self.find_rewrite_motive(&proof_body.proposition, &left, &right, &ty, &target)?
                {
                    return Ok(LoweredLegacyProof {
                        proof: HolDraftProof::EqualityElim {
                            proof_equality: Box::new(equality.proof),
                            motive,
                            proof_left: Box::new(proof_body.proof),
                        },
                        proposition: target,
                    });
                }
                if let Some(motive) =
                    self.find_rewrite_motive(&proof_body.proposition, &right, &left, &ty, &target)?
                {
                    let shifted_left = shift_under_new_binder(&left)?;
                    let symmetry_motive = CoreTerm::lambda(
                        ty.clone(),
                        CoreTerm::equality(ty.clone(), CoreTerm::Bound(0), shifted_left),
                    );
                    let symmetry = HolDraftProof::EqualityElim {
                        proof_equality: Box::new(equality.proof),
                        motive: symmetry_motive,
                        proof_left: Box::new(HolDraftProof::EqualityRefl((*left).clone())),
                    };
                    return Ok(LoweredLegacyProof {
                        proof: HolDraftProof::EqualityElim {
                            proof_equality: Box::new(symmetry),
                            motive,
                            proof_left: Box::new(proof_body.proof),
                        },
                        proposition: target,
                    });
                }
                if definitionally_equal(
                    self.environment.core.types(),
                    self.environment.core.constants(),
                    &self.lowerer.core_context(),
                    &proof_body.proposition,
                    &target,
                )? {
                    // Legacy simplification may normalize the rewritten goal
                    // back to the displayed source. Keep the explicit equality
                    // dependency with a constant motive instead of erasing a
                    // potentially trusted or incomplete theorem reference.
                    let motive =
                        CoreTerm::lambda(ty, shift_under_new_binder(&proof_body.proposition)?);
                    return Ok(LoweredLegacyProof {
                        proof: HolDraftProof::EqualityElim {
                            proof_equality: Box::new(equality.proof),
                            motive,
                            proof_left: Box::new(proof_body.proof),
                        },
                        proposition: target,
                    });
                }
                Err(LoweringError::new(format!(
                    "cannot reconstruct the legacy equality rewrite from `{:?}` to `{:?}` using `{:?} = {:?}` as a single explicit HOL motive",
                    proof_body.proposition, target, left, right
                )))
            }
            LegacyDraftProof::Convert { proof_body, target } => {
                let proof_body = self.lower(proof_body)?;
                let target = self.lowerer.lower_formula(target)?;
                self.lower_compatibility_conversion(proof_body, target)
            }
            LegacyDraftProof::ForallIntro {
                var,
                var_type,
                body,
            } => {
                let domain = self.lowerer.lower_type(var_type)?;
                let mut body_scope = self.under_term_binder(var, domain.clone())?;
                let body = body_scope.lower(body)?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::ForallIntro {
                        domain: domain.clone(),
                        body: Box::new(body.proof),
                    },
                    proposition: CoreTerm::forall(domain, body.proposition),
                })
            }
            LegacyDraftProof::ForallElim { proof_forall, arg } => {
                let proof_forall = self.lower(proof_forall)?;
                let normalized = self.normalize(&proof_forall.proposition)?;
                let CoreTerm::Forall { domain, body } = normalized else {
                    return Err(LoweringError::new(
                        "universal elimination needs a universal proof",
                    ));
                };
                let argument = self.lowerer.lower_term_at_type(arg, &domain)?;
                let proposition = instantiate_binder(
                    self.environment.core.types(),
                    self.environment.core.constants(),
                    &self.lowerer.core_context(),
                    &domain,
                    &body,
                    &argument,
                )?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::ForallElim {
                        proof_forall: Box::new(proof_forall.proof),
                        argument,
                    },
                    proposition,
                })
            }
            LegacyDraftProof::ExistsIntro {
                witness,
                proof_body,
                exists_formula,
            } => {
                let existential = self.lowerer.lower_formula(exists_formula)?;
                let normalized = self.normalize(&existential)?;
                let CoreTerm::Exists { domain, body } = normalized else {
                    return Err(LoweringError::new(
                        "existential introduction target is not existential",
                    ));
                };
                let witness = self.lowerer.lower_term_at_type(witness, &domain)?;
                let expected_body = instantiate_binder(
                    self.environment.core.types(),
                    self.environment.core.constants(),
                    &self.lowerer.core_context(),
                    &domain,
                    &body,
                    &witness,
                )?;
                let proof_body = self.lower(proof_body)?;
                ensure_same_proposition(
                    self.environment,
                    &self.lowerer,
                    &proof_body.proposition,
                    &expected_body,
                )?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::ExistsIntro {
                        domain,
                        body: *body,
                        witness,
                        proof_body: Box::new(proof_body.proof),
                    },
                    proposition: existential,
                })
            }
            LegacyDraftProof::ExistsElim {
                proof_exists,
                witness_name,
                hyp_name,
                body,
                target,
            } => {
                let proof_exists = self.lower(proof_exists)?;
                let normalized = self.normalize(&proof_exists.proposition)?;
                let CoreTerm::Exists {
                    domain,
                    body: exists_body,
                } = normalized
                else {
                    return Err(LoweringError::new(
                        "existential elimination needs an existential proof",
                    ));
                };
                let target = self.lowerer.lower_formula(target)?;
                let shifted_target = shift_under_new_binder(&target)?;
                let mut body_scope = self.under_term_binder(witness_name, domain)?;
                body_scope
                    .hypotheses
                    .push((hyp_name.clone(), (*exists_body).clone()));
                let body = body_scope.lower(body)?;
                ensure_same_proposition(
                    self.environment,
                    &body_scope.lowerer,
                    &body.proposition,
                    &shifted_target,
                )?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::ExistsElim {
                        proof_exists: Box::new(proof_exists.proof),
                        body: Box::new(body.proof),
                        target: target.clone(),
                    },
                    proposition: target,
                })
            }
            LegacyDraftProof::TheoremRef { name, subst } => {
                self.lower_theorem_reference(name, subst)
            }
            LegacyDraftProof::Classical { rule, args, target } => {
                self.lower_classical(rule.clone(), args, target)
            }
            LegacyDraftProof::Sorry { target } => {
                if !self.allow_incomplete {
                    return Err(LoweringError::new(
                        "legacy `sorry` cannot be lowered as checked HOL evidence",
                    ));
                }
                let target = self.lowerer.lower_formula(target)?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::Sorry {
                        target: target.clone(),
                    },
                    proposition: target,
                })
            }
            LegacyDraftProof::NatInd {
                var_name,
                target,
                base_case,
                step_var,
                ih_name,
                step_case,
            } => {
                self.lower_nat_induction(var_name, target, base_case, step_var, ih_name, step_case)
            }
            LegacyDraftProof::DataInd {
                var_name,
                data_name,
                target,
                arms,
            } => self.lower_data_induction(var_name, data_name, target, arms),
        }
    }

    fn lower_nat_induction(
        &mut self,
        var_name: &str,
        target: &Formula,
        base_case: &LegacyDraftProof,
        step_var: &str,
        ih_name: &str,
        step_case: &LegacyDraftProof,
    ) -> Result<LoweredLegacyProof, LoweringError> {
        let (scrutinee_index, scrutinee_type) =
            self.lowerer.resolve_local_term(var_name).ok_or_else(|| {
                LoweringError::new(format!(
                    "unknown Nat induction variable `{var_name}` during HOL lowering"
                ))
            })?;
        let nat = self.environment.prelude.nat_type();
        if scrutinee_type != nat {
            return Err(LoweringError::new(format!(
                "legacy induction variable `{var_name}` has core type `{scrutinee_type:?}`, not Nat"
            )));
        }
        let target = self.lowerer.lower_formula(target)?;
        let motive_body = abstract_local_term(&self.lowerer, &target, scrutinee_index)?;
        let motive = CoreTerm::lambda(nat.clone(), motive_body);
        let scrutinee = CoreTerm::Bound(scrutinee_index);

        let base_expected = self.normalize(&CoreTerm::apply(
            motive.clone(),
            CoreTerm::Constant(self.environment.prelude.zero()),
        ))?;
        let base_case = self.lower(base_case)?;
        ensure_same_proposition(
            self.environment,
            &self.lowerer,
            &base_case.proposition,
            &base_expected,
        )?;

        let mut step_scope = self.under_term_binder(step_var, nat.clone())?;
        let shifted_motive = shift_under_new_binder(&motive)?;
        let induction_hypothesis =
            step_scope.normalize(&CoreTerm::apply(shifted_motive.clone(), CoreTerm::Bound(0)))?;
        step_scope
            .hypotheses
            .push((ih_name.to_string(), induction_hypothesis));
        let step_expected = step_scope.normalize(&CoreTerm::apply(
            shifted_motive,
            CoreTerm::apply(
                CoreTerm::Constant(self.environment.prelude.successor()),
                CoreTerm::Bound(0),
            ),
        ))?;
        let step_case = step_scope.lower(step_case)?;
        ensure_same_proposition(
            self.environment,
            &step_scope.lowerer,
            &step_case.proposition,
            &step_expected,
        )?;

        Ok(LoweredLegacyProof {
            proof: HolDraftProof::Induction {
                datatype: self.environment.prelude.nat_constructor(),
                type_arguments: Vec::new(),
                motive,
                scrutinee,
                cases: vec![base_case.proof, step_case.proof],
            },
            proposition: target,
        })
    }

    fn lower_data_induction(
        &mut self,
        var_name: &str,
        data_name: &str,
        target: &Formula,
        arms: &[crate::DataIndArm],
    ) -> Result<LoweredLegacyProof, LoweringError> {
        let data = self.environment.data.get(data_name).ok_or_else(|| {
            LoweringError::new(format!(
                "unknown induction data type `{data_name}` during HOL lowering"
            ))
        })?;
        if arms.len() != data.source.ctors.len() {
            return Err(LoweringError::new(format!(
                "legacy induction over `{data_name}` needs {} arm(s), but got {}",
                data.source.ctors.len(),
                arms.len()
            )));
        }
        let (scrutinee_index, scrutinee_type) =
            self.lowerer.resolve_local_term(var_name).ok_or_else(|| {
                LoweringError::new(format!(
                    "unknown data induction variable `{var_name}` during HOL lowering"
                ))
            })?;
        let datatype_type = CoreType::constructor(data.datatype, Vec::new());
        if scrutinee_type != datatype_type {
            return Err(LoweringError::new(format!(
                "legacy induction variable `{var_name}` has core type `{scrutinee_type:?}`, not `{datatype_type:?}`"
            )));
        }
        let target = self.lowerer.lower_formula(target)?;
        let motive_body = abstract_local_term(&self.lowerer, &target, scrutinee_index)?;
        let motive = CoreTerm::lambda(datatype_type, motive_body);
        let scrutinee = CoreTerm::Bound(scrutinee_index);
        let mut cases = Vec::with_capacity(arms.len());

        for (((arm, constructor), constructor_id), constructor_index) in arms
            .iter()
            .zip(&data.source.ctors)
            .zip(&data.constructors)
            .zip(0usize..)
        {
            if arm.ctor != constructor.name {
                return Err(LoweringError::new(format!(
                    "legacy induction arm `{}` is out of order; expected `{}`",
                    arm.ctor, constructor.name
                )));
            }
            let recursive_indices = constructor
                .arg_types
                .iter()
                .enumerate()
                .filter_map(|(index, ty)| is_direct_recursive_type(ty, data_name).then_some(index))
                .collect::<Vec<_>>();
            if arm.arg_names.len() != constructor.arg_types.len()
                || arm.ih_names.len() != recursive_indices.len()
            {
                return Err(LoweringError::new(format!(
                    "legacy induction arm `{}` has inconsistent binder metadata",
                    arm.ctor
                )));
            }

            let mut arm_scope = self.clone();
            let mut shifted_motive = motive.clone();
            for (name, ty) in arm.arg_names.iter().zip(&constructor.arg_types).rev() {
                let ty = arm_scope.lowerer.lower_type(ty)?;
                arm_scope = arm_scope.under_term_binder(name, ty)?;
                shifted_motive = shift_under_new_binder(&shifted_motive)?;
            }
            let mut constructor_term = CoreTerm::Constant(*constructor_id);
            for field_index in 0..constructor.arg_types.len() {
                constructor_term =
                    CoreTerm::apply(constructor_term, CoreTerm::Bound(field_index as u32));
            }
            let case_expected =
                arm_scope.normalize(&CoreTerm::apply(shifted_motive.clone(), constructor_term))?;
            for (ih_name, recursive_index) in arm.ih_names.iter().zip(&recursive_indices).rev() {
                let induction_hypothesis = arm_scope.normalize(&CoreTerm::apply(
                    shifted_motive.clone(),
                    CoreTerm::Bound(*recursive_index as u32),
                ))?;
                arm_scope
                    .hypotheses
                    .push((ih_name.clone(), induction_hypothesis));
            }
            let case = arm_scope.lower(&arm.proof)?;
            ensure_same_proposition(
                self.environment,
                &arm_scope.lowerer,
                &case.proposition,
                &case_expected,
            )?;
            cases.push(case.proof);

            debug_assert_eq!(
                self.environment
                    .core
                    .inductives()
                    .declaration(data.datatype)
                    .and_then(|declaration| declaration.constructors.get(constructor_index))
                    .map(|metadata| metadata.constant),
                Some(*constructor_id)
            );
        }

        Ok(LoweredLegacyProof {
            proof: HolDraftProof::Induction {
                datatype: data.datatype,
                type_arguments: Vec::new(),
                motive,
                scrutinee,
                cases,
            },
            proposition: target,
        })
    }

    fn lower_theorem_reference(
        &mut self,
        name: &str,
        substitution: &SchemaSubst,
    ) -> Result<LoweredLegacyProof, LoweringError> {
        let registration = self
            .environment
            .theorems
            .iter()
            .find(|registration| registration.name == name)
            .ok_or_else(|| {
                LoweringError::new(format!(
                    "unknown compatibility theorem `{name}` in legacy proof"
                ))
            })?;
        let mut type_arguments = Vec::with_capacity(registration.type_parameters.len());
        for parameter in &registration.parameters {
            if matches!(parameter.kind, ParamKind::Type) {
                let argument = substitution.type_args.get(&parameter.name).ok_or_else(|| {
                    LoweringError::new(format!(
                        "legacy theorem `{name}` is missing type argument `{}`",
                        parameter.name
                    ))
                })?;
                type_arguments.push(self.lowerer.lower_type(argument)?);
            }
        }
        if type_arguments.len() != registration.type_parameters.len() {
            return Err(LoweringError::new(format!(
                "legacy theorem `{name}` has inconsistent type-parameter metadata"
            )));
        }

        let mut term_arguments = Vec::with_capacity(registration.parameter_types.len());
        let mut parameter_type_index = 0usize;
        for parameter in &registration.parameters {
            if matches!(parameter.kind, ParamKind::Type) {
                continue;
            }
            let schematic_type = &registration.parameter_types[parameter_type_index];
            parameter_type_index += 1;
            let expected = self.environment.core.types().instantiate_scheme(
                &registration.type_parameters,
                schematic_type,
                &type_arguments,
            )?;
            let argument = match &parameter.kind {
                ParamKind::Prop => {
                    let argument =
                        substitution
                            .formula_args
                            .get(&parameter.name)
                            .ok_or_else(|| {
                                LoweringError::new(format!(
                                    "legacy theorem `{name}` is missing proposition argument `{}`",
                                    parameter.name
                                ))
                            })?;
                    let argument = self.lowerer.lower_formula(argument)?;
                    self.expect_type(&argument, &expected, &parameter.name)?;
                    argument
                }
                ParamKind::Predicate(_) => {
                    let argument = substitution
                        .predicate_args
                        .get(&parameter.name)
                        .ok_or_else(|| {
                            LoweringError::new(format!(
                                "legacy theorem `{name}` is missing predicate argument `{}`",
                                parameter.name
                            ))
                        })?;
                    let term = match argument {
                        PredicateArg::Named(name) => Term::Var(name.clone()),
                        PredicateArg::Lambda { params, body } => Term::PredLambda {
                            params: params.clone(),
                            body: Box::new(body.clone()),
                        },
                    };
                    self.lowerer.lower_term_at_type(&term, &expected)?
                }
                ParamKind::Term(_) => {
                    let argument =
                        substitution.term_args.get(&parameter.name).ok_or_else(|| {
                            LoweringError::new(format!(
                                "legacy theorem `{name}` is missing term argument `{}`",
                                parameter.name
                            ))
                        })?;
                    self.lowerer.lower_term_at_type(argument, &expected)?
                }
                ParamKind::Type => unreachable!("type parameters were skipped"),
            };
            term_arguments.push(argument);
        }

        let context = self.lowerer.core_context();
        let statement = if self.allow_incomplete {
            self.environment
                .core
                .theorems()
                .instantiate_draft_statement(
                    self.environment.core.types(),
                    self.environment.core.constants(),
                    &context,
                    registration.theorem,
                    &type_arguments,
                    &term_arguments,
                )
        } else {
            self.environment.core.theorems().instantiate_statement(
                self.environment.core.types(),
                self.environment.core.constants(),
                &context,
                registration.theorem,
                &type_arguments,
                &term_arguments,
            )
        }
        .map_err(|error| LoweringError::new(error.message))?;
        Ok(LoweredLegacyProof {
            proof: HolDraftProof::TheoremRef {
                theorem: registration.theorem,
                type_arguments,
                term_arguments,
            },
            proposition: statement,
        })
    }

    fn find_rewrite_motive(
        &self,
        source: &CoreTerm,
        from: &CoreTerm,
        to: &CoreTerm,
        ty: &CoreType,
        target: &CoreTerm,
    ) -> Result<Option<CoreTerm>, LoweringError> {
        let shifted_source = shift_under_new_binder(source)?;
        let shifted_from = shift_under_new_binder(from)?;
        for body in replace_core_term_once(&shifted_source, &shifted_from, 0)? {
            let motive = CoreTerm::lambda(ty.clone(), body);
            let produced = CoreTerm::apply(motive.clone(), to.clone());
            if definitionally_equal(
                self.environment.core.types(),
                self.environment.core.constants(),
                &self.lowerer.core_context(),
                &produced,
                target,
            )? {
                return Ok(Some(motive));
            }
        }
        Ok(None)
    }

    fn lower_compatibility_conversion(
        &self,
        proof_body: LoweredLegacyProof,
        target: CoreTerm,
    ) -> Result<LoweredLegacyProof, LoweringError> {
        if definitionally_equal(
            self.environment.core.types(),
            self.environment.core.constants(),
            &self.lowerer.core_context(),
            &proof_body.proposition,
            &target,
        )? {
            return Ok(LoweredLegacyProof {
                proof: proof_body.proof,
                proposition: target,
            });
        }

        let (source_steps, source_normalized) =
            self.compatibility_arithmetic_path(&proof_body.proposition)?;
        let (target_steps, target_normalized) = self.compatibility_arithmetic_path(&target)?;
        if !definitionally_equal(
            self.environment.core.types(),
            self.environment.core.constants(),
            &self.lowerer.core_context(),
            &source_normalized,
            &target_normalized,
        )? {
            return Err(LoweringError::new(format!(
                "lowered legacy proof has proposition `{:?}`, but expected `{:?}`; checked arithmetic compatibility normalization reached `{:?}` and `{:?}`",
                proof_body.proposition, target, source_normalized, target_normalized
            )));
        }

        let mut proof = proof_body.proof;
        for step in &source_steps {
            let motive = self
                .find_rewrite_motive(
                    &step.before,
                    &step.rewrite.from,
                    &step.rewrite.to,
                    &step.rewrite.ty,
                    &step.after,
                )?
                .ok_or_else(|| {
                    LoweringError::new(
                        "could not reconstruct a forward checked arithmetic conversion motive",
                    )
                })?;
            proof = HolDraftProof::EqualityElim {
                proof_equality: Box::new(step.rewrite.proof.clone()),
                motive,
                proof_left: Box::new(proof),
            };
        }
        for step in target_steps.iter().rev() {
            let motive = self
                .find_rewrite_motive(
                    &step.after,
                    &step.rewrite.to,
                    &step.rewrite.from,
                    &step.rewrite.ty,
                    &step.before,
                )?
                .ok_or_else(|| {
                    LoweringError::new(
                        "could not reconstruct a reverse checked arithmetic conversion motive",
                    )
                })?;
            proof = HolDraftProof::EqualityElim {
                proof_equality: Box::new(symmetry_proof(
                    &step.rewrite.ty,
                    &step.rewrite.from,
                    step.rewrite.proof.clone(),
                )?),
                motive,
                proof_left: Box::new(proof),
            };
        }
        Ok(LoweredLegacyProof {
            proof,
            proposition: target,
        })
    }

    fn compatibility_arithmetic_path(
        &self,
        proposition: &CoreTerm,
    ) -> Result<(Vec<CompatibilityArithmeticStep>, CoreTerm), LoweringError> {
        const MAX_STEPS: usize = 16_384;

        let mut steps = Vec::new();
        let mut current = proposition.clone();
        loop {
            if steps.len() >= MAX_STEPS {
                return Err(LoweringError::new(
                    "checked arithmetic compatibility normalization exceeded its step limit",
                ));
            }
            if let Some(rewrite) = self.find_compatibility_arithmetic_rewrite(&current) {
                let shifted_current = shift_under_new_binder(&current)?;
                let shifted_from = shift_under_new_binder(&rewrite.from)?;
                let after = replace_core_term_once(&shifted_current, &shifted_from, 0)?
                    .into_iter()
                    .map(|body| {
                        instantiate_binder(
                            self.environment.core.types(),
                            self.environment.core.constants(),
                            &self.lowerer.core_context(),
                            &rewrite.ty,
                            &body,
                            &rewrite.to,
                        )
                        .map_err(LoweringError::from)
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .find(|candidate| candidate != &current)
                    .ok_or_else(|| {
                        LoweringError::new(
                            "checked arithmetic compatibility rewrite found no source occurrence",
                        )
                    })?;
                steps.push(CompatibilityArithmeticStep {
                    before: current,
                    after: after.clone(),
                    rewrite,
                });
                current = after;
                continue;
            }

            let normalized = self.normalize(&current)?;
            if normalized == current {
                return Ok((steps, current));
            }
            current = normalized;
        }
    }

    fn find_compatibility_arithmetic_rewrite(
        &self,
        proposition: &CoreTerm,
    ) -> Option<CompatibilityArithmeticRewrite> {
        let mut terms = Vec::new();
        collect_unbound_core_terms_postorder(proposition, &mut terms);
        terms.into_iter().find_map(|term| {
            let prelude = self.environment.prelude();
            let nat = prelude.nat_type();
            let zero = CoreTerm::Constant(prelude.zero());

            if let Some((left, right)) = binary_constant_application(&term, prelude.addition()) {
                let normalized_right = self.normalize(right).ok()?;
                if normalized_right == zero {
                    return Some(CompatibilityArithmeticRewrite {
                        ty: nat,
                        from: term.clone(),
                        to: left.clone(),
                        proof: compatibility_theorem_reference(
                            prelude.addition_zero_right(),
                            vec![left.clone()],
                        ),
                    });
                }
                if let Some(predecessor) =
                    unary_constant_application(&normalized_right, prelude.successor())
                {
                    return Some(CompatibilityArithmeticRewrite {
                        ty: nat,
                        from: term.clone(),
                        to: CoreTerm::apply(
                            CoreTerm::Constant(prelude.successor()),
                            apply2_core(prelude.addition(), left.clone(), predecessor.clone()),
                        ),
                        proof: compatibility_theorem_reference(
                            prelude.addition_successor_right(),
                            vec![left.clone(), predecessor.clone()],
                        ),
                    });
                }
            }
            if let Some((left, right)) =
                binary_constant_application(&term, prelude.multiplication())
            {
                let normalized_right = self.normalize(right).ok()?;
                if normalized_right == zero {
                    return Some(CompatibilityArithmeticRewrite {
                        ty: nat,
                        from: term.clone(),
                        to: zero.clone(),
                        proof: compatibility_theorem_reference(
                            prelude.multiplication_zero_right(),
                            vec![left.clone()],
                        ),
                    });
                }
                if let Some(predecessor) =
                    unary_constant_application(&normalized_right, prelude.successor())
                {
                    return Some(CompatibilityArithmeticRewrite {
                        ty: nat,
                        from: term.clone(),
                        to: apply2_core(
                            prelude.addition(),
                            left.clone(),
                            apply2_core(
                                prelude.multiplication(),
                                left.clone(),
                                predecessor.clone(),
                            ),
                        ),
                        proof: compatibility_theorem_reference(
                            prelude.multiplication_successor_right(),
                            vec![left.clone(), predecessor.clone()],
                        ),
                    });
                }
            }
            if let Some((left, right)) = binary_constant_application(&term, prelude.subtraction()) {
                let normalized_left = self.normalize(left).ok()?;
                let normalized_right = self.normalize(right).ok()?;
                if normalized_left == zero {
                    return Some(CompatibilityArithmeticRewrite {
                        ty: nat,
                        from: term.clone(),
                        to: zero,
                        proof: compatibility_theorem_reference(
                            prelude.subtraction_zero_left(),
                            vec![right.clone()],
                        ),
                    });
                }
                if let (Some(left_predecessor), Some(right_predecessor)) = (
                    unary_constant_application(&normalized_left, prelude.successor()),
                    unary_constant_application(&normalized_right, prelude.successor()),
                ) {
                    return Some(CompatibilityArithmeticRewrite {
                        ty: nat,
                        from: term.clone(),
                        to: apply2_core(
                            prelude.subtraction(),
                            left_predecessor.clone(),
                            right_predecessor.clone(),
                        ),
                        proof: compatibility_theorem_reference(
                            prelude.subtraction_successor_successor(),
                            vec![left_predecessor.clone(), right_predecessor.clone()],
                        ),
                    });
                }
            }
            None
        })
    }

    fn lower_classical(
        &mut self,
        rule: ClassicalRule,
        args: &[LegacyDraftProof],
        target: &Formula,
    ) -> Result<LoweredLegacyProof, LoweringError> {
        let target = self.lowerer.lower_formula(target)?;
        match rule {
            ClassicalRule::ExcludedMiddle => {
                if !args.is_empty() {
                    return Err(LoweringError::new(
                        "legacy excluded middle unexpectedly has proof arguments",
                    ));
                }
                let normalized = self.normalize(&target)?;
                let CoreTerm::Or(left, right) = normalized else {
                    return Err(LoweringError::new(
                        "legacy excluded middle target is not a disjunction",
                    ));
                };
                let CoreTerm::Implies(negated, falsehood) = *right else {
                    return Err(LoweringError::new(
                        "legacy excluded middle target has no negated right branch",
                    ));
                };
                if !matches!(*falsehood, CoreTerm::Falsity) {
                    return Err(LoweringError::new(
                        "legacy excluded middle target has a malformed negation",
                    ));
                }
                ensure_same_proposition(self.environment, &self.lowerer, &left, &negated)?;
                Ok(LoweredLegacyProof {
                    proof: HolDraftProof::ExcludedMiddle {
                        proposition: (*left).clone(),
                    },
                    proposition: target,
                })
            }
            ClassicalRule::DoubleNegationElim | ClassicalRule::ByContra => {
                if args.len() != 1 {
                    return Err(LoweringError::new(format!(
                        "legacy `{rule}` expects one proof argument"
                    )));
                }
                let proof_not_not = self.lower(&args[0])?;
                Ok(LoweredLegacyProof {
                    // The legacy by-contradiction node stores a complete proof
                    // of `not not P`; DNE is the extensionally identical core
                    // boundary and keeps the classical audit explicit.
                    proof: HolDraftProof::DoubleNegationElim {
                        proposition: target.clone(),
                        proof_not_not: Box::new(proof_not_not.proof),
                    },
                    proposition: target,
                })
            }
        }
    }

    fn normalize(&self, proposition: &CoreTerm) -> Result<CoreTerm, LoweringError> {
        Ok(normalize(
            self.environment.core.types(),
            self.environment.core.constants(),
            &self.lowerer.core_context(),
            proposition,
        )?)
    }

    fn expect_normalized_shape(
        &self,
        proposition: &CoreTerm,
        predicate: impl FnOnce(&CoreTerm) -> bool,
        message: &str,
    ) -> Result<(), LoweringError> {
        let normalized = self.normalize(proposition)?;
        if predicate(&normalized) {
            Ok(())
        } else {
            Err(LoweringError::new(message))
        }
    }

    fn expect_type(
        &self,
        term: &CoreTerm,
        expected: &CoreType,
        parameter: &str,
    ) -> Result<(), LoweringError> {
        let actual = self.lowerer.infer_core(term)?;
        if actual == *expected {
            Ok(())
        } else {
            Err(LoweringError::new(format!(
                "legacy theorem argument `{parameter}` has core type `{actual:?}`, but expected `{expected:?}`"
            )))
        }
    }

    fn under_term_binder(&self, name: &str, ty: CoreType) -> Result<Self, LoweringError> {
        let mut scope = self.clone();
        scope.lowerer.bind_term_parameter(name.to_string(), ty)?;
        for (_, proposition) in &mut scope.hypotheses {
            *proposition = shift_under_new_binder(proposition)?;
        }
        Ok(scope)
    }
}

fn ensure_same_proposition(
    environment: &CompatibilityElaborator,
    lowerer: &CompatibilityLowerer<'_>,
    actual: &CoreTerm,
    expected: &CoreTerm,
) -> Result<(), LoweringError> {
    if definitionally_equal(
        environment.core.types(),
        environment.core.constants(),
        &lowerer.core_context(),
        actual,
        expected,
    )? {
        Ok(())
    } else {
        Err(LoweringError::new(format!(
            "lowered legacy proof has proposition `{actual:?}`, but expected `{expected:?}`"
        )))
    }
}

/// Abstract one resolved local de Bruijn variable while preserving every
/// other surrounding binder. `instantiate_term_parameters_under_binders`
/// performs the capture-safe traversal for us; the argument vector merely
/// renames the selected old index to the new index zero and shifts its peers.
fn abstract_local_term(
    lowerer: &CompatibilityLowerer<'_>,
    term: &CoreTerm,
    selected: u32,
) -> Result<CoreTerm, LoweringError> {
    let depth = lowerer.core_context().depth();
    let selected = usize::try_from(selected)
        .map_err(|_| LoweringError::new("selected binder index does not fit in memory"))?;
    if selected >= depth {
        return Err(LoweringError::new(format!(
            "cannot abstract binder `{selected}` from context depth `{depth}`"
        )));
    }
    let arguments = (0..depth)
        .rev()
        .map(|old_index| {
            if old_index == selected {
                Ok(CoreTerm::Bound(0))
            } else {
                let shifted = old_index
                    .checked_add(1)
                    .ok_or_else(|| LoweringError::new("binder index overflow"))?;
                Ok(CoreTerm::Bound(u32::try_from(shifted).map_err(|_| {
                    LoweringError::new("binder index exceeds HOL core limits")
                })?))
            }
        })
        .collect::<Result<Vec<_>, LoweringError>>()?;
    Ok(instantiate_term_parameters_under_binders(
        term, &arguments, 0,
    )?)
}

fn replace_core_term_once(
    term: &CoreTerm,
    needle: &CoreTerm,
    binder_depth: u32,
) -> Result<Vec<CoreTerm>, LoweringError> {
    let mut replacements = Vec::new();
    if term == needle {
        replacements.push(CoreTerm::Bound(binder_depth));
    }
    let nested = |body: &CoreTerm,
                  wrap: &dyn Fn(CoreTerm) -> CoreTerm|
     -> Result<Vec<CoreTerm>, LoweringError> {
        let nested_needle = shift_under_new_binder(needle)?;
        let nested_depth = binder_depth
            .checked_add(1)
            .ok_or_else(|| LoweringError::new("rewrite binder depth overflow"))?;
        Ok(replace_core_term_once(body, &nested_needle, nested_depth)?
            .into_iter()
            .map(wrap)
            .collect())
    };
    let unary = |body: &CoreTerm,
                 wrap: &dyn Fn(CoreTerm) -> CoreTerm|
     -> Result<Vec<CoreTerm>, LoweringError> {
        Ok(replace_core_term_once(body, needle, binder_depth)?
            .into_iter()
            .map(wrap)
            .collect())
    };
    let binary = |left: &CoreTerm,
                  right: &CoreTerm,
                  wrap: &dyn Fn(CoreTerm, CoreTerm) -> CoreTerm|
     -> Result<Vec<CoreTerm>, LoweringError> {
        let mut results = replace_core_term_once(left, needle, binder_depth)?
            .into_iter()
            .map(|replacement| wrap(replacement, right.clone()))
            .collect::<Vec<_>>();
        results.extend(
            replace_core_term_once(right, needle, binder_depth)?
                .into_iter()
                .map(|replacement| wrap(left.clone(), replacement)),
        );
        Ok(results)
    };

    let mut descendants = match term {
        CoreTerm::Bound(_)
        | CoreTerm::Constant(_)
        | CoreTerm::TypeApplication { .. }
        | CoreTerm::EmptySet { .. }
        | CoreTerm::UniverseSet { .. }
        | CoreTerm::Truth
        | CoreTerm::Falsity => Vec::new(),
        CoreTerm::Lambda {
            parameter_type,
            body,
        } => nested(body, &|body| CoreTerm::lambda(parameter_type.clone(), body))?,
        CoreTerm::Apply { function, argument } => binary(function, argument, &CoreTerm::apply)?,
        CoreTerm::Pair(left, right) => binary(left, right, &CoreTerm::pair)?,
        CoreTerm::First(pair) => unary(pair, &CoreTerm::first)?,
        CoreTerm::Second(pair) => unary(pair, &CoreTerm::second)?,
        CoreTerm::SingletonSet(element) => unary(element, &CoreTerm::singleton_set)?,
        CoreTerm::SetUnion(left, right) => binary(left, right, &CoreTerm::set_union)?,
        CoreTerm::SetIntersection(left, right) => binary(left, right, &CoreTerm::set_intersection)?,
        CoreTerm::SetDifference(left, right) => binary(left, right, &CoreTerm::set_difference)?,
        CoreTerm::SetComplement(set) => unary(set, &CoreTerm::set_complement)?,
        CoreTerm::SetProduct(left, right) => binary(left, right, &CoreTerm::set_product)?,
        CoreTerm::Powerset { element_type, set } => {
            unary(set, &|set| CoreTerm::powerset(element_type.clone(), set))?
        }
        CoreTerm::SetBuilder { element_type, body } => nested(body, &|body| {
            CoreTerm::set_builder(element_type.clone(), body)
        })?,
        CoreTerm::Membership {
            element_type,
            element,
            set,
        } => binary(element, set, &|element, set| {
            CoreTerm::membership(element_type.clone(), element, set)
        })?,
        CoreTerm::Subset {
            element_type,
            left,
            right,
        } => binary(left, right, &|left, right| {
            CoreTerm::subset(element_type.clone(), left, right)
        })?,
        CoreTerm::And(left, right) => binary(left, right, &CoreTerm::and)?,
        CoreTerm::Or(left, right) => binary(left, right, &CoreTerm::or)?,
        CoreTerm::Implies(left, right) => binary(left, right, &CoreTerm::implies)?,
        CoreTerm::Equality { ty, left, right } => binary(left, right, &|left, right| {
            CoreTerm::equality(ty.clone(), left, right)
        })?,
        CoreTerm::Forall { domain, body } => {
            nested(body, &|body| CoreTerm::forall(domain.clone(), body))?
        }
        CoreTerm::Exists { domain, body } => {
            nested(body, &|body| CoreTerm::exists(domain.clone(), body))?
        }
    };
    replacements.append(&mut descendants);
    Ok(replacements)
}

fn compatibility_theorem_reference(
    theorem: TheoremId,
    term_arguments: Vec<CoreTerm>,
) -> HolDraftProof {
    HolDraftProof::TheoremRef {
        theorem,
        type_arguments: Vec::new(),
        term_arguments,
    }
}

fn apply2_core(function: ConstantId, left: CoreTerm, right: CoreTerm) -> CoreTerm {
    CoreTerm::apply(CoreTerm::apply(CoreTerm::Constant(function), left), right)
}

fn binary_constant_application(
    term: &CoreTerm,
    constant: ConstantId,
) -> Option<(&CoreTerm, &CoreTerm)> {
    let CoreTerm::Apply {
        function,
        argument: right,
    } = term
    else {
        return None;
    };
    let CoreTerm::Apply {
        function,
        argument: left,
    } = function.as_ref()
    else {
        return None;
    };
    matches!(function.as_ref(), CoreTerm::Constant(found) if *found == constant)
        .then_some((left.as_ref(), right.as_ref()))
}

fn unary_constant_application(term: &CoreTerm, constant: ConstantId) -> Option<&CoreTerm> {
    let CoreTerm::Apply { function, argument } = term else {
        return None;
    };
    matches!(function.as_ref(), CoreTerm::Constant(found) if *found == constant)
        .then_some(argument.as_ref())
}

fn symmetry_proof(
    ty: &CoreType,
    left: &CoreTerm,
    proof_equality: HolDraftProof,
) -> Result<HolDraftProof, LoweringError> {
    let shifted_left = shift_under_new_binder(left)?;
    Ok(HolDraftProof::EqualityElim {
        proof_equality: Box::new(proof_equality),
        motive: CoreTerm::lambda(
            ty.clone(),
            CoreTerm::equality(ty.clone(), CoreTerm::Bound(0), shifted_left),
        ),
        proof_left: Box::new(HolDraftProof::EqualityRefl(left.clone())),
    })
}

/// Collect only terms whose free variables are available in the current proof
/// context. Arithmetic below a term/formula binder is handled when the legacy
/// proof introduces that binder, so a synthesized theorem reference never
/// escapes the scope of one of its arguments.
fn collect_unbound_core_terms_postorder(term: &CoreTerm, terms: &mut Vec<CoreTerm>) {
    let unary = |child: &CoreTerm, terms: &mut Vec<CoreTerm>| {
        collect_unbound_core_terms_postorder(child, terms)
    };
    let binary = |left: &CoreTerm, right: &CoreTerm, terms: &mut Vec<CoreTerm>| {
        collect_unbound_core_terms_postorder(left, terms);
        collect_unbound_core_terms_postorder(right, terms);
    };
    match term {
        CoreTerm::Bound(_)
        | CoreTerm::Constant(_)
        | CoreTerm::TypeApplication { .. }
        | CoreTerm::EmptySet { .. }
        | CoreTerm::UniverseSet { .. }
        | CoreTerm::Truth
        | CoreTerm::Falsity => {}
        CoreTerm::Lambda { .. }
        | CoreTerm::SetBuilder { .. }
        | CoreTerm::Forall { .. }
        | CoreTerm::Exists { .. } => {}
        CoreTerm::Apply { function, argument } => binary(function, argument, terms),
        CoreTerm::Pair(left, right)
        | CoreTerm::SetUnion(left, right)
        | CoreTerm::SetIntersection(left, right)
        | CoreTerm::SetDifference(left, right)
        | CoreTerm::SetProduct(left, right)
        | CoreTerm::And(left, right)
        | CoreTerm::Or(left, right)
        | CoreTerm::Implies(left, right) => binary(left, right, terms),
        CoreTerm::First(pair) | CoreTerm::Second(pair) => unary(pair, terms),
        CoreTerm::SingletonSet(element) => unary(element, terms),
        CoreTerm::SetComplement(set) => unary(set, terms),
        CoreTerm::Powerset { set, .. } => unary(set, terms),
        CoreTerm::Membership { element, set, .. } => binary(element, set, terms),
        CoreTerm::Subset { left, right, .. } | CoreTerm::Equality { left, right, .. } => {
            binary(left, right, terms)
        }
    }
    terms.push(term.clone());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{EvidenceStatus, StatementFragment};
    use crate::hol::terms::{definitionally_equal, infer_type, normalize, TermContext};
    use crate::hol::theorems::HolTheoremStatus;
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
    fn registered_generic_list_coexists_with_the_legacy_monomorphic_surface() {
        let mut elaborator = CompatibilityElaborator::new().expect("compatibility elaborator");
        let installed = elaborator
            .install_builtin_list_v1()
            .expect("install registered generic List");
        assert_eq!(
            elaborator
                .libraries()
                .list_v1()
                .expect("registered package"),
            &installed
        );

        let legacy_list = elaborator
            .declare_data(&list_definition())
            .expect("legacy monomorphic List remains available");
        assert_ne!(legacy_list, installed.lists.datatype);
        assert_eq!(elaborator.core().types().resolve("List"), Some(legacy_list));
        assert_eq!(
            elaborator.core().types().resolve("@library.list.v1.List"),
            Some(installed.lists.datatype)
        );

        let legacy_nil = elaborator
            .core()
            .constants()
            .resolve("nil")
            .expect("legacy nil");
        let lowered_nil = elaborator
            .lower_term(&Term::Var("nil".to_string()))
            .expect("legacy nil remains the surface meaning");
        assert_eq!(lowered_nil, CoreTerm::Constant(legacy_nil));
        assert_ne!(legacy_nil, installed.lists.nil);
    }

    #[test]
    fn registered_cardinality_installs_its_dependency_without_surface_aliases() {
        let mut elaborator = CompatibilityElaborator::new().expect("compatibility elaborator");
        let installed = elaborator
            .install_builtin_cardinality_v1()
            .expect("install registered cardinality transport");
        assert_eq!(elaborator.libraries().packages().len(), 2);
        assert!(elaborator.libraries().list_v1().is_some());
        assert_eq!(
            elaborator
                .libraries()
                .cardinality_v1()
                .expect("registered cardinality package"),
            &installed
        );

        let names = super::super::CardinalityTransportNames::under_namespace(
            super::super::BUILTIN_CARDINALITY_V1_NAMESPACE,
        );
        assert_eq!(
            elaborator.core().constants().resolve(&names.map),
            Some(installed.cardinality.map)
        );
        let reserved_error = elaborator
            .lower_term(&Term::Var(names.map))
            .expect_err("reserved package names stay outside the legacy scope");
        assert!(reserved_error.message.contains("unknown compatibility"));

        let legacy_map = elaborator
            .declare_function("map", &[Type::Nat], &Type::Nat)
            .expect("a legacy surface symbol can retain the unqualified name");
        let lowered = elaborator
            .lower_term(&Term::App("map".to_string(), vec![Term::Zero]))
            .expect("legacy map application");
        assert_eq!(
            lowered,
            CoreTerm::apply(
                CoreTerm::Constant(legacy_map),
                CoreTerm::Constant(elaborator.prelude().zero()),
            )
        );
        assert_ne!(legacy_map, installed.cardinality.map);
    }

    #[test]
    fn registered_finite_package_keeps_has_card_outside_the_legacy_surface() {
        let mut elaborator = CompatibilityElaborator::new().expect("compatibility elaborator");
        let installed = elaborator
            .install_builtin_finite_v1()
            .expect("install registered finite package");
        assert_eq!(elaborator.libraries().packages().len(), 2);
        assert!(elaborator.libraries().list_v1().is_some());
        assert_eq!(
            elaborator
                .libraries()
                .finite_v1()
                .expect("registered finite package"),
            &installed
        );

        let names = super::super::FiniteEnumerationNames::under_namespace(
            super::super::BUILTIN_FINITE_V1_NAMESPACE,
        );
        assert_eq!(
            elaborator.core().constants().resolve(&names.has_card),
            Some(installed.finite.has_card)
        );
        let reserved_error = elaborator
            .lower_term(&Term::Var(names.has_card))
            .expect_err("reserved HasCard stays outside the legacy scope");
        assert!(reserved_error.message.contains("unknown compatibility"));

        let legacy_has_card = elaborator
            .declare_predicate("HasCard", &[])
            .expect("legacy surface can retain the unqualified name");
        let lowered = elaborator
            .lower_formula(&Formula::Atom("HasCard".to_string()))
            .expect("lower legacy HasCard atom");
        assert_eq!(lowered, CoreTerm::Constant(legacy_has_card));
        assert_ne!(legacy_has_card, installed.finite.has_card);
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
    fn theorem_templates_lower_all_status_boundaries_transactionally() {
        let mut elaborator = CompatibilityElaborator::new().expect("compatibility elaborator");
        let proposition_parameter = Param {
            name: "P".to_string(),
            kind: ParamKind::Prop,
        };
        let identity_statement = Formula::Implies(
            Box::new(Formula::Atom("P".to_string())),
            Box::new(Formula::Atom("P".to_string())),
        );
        let (identity, identity_receipt) = elaborator
            .declare_checked_theorem(
                "prop_identity",
                std::slice::from_ref(&proposition_parameter),
                &identity_statement,
                HolDraftProof::ImpIntro {
                    premise: CoreTerm::Bound(0),
                    body: Box::new(HolDraftProof::Hypothesis(0)),
                },
            )
            .expect("checked proposition template");
        assert_eq!(identity_receipt.status(), EvidenceStatus::Checked);
        assert_eq!(
            identity_receipt.proof().required_fragment(),
            StatementFragment::Prop
        );
        assert_eq!(
            elaborator
                .core()
                .theorems()
                .declaration(identity)
                .map(|declaration| declaration.status),
            Some(HolTheoremStatus::Checked)
        );

        let axiom_parameters = vec![
            Param {
                name: "A".to_string(),
                kind: ParamKind::Type,
            },
            Param {
                name: "x".to_string(),
                kind: ParamKind::Term(Type::Named("A".to_string())),
            },
        ];
        let (axiom, axiom_receipt) = elaborator
            .declare_trusted_axiom(
                "trusted_refl",
                &axiom_parameters,
                &Formula::Eq(var("x"), var("x")),
            )
            .expect("typed trusted axiom");
        assert_eq!(axiom_receipt.status(), EvidenceStatus::TrustedAxiom);
        assert_eq!(
            axiom_receipt.proof().required_fragment(),
            StatementFragment::FirstOrder
        );
        assert_eq!(
            elaborator
                .core()
                .theorems()
                .declaration(axiom)
                .map(|declaration| declaration.status),
            Some(HolTheoremStatus::TrustedAxiom)
        );

        let (incomplete, incomplete_receipt) = elaborator
            .declare_incomplete_theorem(
                "exercise",
                std::slice::from_ref(&proposition_parameter),
                &Formula::Atom("P".to_string()),
                HolDraftProof::Sorry {
                    target: CoreTerm::Bound(0),
                },
            )
            .expect("typed incomplete theorem");
        assert_eq!(incomplete_receipt.status(), EvidenceStatus::Incomplete);
        let incomplete_declaration = elaborator
            .core()
            .theorems()
            .declaration(incomplete)
            .expect("stored incomplete declaration");
        assert_eq!(incomplete_declaration.status, HolTheoremStatus::Incomplete);
        assert!(incomplete_declaration.incomplete_draft.is_some());

        let before = elaborator.clone();
        let error = elaborator
            .declare_checked_theorem(
                "bad_theorem",
                &[],
                &Formula::False,
                HolDraftProof::TruthIntro,
            )
            .expect_err("ill-typed evidence must reject transactionally");
        assert!(error.message.contains("expected"));
        assert_eq!(elaborator, before);
        elaborator
            .declare_trusted_axiom("bad_theorem", &[], &Formula::False)
            .expect("failed proof did not reserve theorem name");
    }

    #[test]
    fn lowers_legacy_propositional_proofs_references_classical_rules_and_holes() {
        let mut elaborator = CompatibilityElaborator::new().expect("compatibility elaborator");
        let p = Param {
            name: "P".to_string(),
            kind: ParamKind::Prop,
        };
        let identity_statement = Formula::Implies(
            Box::new(Formula::Atom("P".to_string())),
            Box::new(Formula::Atom("P".to_string())),
        );
        let identity_proof = LegacyDraftProof::ImpIntro {
            hyp_name: "h".to_string(),
            hyp_formula: Formula::Atom("P".to_string()),
            body: Box::new(LegacyDraftProof::Hyp("h".to_string())),
        };
        let (identity, identity_receipt) = elaborator
            .declare_legacy_checked_theorem(
                "legacy_prop_identity",
                std::slice::from_ref(&p),
                &identity_statement,
                &identity_proof,
            )
            .expect("legacy implication proof");
        assert_eq!(identity_receipt.status(), EvidenceStatus::Checked);
        assert_eq!(
            elaborator
                .core()
                .theorems()
                .declaration(identity)
                .map(|declaration| declaration.status),
            Some(HolTheoremStatus::Checked)
        );

        let q = Param {
            name: "Q".to_string(),
            kind: ParamKind::Prop,
        };
        let conjunction = Formula::And(
            Box::new(Formula::Atom("P".to_string())),
            Box::new(Formula::Atom("Q".to_string())),
        );
        let swapped = Formula::And(
            Box::new(Formula::Atom("Q".to_string())),
            Box::new(Formula::Atom("P".to_string())),
        );
        elaborator
            .declare_legacy_checked_theorem(
                "legacy_and_comm",
                &[p.clone(), q],
                &Formula::Implies(Box::new(conjunction.clone()), Box::new(swapped)),
                &LegacyDraftProof::ImpIntro {
                    hyp_name: "h".to_string(),
                    hyp_formula: conjunction,
                    body: Box::new(LegacyDraftProof::AndIntro(
                        Box::new(LegacyDraftProof::AndElimRight(Box::new(
                            LegacyDraftProof::Hyp("h".to_string()),
                        ))),
                        Box::new(LegacyDraftProof::AndElimLeft(Box::new(
                            LegacyDraftProof::Hyp("h".to_string()),
                        ))),
                    )),
                },
            )
            .expect("legacy conjunction proof");

        let mut identity_substitution = SchemaSubst::default();
        identity_substitution
            .formula_args
            .insert("P".to_string(), Formula::Atom("P".to_string()));
        let (_, facade_receipt) = elaborator
            .declare_legacy_checked_theorem(
                "legacy_identity_facade",
                std::slice::from_ref(&p),
                &identity_statement,
                &LegacyDraftProof::TheoremRef {
                    name: "legacy_prop_identity".to_string(),
                    subst: identity_substitution,
                },
            )
            .expect("legacy theorem reference");
        assert_eq!(facade_receipt.status(), EvidenceStatus::Checked);
        assert_eq!(facade_receipt.proof().direct_dependencies().len(), 1);

        let generic_parameters = vec![
            Param {
                name: "A".to_string(),
                kind: ParamKind::Type,
            },
            Param {
                name: "R".to_string(),
                kind: ParamKind::Predicate(vec![Type::Named("A".to_string())]),
            },
            Param {
                name: "x".to_string(),
                kind: ParamKind::Term(Type::Named("A".to_string())),
            },
        ];
        let generic_atom = Formula::PredApp("R".to_string(), vec![var("x")]);
        let generic_statement = Formula::Implies(
            Box::new(generic_atom.clone()),
            Box::new(generic_atom.clone()),
        );
        elaborator
            .declare_legacy_checked_theorem(
                "legacy_generic_predicate_identity",
                &generic_parameters,
                &generic_statement,
                &LegacyDraftProof::ImpIntro {
                    hyp_name: "h".to_string(),
                    hyp_formula: generic_atom,
                    body: Box::new(LegacyDraftProof::Hyp("h".to_string())),
                },
            )
            .expect("generic legacy predicate theorem");
        let nat_reflexive = Formula::Eq(Term::Zero, Term::Zero);
        let concrete_statement = Formula::Implies(
            Box::new(nat_reflexive.clone()),
            Box::new(nat_reflexive.clone()),
        );
        let mut generic_substitution = SchemaSubst::default();
        generic_substitution
            .type_args
            .insert("A".to_string(), Type::Nat);
        generic_substitution.predicate_args.insert(
            "R".to_string(),
            PredicateArg::Lambda {
                params: vec![crate::LambdaParam {
                    name: "n".to_string(),
                    ty: Some(Type::Nat),
                }],
                body: Formula::Eq(var("n"), var("n")),
            },
        );
        generic_substitution
            .term_args
            .insert("x".to_string(), Term::Zero);
        let (_, generic_instance_receipt) = elaborator
            .declare_legacy_checked_theorem(
                "legacy_generic_nat_instance",
                &[],
                &concrete_statement,
                &LegacyDraftProof::TheoremRef {
                    name: "legacy_generic_predicate_identity".to_string(),
                    subst: generic_substitution,
                },
            )
            .expect("explicit type/predicate/term theorem substitution");
        assert_eq!(
            generic_instance_receipt.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );

        elaborator
            .declare_trusted_axiom("legacy_trusted_truth", &[], &Formula::True)
            .expect("trusted truth fixture");
        let (_, trusted_user_receipt) = elaborator
            .declare_legacy_checked_theorem(
                "legacy_trusted_user",
                &[],
                &Formula::True,
                &LegacyDraftProof::TheoremRef {
                    name: "legacy_trusted_truth".to_string(),
                    subst: SchemaSubst::default(),
                },
            )
            .expect("trusted theorem reference");
        assert_eq!(trusted_user_receipt.proof().axiom_dependencies().len(), 1);

        let excluded_middle = Formula::Or(
            Box::new(Formula::Atom("P".to_string())),
            Box::new(Formula::Implies(
                Box::new(Formula::Atom("P".to_string())),
                Box::new(Formula::False),
            )),
        );
        let (_, classical_receipt) = elaborator
            .declare_legacy_checked_theorem(
                "legacy_em",
                std::slice::from_ref(&p),
                &excluded_middle,
                &LegacyDraftProof::Classical {
                    rule: ClassicalRule::ExcludedMiddle,
                    args: Vec::new(),
                    target: excluded_middle.clone(),
                },
            )
            .expect("explicit legacy classical evidence");
        assert!(classical_receipt
            .proof()
            .transitive_features()
            .contains(&crate::hol::ProofFeature::Classical));

        let (_, incomplete_receipt) = elaborator
            .declare_legacy_incomplete_theorem(
                "legacy_exercise",
                std::slice::from_ref(&p),
                &Formula::Atom("P".to_string()),
                &LegacyDraftProof::Sorry {
                    target: Formula::Atom("P".to_string()),
                },
            )
            .expect("legacy draft hole");
        assert_eq!(incomplete_receipt.status(), EvidenceStatus::Incomplete);
        let mut incomplete_substitution = SchemaSubst::default();
        incomplete_substitution
            .formula_args
            .insert("P".to_string(), Formula::Atom("P".to_string()));
        let (_, incomplete_user_receipt) = elaborator
            .declare_legacy_incomplete_theorem(
                "legacy_exercise_user",
                std::slice::from_ref(&p),
                &Formula::Atom("P".to_string()),
                &LegacyDraftProof::TheoremRef {
                    name: "legacy_exercise".to_string(),
                    subst: incomplete_substitution,
                },
            )
            .expect("draft-to-draft theorem reference");
        assert_eq!(
            incomplete_user_receipt
                .proof()
                .incomplete_dependencies()
                .len(),
            1
        );

        let forall_refl = Formula::Forall {
            var: "n".to_string(),
            var_type: Type::Nat,
            body: Box::new(Formula::Eq(var("n"), var("n"))),
        };
        elaborator
            .declare_legacy_checked_theorem(
                "legacy_forall_refl",
                &[],
                &forall_refl,
                &LegacyDraftProof::ForallIntro {
                    var: "n".to_string(),
                    var_type: Type::Nat,
                    body: Box::new(LegacyDraftProof::EqRefl(var("n"))),
                },
            )
            .expect("legacy universal introduction");
        elaborator
            .declare_legacy_checked_theorem(
                "legacy_zero_refl",
                &[],
                &Formula::Eq(Term::Zero, Term::Zero),
                &LegacyDraftProof::ForallElim {
                    proof_forall: Box::new(LegacyDraftProof::TheoremRef {
                        name: "legacy_forall_refl".to_string(),
                        subst: SchemaSubst::default(),
                    }),
                    arg: Term::Zero,
                },
            )
            .expect("legacy universal elimination");

        let exists_zero = Formula::Exists {
            var: "n".to_string(),
            var_type: Type::Nat,
            body: Box::new(Formula::Eq(var("n"), Term::Zero)),
        };
        elaborator
            .declare_legacy_checked_theorem(
                "legacy_exists_zero",
                &[],
                &exists_zero,
                &LegacyDraftProof::ExistsIntro {
                    witness: Term::Zero,
                    proof_body: Box::new(LegacyDraftProof::EqRefl(Term::Zero)),
                    exists_formula: exists_zero.clone(),
                },
            )
            .expect("legacy existential introduction");
        let exists_truth = Formula::Exists {
            var: "n".to_string(),
            var_type: Type::Nat,
            body: Box::new(Formula::True),
        };
        elaborator
            .declare_legacy_checked_theorem(
                "legacy_exists_elim",
                &[],
                &Formula::Implies(Box::new(exists_truth.clone()), Box::new(Formula::True)),
                &LegacyDraftProof::ImpIntro {
                    hyp_name: "h".to_string(),
                    hyp_formula: exists_truth,
                    body: Box::new(LegacyDraftProof::ExistsElim {
                        proof_exists: Box::new(LegacyDraftProof::Hyp("h".to_string())),
                        witness_name: "n".to_string(),
                        hyp_name: "hn".to_string(),
                        body: Box::new(LegacyDraftProof::TrueIntro),
                        target: Formula::True,
                    }),
                },
            )
            .expect("legacy existential elimination");

        let nat_parameter = Param {
            name: "n".to_string(),
            kind: ParamKind::Term(Type::Nat),
        };
        let nat_reflexivity = Formula::Eq(var("n"), var("n"));
        let (_, nat_induction_receipt) = elaborator
            .declare_legacy_checked_theorem(
                "legacy_nat_induction",
                std::slice::from_ref(&nat_parameter),
                &nat_reflexivity,
                &LegacyDraftProof::NatInd {
                    var_name: "n".to_string(),
                    target: nat_reflexivity.clone(),
                    base_case: Box::new(LegacyDraftProof::EqRefl(Term::Zero)),
                    step_var: "k".to_string(),
                    ih_name: "ih".to_string(),
                    step_case: Box::new(LegacyDraftProof::EqRefl(Term::Succ(Box::new(var("k"))))),
                },
            )
            .expect("legacy Nat induction");
        assert!(nat_induction_receipt
            .proof()
            .direct_features()
            .contains(&crate::hol::ProofFeature::Induction));

        let equality_parameters = vec![
            Param {
                name: "x".to_string(),
                kind: ParamKind::Term(Type::Nat),
            },
            Param {
                name: "y".to_string(),
                kind: ParamKind::Term(Type::Nat),
            },
        ];
        let xy = Formula::Eq(var("x"), var("y"));
        elaborator
            .declare_legacy_checked_theorem(
                "legacy_eq_symm_forward",
                &equality_parameters,
                &Formula::Implies(
                    Box::new(xy.clone()),
                    Box::new(Formula::Eq(var("y"), var("x"))),
                ),
                &LegacyDraftProof::ImpIntro {
                    hyp_name: "h".to_string(),
                    hyp_formula: xy.clone(),
                    body: Box::new(LegacyDraftProof::EqSubst {
                        eq_proof: Box::new(LegacyDraftProof::Hyp("h".to_string())),
                        proof_body: Box::new(LegacyDraftProof::EqRefl(var("x"))),
                        target: Formula::Eq(var("y"), var("x")),
                    }),
                },
            )
            .expect("forward equality motive reconstruction");
        elaborator
            .declare_legacy_checked_theorem(
                "legacy_eq_reverse_rewrite",
                &equality_parameters,
                &Formula::Implies(Box::new(xy.clone()), Box::new(xy.clone())),
                &LegacyDraftProof::ImpIntro {
                    hyp_name: "h".to_string(),
                    hyp_formula: xy.clone(),
                    body: Box::new(LegacyDraftProof::EqSubst {
                        eq_proof: Box::new(LegacyDraftProof::Hyp("h".to_string())),
                        proof_body: Box::new(LegacyDraftProof::EqRefl(var("y"))),
                        target: xy,
                    }),
                },
            )
            .expect("reverse equality motive reconstruction");

        elaborator
            .declare_data(&list_definition())
            .expect("List for data induction");
        let list_parameter = Param {
            name: "l".to_string(),
            kind: ParamKind::Term(Type::Named("List".to_string())),
        };
        let list_reflexivity = Formula::Eq(var("l"), var("l"));
        elaborator
            .declare_legacy_checked_theorem(
                "legacy_list_induction",
                std::slice::from_ref(&list_parameter),
                &list_reflexivity,
                &LegacyDraftProof::DataInd {
                    var_name: "l".to_string(),
                    data_name: "List".to_string(),
                    target: list_reflexivity.clone(),
                    arms: vec![
                        crate::DataIndArm {
                            ctor: "nil".to_string(),
                            arg_names: Vec::new(),
                            ih_names: Vec::new(),
                            proof: LegacyDraftProof::EqRefl(var("nil")),
                        },
                        crate::DataIndArm {
                            ctor: "cons".to_string(),
                            arg_names: vec!["head".to_string(), "tail".to_string()],
                            ih_names: vec!["ih".to_string()],
                            proof: LegacyDraftProof::EqRefl(Term::App(
                                "cons".to_string(),
                                vec![var("head"), var("tail")],
                            )),
                        },
                    ],
                },
            )
            .expect("legacy data induction");

        let before = elaborator.clone();
        let unsupported = LegacyDraftProof::EqSubst {
            eq_proof: Box::new(LegacyDraftProof::EqRefl(Term::Zero)),
            proof_body: Box::new(LegacyDraftProof::TrueIntro),
            target: Formula::False,
        };
        assert!(elaborator
            .declare_legacy_checked_theorem("invalid_rewrite", &[], &Formula::False, &unsupported,)
            .is_err());
        assert_eq!(elaborator, before);
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
