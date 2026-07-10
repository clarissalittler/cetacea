//! Deliberately small name-resolving elaborator for the H3 stop/go spike.
//!
//! This is not the compatibility parser. It is a compact facade that lets the
//! three architectural examples use names and checked declarations while still
//! lowering immediately to resolved core IDs. It also ties kernel proof audits
//! to fragment receipts so example labels cannot be asserted by hand.

use std::collections::HashMap;
use std::fmt;

use super::fragments::{
    classify_statement, proof_features_from_audit, DeclarationId, DeclarationReceipt,
    FragmentError, FragmentMetadata, ProofFeature, StatementFragment,
};
use super::inductive::{InductiveError, InductiveSignature, InductiveSpec};
use super::proofs::{HolDraftProof, HolKernelProof, ProofError};
use super::recursion::{RecursionError, RecursionSignature, StructuralDefinitionSpec};
use super::terms::{
    infer_type, term_constant_dependencies, ConstantId, CoreTerm, TermContext, TermError,
    TermSignature,
};
use super::theorems::{HolTheoremSignature, TheoremError, TheoremId};
use super::types::{CoreType, TypeConstructorId, TypeError, TypeParameter, TypeSignature};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpikeError {
    pub message: String,
}

impl SpikeError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for SpikeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for SpikeError {}

macro_rules! from_error {
    ($error:ty) => {
        impl From<$error> for SpikeError {
            fn from(error: $error) -> Self {
                Self::new(error.message)
            }
        }
    };
}

from_error!(TypeError);
from_error!(TermError);
from_error!(InductiveError);
from_error!(RecursionError);
from_error!(ProofError);
from_error!(FragmentError);
from_error!(TheoremError);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpikeElaborator {
    types: TypeSignature,
    constants: TermSignature,
    inductives: InductiveSignature,
    recursion: RecursionSignature,
    fragments: FragmentMetadata,
    theorems: HolTheoremSignature,
    theorem_receipts: HashMap<TheoremId, DeclarationReceipt>,
    definition_receipts: HashMap<ConstantId, DeclarationReceipt>,
    next_receipt_id: u32,
}

impl Default for SpikeElaborator {
    fn default() -> Self {
        Self {
            types: TypeSignature::new(),
            constants: TermSignature::new(),
            inductives: InductiveSignature::new(),
            recursion: RecursionSignature::new(),
            fragments: FragmentMetadata::new(),
            theorems: HolTheoremSignature::new(),
            theorem_receipts: HashMap::new(),
            definition_receipts: HashMap::new(),
            next_receipt_id: 0,
        }
    }
}

impl SpikeElaborator {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn types(&self) -> &TypeSignature {
        &self.types
    }

    pub fn constants(&self) -> &TermSignature {
        &self.constants
    }

    pub fn inductives(&self) -> &InductiveSignature {
        &self.inductives
    }

    pub fn recursion(&self) -> &RecursionSignature {
        &self.recursion
    }

    pub fn fragment_metadata(&self) -> &FragmentMetadata {
        &self.fragments
    }

    pub fn theorems(&self) -> &HolTheoremSignature {
        &self.theorems
    }

    pub fn theorem_receipt(&self, id: TheoremId) -> Option<&DeclarationReceipt> {
        self.theorem_receipts.get(&id)
    }

    pub fn definition_receipt(&self, id: ConstantId) -> Option<&DeclarationReceipt> {
        self.definition_receipts.get(&id)
    }

    pub fn declare_base_type(
        &mut self,
        name: impl Into<String>,
        first_order: bool,
    ) -> Result<TypeConstructorId, SpikeError> {
        Ok(self.types.declare(name, 0, first_order)?)
    }

    pub fn declare_constant(
        &mut self,
        name: impl Into<String>,
        ty: CoreType,
    ) -> Result<ConstantId, SpikeError> {
        Ok(self.constants.declare(&self.types, name, ty)?)
    }

    pub fn declare_polymorphic_constant(
        &mut self,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        ty: CoreType,
    ) -> Result<ConstantId, SpikeError> {
        Ok(self
            .constants
            .declare_polymorphic(&self.types, name, type_parameters, ty)?)
    }

    pub fn declare_inductive(
        &mut self,
        spec: InductiveSpec,
    ) -> Result<TypeConstructorId, SpikeError> {
        let id = self
            .inductives
            .declare(&mut self.types, &mut self.constants, spec)?;
        self.fragments.mark_inductive_type(id);
        Ok(id)
    }

    pub fn declare_structural_definition(
        &mut self,
        spec: StructuralDefinitionSpec,
    ) -> Result<ConstantId, SpikeError> {
        let referenced_constants = spec
            .arms
            .iter()
            .flat_map(|arm| term_constant_dependencies(&arm.body))
            .collect::<std::collections::BTreeSet<_>>();
        let dependency_receipts = referenced_constants
            .iter()
            .filter_map(|constant| self.definition_receipts.get(constant).cloned())
            .collect::<Vec<_>>();
        let fragment = structural_definition_fragment(
            &self.types,
            spec.datatype,
            &spec.datatype_arguments,
            &spec.fixed_parameter_types,
            &spec.result_type,
        )?;
        let receipt_id = DeclarationId(self.next_receipt_id);
        let next_receipt_id = self
            .next_receipt_id
            .checked_add(1)
            .ok_or_else(|| SpikeError::new("too many spike declaration receipts"))?;
        let id =
            self.recursion
                .declare(&self.types, &mut self.constants, &self.inductives, spec)?;
        self.fragments.mark_structurally_recursive_constant(id);
        let receipt = DeclarationReceipt::checked(
            receipt_id,
            fragment,
            [ProofFeature::StructuralRecursion],
            dependency_receipts.iter(),
        );
        self.definition_receipts.insert(id, receipt);
        self.next_receipt_id = next_receipt_id;
        Ok(id)
    }

    pub fn resolve_type(&self, name: &str) -> Result<TypeConstructorId, SpikeError> {
        self.types
            .resolve(name)
            .ok_or_else(|| SpikeError::new(format!("unknown type constructor `{name}`")))
    }

    pub fn resolve_constant(&self, name: &str) -> Result<ConstantId, SpikeError> {
        self.constants
            .resolve(name)
            .ok_or_else(|| SpikeError::new(format!("unknown constant `{name}`")))
    }

    pub fn named_constant(
        &self,
        name: &str,
        type_arguments: Vec<CoreType>,
    ) -> Result<CoreTerm, SpikeError> {
        let id = self.resolve_constant(name)?;
        let term = if type_arguments.is_empty() {
            CoreTerm::Constant(id)
        } else {
            CoreTerm::instantiate_constant(id, type_arguments)
        };
        infer_type(&self.types, &self.constants, &TermContext::new(), &term)?;
        Ok(term)
    }

    pub fn named_application(
        &self,
        name: &str,
        type_arguments: Vec<CoreType>,
        arguments: impl IntoIterator<Item = CoreTerm>,
    ) -> Result<CoreTerm, SpikeError> {
        Ok(arguments
            .into_iter()
            .fold(self.named_constant(name, type_arguments)?, CoreTerm::apply))
    }

    pub fn classify(&self, statement: &CoreTerm) -> Result<StatementFragment, SpikeError> {
        Ok(classify_statement(
            &self.types,
            &self.constants,
            &TermContext::new(),
            &self.fragments,
            statement,
        )?)
    }

    /// Check, store, and receipt a named theorem. The direct theorem
    /// dependencies come from `TheoremRef` nodes in checked evidence; callers
    /// cannot provide or omit that list.
    pub fn declare_theorem(
        &mut self,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        statement: CoreTerm,
        draft: HolDraftProof,
    ) -> Result<(TheoremId, DeclarationReceipt), SpikeError> {
        let proof = HolKernelProof::try_from(draft)?;
        let mut staged_theorems = self.theorems.clone();
        let theorem = staged_theorems.check_and_declare(
            &self.types,
            &self.constants,
            &self.inductives,
            name,
            type_parameters,
            statement.clone(),
            proof,
        )?;
        let declaration = staged_theorems
            .declaration(theorem)
            .expect("a newly checked theorem is stored");
        let mut dependency_receipts = declaration
            .direct_dependencies
            .iter()
            .map(|dependency| {
                self.theorem_receipts
                    .get(dependency)
                    .cloned()
                    .ok_or_else(|| {
                        SpikeError::new(format!(
                            "checked theorem dependency `{}` has no receipt",
                            dependency.0
                        ))
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        dependency_receipts.extend(
            declaration
                .direct_constant_dependencies
                .iter()
                .filter_map(|constant| self.definition_receipts.get(constant).cloned()),
        );
        let fragment = self.classify(&statement)?;
        let receipt_id = DeclarationId(self.next_receipt_id);
        let next_receipt_id = self
            .next_receipt_id
            .checked_add(1)
            .ok_or_else(|| SpikeError::new("too many spike declaration receipts"))?;
        let receipt = DeclarationReceipt::checked(
            receipt_id,
            fragment,
            proof_features_from_audit(declaration.audit.clone()),
            dependency_receipts.iter(),
        );
        self.theorems = staged_theorems;
        self.theorem_receipts.insert(theorem, receipt.clone());
        self.next_receipt_id = next_receipt_id;
        Ok((theorem, receipt))
    }
}

fn structural_definition_fragment(
    types: &TypeSignature,
    datatype: TypeConstructorId,
    datatype_arguments: &[CoreType],
    fixed_parameters: &[CoreType],
    result: &CoreType,
) -> Result<StatementFragment, SpikeError> {
    let datatype = CoreType::constructor(datatype, datatype_arguments.to_vec());
    if first_order_scheme_status(types, &datatype)? != super::types::FirstOrderStatus::FirstOrder
        || fixed_parameters.iter().any(|parameter| {
            first_order_scheme_status(types, parameter).ok()
                != Some(super::types::FirstOrderStatus::FirstOrder)
        })
        || !first_order_symbol_result(types, result)?
    {
        Ok(StatementFragment::HigherOrder)
    } else {
        Ok(StatementFragment::FirstOrderInductive)
    }
}

/// Classify the least fragment of a schematic definition. An unconstrained
/// parameter can later receive a higher-order argument, but that concrete use
/// is classified from the checked theorem term. Treating parameters as
/// first-order placeholders here avoids tainting every first-order instance of
/// an otherwise parametric definition.
fn first_order_scheme_status(
    types: &TypeSignature,
    ty: &CoreType,
) -> Result<super::types::FirstOrderStatus, SpikeError> {
    fn narrow_parameters(ty: &CoreType) -> CoreType {
        match ty {
            CoreType::Prop => CoreType::Prop,
            CoreType::Parameter(parameter) => {
                CoreType::Parameter(TypeParameter::first_order(parameter.id.0))
            }
            CoreType::Constructor { id, arguments } => {
                CoreType::constructor(*id, arguments.iter().map(narrow_parameters).collect())
            }
            CoreType::Arrow(domain, codomain) => {
                CoreType::arrow(narrow_parameters(domain), narrow_parameters(codomain))
            }
            CoreType::Product(left, right) => {
                CoreType::product(narrow_parameters(left), narrow_parameters(right))
            }
        }
    }

    Ok(types.first_order_status(&narrow_parameters(ty))?)
}

fn first_order_symbol_result(types: &TypeSignature, result: &CoreType) -> Result<bool, SpikeError> {
    match result {
        CoreType::Prop => Ok(true),
        CoreType::Arrow(domain, codomain) => Ok(first_order_scheme_status(types, domain)?
            == super::types::FirstOrderStatus::FirstOrder
            && first_order_symbol_result(types, codomain)?),
        _ => {
            Ok(first_order_scheme_status(types, result)?
                == super::types::FirstOrderStatus::FirstOrder)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{ProofFeature, ReceiptPolicy, TeachingProfile};
    use crate::hol::inductive::{InductiveConstructorSpec, InductiveFieldType};
    use crate::hol::recursion::StructuralArmSpec;

    #[test]
    fn named_spike_elaboration_produces_checked_induction_receipts() {
        let mut elaborator = SpikeElaborator::new();
        let nat_id = elaborator.declare_base_type("Nat", true).expect("Nat");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let parameter = TypeParameter::any(0);
        let list = elaborator
            .declare_inductive(InductiveSpec::new(
                "List",
                vec![parameter],
                vec![
                    InductiveConstructorSpec::new("nil", Vec::new()),
                    InductiveConstructorSpec::new(
                        "cons",
                        vec![
                            InductiveFieldType::existing(CoreType::Parameter(parameter)),
                            InductiveFieldType::Recursive,
                        ],
                    ),
                ],
            ))
            .expect("List");
        let list_nat = CoreType::constructor(list, vec![nat.clone()]);
        let nil = elaborator
            .named_constant("nil", vec![nat.clone()])
            .expect("nil Nat");
        let proof = HolDraftProof::Induction {
            datatype: list,
            type_arguments: vec![nat],
            motive: CoreTerm::lambda(list_nat, CoreTerm::Truth),
            scrutinee: nil,
            cases: vec![HolDraftProof::TruthIntro, HolDraftProof::TruthIntro],
        };
        let (_, theorem) = elaborator
            .declare_theorem("anonymous_induction", Vec::new(), CoreTerm::Truth, proof)
            .expect("checked spike theorem");
        assert_eq!(
            theorem.proof().direct_features(),
            &std::collections::BTreeSet::from([ProofFeature::Induction])
        );
        assert_eq!(
            theorem.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert!(ReceiptPolicy::new(TeachingProfile::FirstOrderInductive)
            .check(&theorem)
            .is_empty());
        assert!(!ReceiptPolicy::new(TeachingProfile::FirstOrder)
            .check(&theorem)
            .is_empty());

        let nil_again = elaborator
            .named_constant("nil", vec![CoreType::constructor(nat_id, Vec::new())])
            .expect("nil Nat");
        let (inductive_source, _) = elaborator
            .declare_theorem(
                "inductive_source",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::Induction {
                    datatype: list,
                    type_arguments: vec![CoreType::constructor(nat_id, Vec::new())],
                    motive: CoreTerm::lambda(
                        CoreType::constructor(
                            list,
                            vec![CoreType::constructor(nat_id, Vec::new())],
                        ),
                        CoreTerm::Truth,
                    ),
                    scrutinee: nil_again,
                    cases: vec![HolDraftProof::TruthIntro, HolDraftProof::TruthIntro],
                },
            )
            .expect("stored induction theorem");
        let (_, facade_receipt) = elaborator
            .declare_theorem(
                "first_order_facade",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TheoremRef {
                    theorem: inductive_source,
                    type_arguments: Vec::new(),
                },
            )
            .expect("stored facade theorem");
        assert!(facade_receipt.proof().direct_features().is_empty());
        assert_eq!(
            facade_receipt.proof().transitive_features(),
            &std::collections::BTreeSet::from([ProofFeature::Induction])
        );
        assert!(!ReceiptPolicy::new(TeachingProfile::FirstOrder)
            .check(&facade_receipt)
            .is_empty());

        let nil_id = elaborator.resolve_constant("nil").expect("nil id");
        let cons_id = elaborator.resolve_constant("cons").expect("cons id");
        let always = elaborator
            .declare_structural_definition(StructuralDefinitionSpec {
                name: "AlwaysNat".to_string(),
                type_parameters: Vec::new(),
                datatype: list,
                datatype_arguments: vec![CoreType::constructor(nat_id, Vec::new())],
                fixed_parameter_types: Vec::new(),
                result_type: CoreType::Prop,
                arms: vec![
                    StructuralArmSpec::new(nil_id, CoreTerm::Truth),
                    StructuralArmSpec::new(cons_id, CoreTerm::Truth),
                ],
            })
            .expect("AlwaysNat");
        let always_nil = CoreTerm::apply(
            CoreTerm::Constant(always),
            elaborator
                .named_constant("nil", vec![CoreType::constructor(nat_id, Vec::new())])
                .expect("nil Nat"),
        );
        let always_receipt_id = elaborator
            .definition_receipt(always)
            .expect("stored definition receipt")
            .id();
        let (_, computed_receipt) = elaborator
            .declare_theorem(
                "always_nil",
                Vec::new(),
                always_nil.clone(),
                HolDraftProof::TruthIntro,
            )
            .expect("computed structural theorem");
        assert!(computed_receipt
            .proof()
            .transitive_features()
            .contains(&ProofFeature::StructuralRecursion));
        assert_eq!(
            computed_receipt.proof().direct_dependencies(),
            &std::collections::BTreeSet::from([always_receipt_id])
        );

        // The recursive definition occurs only in discarded proof evidence,
        // not in the stored statement. Evidence scanning must still discover
        // the dependency.
        let (_, hidden_receipt) = elaborator
            .declare_theorem(
                "hidden_structural_use",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::OrElim {
                    proof_or: Box::new(HolDraftProof::OrIntroLeft {
                        proof_left: Box::new(HolDraftProof::TruthIntro),
                        right: always_nil,
                    }),
                    left_case: Box::new(HolDraftProof::TruthIntro),
                    right_case: Box::new(HolDraftProof::TruthIntro),
                    target: CoreTerm::Truth,
                },
            )
            .expect("proof-only structural dependency");
        assert_eq!(
            hidden_receipt.proof().direct_dependencies(),
            &std::collections::BTreeSet::from([always_receipt_id])
        );
        assert!(hidden_receipt
            .proof()
            .transitive_features()
            .contains(&ProofFeature::StructuralRecursion));
    }

    #[test]
    fn stored_theorem_receipts_discover_transitive_refs_automatically() {
        let mut elaborator = SpikeElaborator::new();
        let (base, base_receipt) = elaborator
            .declare_theorem(
                "base",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TruthIntro,
            )
            .expect("base theorem");
        let (middle, middle_receipt) = elaborator
            .declare_theorem(
                "middle",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TheoremRef {
                    theorem: base,
                    type_arguments: Vec::new(),
                },
            )
            .expect("middle theorem");
        let (_, leaf_receipt) = elaborator
            .declare_theorem(
                "leaf",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TheoremRef {
                    theorem: middle,
                    type_arguments: Vec::new(),
                },
            )
            .expect("leaf theorem");
        assert!(base_receipt.proof().direct_dependencies().is_empty());
        assert_eq!(
            middle_receipt.proof().direct_dependencies(),
            &std::collections::BTreeSet::from([base_receipt.id()])
        );
        assert_eq!(
            leaf_receipt.proof().direct_dependencies(),
            &std::collections::BTreeSet::from([middle_receipt.id()])
        );
        assert_eq!(
            leaf_receipt.proof().transitive_dependencies(),
            &std::collections::BTreeSet::from([base_receipt.id(), middle_receipt.id()])
        );
    }
}
