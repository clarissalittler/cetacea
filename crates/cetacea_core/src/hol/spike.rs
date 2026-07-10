//! Deliberately small name-resolving elaborator for the H3 stop/go spike.
//!
//! This is not the compatibility parser. It is a compact facade that lets the
//! three architectural examples use names and checked declarations while still
//! lowering immediately to resolved core IDs. It also ties kernel proof audits
//! to fragment receipts so example labels cannot be asserted by hand.

use std::fmt;

use super::fragments::{
    classify_statement, proof_features_from_audit, DeclarationId, DeclarationReceipt,
    FragmentError, FragmentMetadata, StatementFragment,
};
use super::inductive::{InductiveError, InductiveSignature, InductiveSpec};
use super::proofs::{
    check_hol_proof_with_inductives_audit, HolDraftProof, HolKernelProof, HolProofContext,
    ProofError,
};
use super::recursion::{RecursionError, RecursionSignature, StructuralDefinitionSpec};
use super::terms::{infer_type, ConstantId, CoreTerm, TermContext, TermError, TermSignature};
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedSpikeTheorem {
    pub proof: HolKernelProof,
    pub receipt: DeclarationReceipt,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SpikeElaborator {
    types: TypeSignature,
    constants: TermSignature,
    inductives: InductiveSignature,
    recursion: RecursionSignature,
    fragments: FragmentMetadata,
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
        let id =
            self.recursion
                .declare(&self.types, &mut self.constants, &self.inductives, spec)?;
        self.fragments.mark_structurally_recursive_constant(id);
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

    pub fn check_theorem<'a>(
        &self,
        id: DeclarationId,
        statement: &CoreTerm,
        draft: HolDraftProof,
        dependencies: impl IntoIterator<Item = &'a DeclarationReceipt>,
    ) -> Result<CheckedSpikeTheorem, SpikeError> {
        let proof = HolKernelProof::try_from(draft)?;
        let audit = check_hol_proof_with_inductives_audit(
            &self.types,
            &self.constants,
            &self.inductives,
            &TermContext::new(),
            &HolProofContext::new(),
            &proof,
            statement,
        )?;
        let fragment = self.classify(statement)?;
        let receipt = DeclarationReceipt::checked(
            id,
            fragment,
            proof_features_from_audit(audit),
            dependencies,
        );
        Ok(CheckedSpikeTheorem { proof, receipt })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{ProofFeature, ReceiptPolicy, TeachingProfile};
    use crate::hol::inductive::{InductiveConstructorSpec, InductiveFieldType};

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
        let theorem = elaborator
            .check_theorem(DeclarationId(0), &CoreTerm::Truth, proof, [])
            .expect("checked spike theorem");
        assert_eq!(
            theorem.receipt.proof().direct_features(),
            &std::collections::BTreeSet::from([ProofFeature::Induction])
        );
        assert_eq!(
            theorem.receipt.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert!(ReceiptPolicy::new(TeachingProfile::FirstOrderInductive)
            .check(&theorem.receipt)
            .is_empty());
        assert!(!ReceiptPolicy::new(TeachingProfile::FirstOrder)
            .check(&theorem.receipt)
            .is_empty());
    }
}
