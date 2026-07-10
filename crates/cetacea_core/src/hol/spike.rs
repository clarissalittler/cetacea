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
    EvidenceStatus, FragmentError, FragmentMetadata, ProofFeature, StatementFragment,
};
use super::inductive::{InductiveError, InductiveSignature, InductiveSpec};
use super::proofs::{HolDraftProof, HolKernelProof, HolProofAudit, ProofError};
use super::recursion::{RecursionError, RecursionSignature, StructuralDefinitionSpec};
use super::terms::{
    infer_type, term_constant_dependencies, ConstantId, CoreTerm, TermContext, TermError,
    TermSignature,
};
use super::theorems::{HolTheoremSignature, HolTheoremStatus, TheoremError, TheoremId};
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

    fn theorem_dependency_receipts(
        &self,
        audit: &HolProofAudit,
    ) -> Result<Vec<DeclarationReceipt>, SpikeError> {
        self.validate_theorem_reference_audit(audit)?;
        audit
            .theorem_references()
            .iter()
            .map(|reference| self.theorem_instance_receipt(reference))
            .collect()
    }

    fn validate_theorem_reference_audit(&self, audit: &HolProofAudit) -> Result<(), SpikeError> {
        let traced = audit
            .theorem_references()
            .iter()
            .map(|reference| reference.theorem())
            .collect::<std::collections::BTreeSet<_>>();
        if &traced != audit.theorem_dependencies() {
            Err(SpikeError::new(
                "checked theorem reference audit is inconsistent with dependency IDs",
            ))
        } else {
            Ok(())
        }
    }

    fn theorem_instance_receipt(
        &self,
        reference: &super::proofs::HolTheoremReferenceAudit,
    ) -> Result<DeclarationReceipt, SpikeError> {
        let base_receipt = self
            .theorem_receipts
            .get(&reference.theorem())
            .ok_or_else(|| {
                SpikeError::new(format!(
                    "theorem dependency `{}` has no receipt",
                    reference.theorem().0
                ))
            })?;
        let declaration = self
            .theorems
            .declaration(reference.theorem())
            .ok_or_else(|| {
                SpikeError::new(format!(
                    "theorem dependency `{}` has no declaration",
                    reference.theorem().0
                ))
            })?;
        let status_matches = matches!(
            (declaration.status, base_receipt.status()),
            (HolTheoremStatus::Checked, EvidenceStatus::Checked)
                | (HolTheoremStatus::Incomplete, EvidenceStatus::Incomplete)
                | (HolTheoremStatus::TrustedAxiom, EvidenceStatus::TrustedAxiom)
        );
        if !status_matches {
            return Err(SpikeError::new(
                "theorem declaration and receipt statuses are inconsistent",
            ));
        }
        self.validate_theorem_reference_audit(&declaration.audit)?;

        let mut dependencies = declaration
            .audit
            .theorem_references()
            .iter()
            .map(|nested| {
                let nested = nested.specialize_outer_parameters(
                    &self.types,
                    &declaration.type_parameters,
                    declaration.term_parameters.len(),
                    reference.type_arguments(),
                    reference.term_arguments(),
                    reference.term_context(),
                )?;
                self.theorem_instance_receipt(&nested)
            })
            .collect::<Result<Vec<_>, SpikeError>>()?;
        dependencies.extend(
            declaration
                .direct_constant_dependencies
                .iter()
                .filter_map(|constant| self.definition_receipts.get(constant).cloned()),
        );
        let fragment = classify_statement(
            &self.types,
            &self.constants,
            reference.term_context(),
            &self.fragments,
            reference.instantiated_statement(),
        )?;
        let receipt = match declaration.status {
            HolTheoremStatus::Checked => DeclarationReceipt::checked(
                base_receipt.id(),
                fragment,
                proof_features_from_audit(declaration.audit.clone()),
                dependencies.iter(),
            ),
            HolTheoremStatus::Incomplete => DeclarationReceipt::incomplete_with_dependencies(
                base_receipt.id(),
                fragment,
                proof_features_from_audit(declaration.audit.clone()),
                dependencies.iter(),
            ),
            HolTheoremStatus::TrustedAxiom => DeclarationReceipt::trusted_axiom_with_dependencies(
                base_receipt.id(),
                fragment,
                dependencies.iter(),
            ),
        };
        Ok(receipt)
    }

    pub fn declare_base_type(
        &mut self,
        name: impl Into<String>,
        first_order: bool,
    ) -> Result<TypeConstructorId, SpikeError> {
        Ok(self.types.declare(name, 0, first_order)?)
    }

    pub fn declare_legacy_set_type(
        &mut self,
        name: impl Into<String>,
    ) -> Result<TypeConstructorId, SpikeError> {
        Ok(self.types.declare_legacy_set(name)?)
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

    pub fn declare_transparent_definition(
        &mut self,
        name: impl Into<String>,
        ty: CoreType,
        body: CoreTerm,
    ) -> Result<ConstantId, SpikeError> {
        self.declare_polymorphic_transparent_definition(name, Vec::new(), ty, body)
    }

    /// Check and receipt a conservative nonrecursive abbreviation. The
    /// definition receipt itself is fragment-neutral: concrete uses are
    /// delta-normalized before classification, while dependencies of the body
    /// still propagate transitively.
    pub fn declare_polymorphic_transparent_definition(
        &mut self,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        ty: CoreType,
        body: CoreTerm,
    ) -> Result<ConstantId, SpikeError> {
        let referenced_constants = term_constant_dependencies(&body);
        let dependency_receipts = referenced_constants
            .iter()
            .filter_map(|constant| self.definition_receipts.get(constant).cloned())
            .collect::<Vec<_>>();
        let receipt_id = DeclarationId(self.next_receipt_id);
        let next_receipt_id = self
            .next_receipt_id
            .checked_add(1)
            .ok_or_else(|| SpikeError::new("too many spike declaration receipts"))?;
        let id = self.constants.declare_polymorphic_transparent_definition(
            &self.types,
            name,
            type_parameters,
            ty,
            body,
        )?;
        let receipt = DeclarationReceipt::checked(
            receipt_id,
            StatementFragment::Prop,
            [],
            dependency_receipts.iter(),
        );
        self.definition_receipts.insert(id, receipt);
        self.next_receipt_id = next_receipt_id;
        Ok(id)
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
            // A definition has no proposition of its own. Its concrete use is
            // normalized and classified at the use site, while recursion and
            // every transitive dependency remain visible through the receipt.
            // In particular, an implementation helper may accept an arrow
            // without making a fully saturated first-order client HOL.
            StatementFragment::Prop,
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
        self.declare_theorem_with_parameters(name, type_parameters, Vec::new(), statement, draft)
    }

    /// Check, store, and receipt a theorem template with explicit rank-one
    /// term/symbol parameters. Parameters are in declaration order; the last
    /// parameter is de Bruijn index zero in the open statement and evidence.
    pub fn declare_theorem_with_parameters(
        &mut self,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        term_parameters: Vec<CoreType>,
        statement: CoreTerm,
        draft: HolDraftProof,
    ) -> Result<(TheoremId, DeclarationReceipt), SpikeError> {
        let proof = HolKernelProof::try_from(draft)?;
        let mut staged_theorems = self.theorems.clone();
        let theorem = staged_theorems.check_and_declare_with_parameters(
            &self.types,
            &self.constants,
            &self.inductives,
            name,
            type_parameters,
            term_parameters.clone(),
            statement.clone(),
            proof,
        )?;
        let declaration = staged_theorems
            .declaration(theorem)
            .expect("a newly checked theorem is stored");
        let mut dependency_receipts = self.theorem_dependency_receipts(&declaration.audit)?;
        dependency_receipts.extend(
            declaration
                .direct_constant_dependencies
                .iter()
                .filter_map(|constant| self.definition_receipts.get(constant).cloned()),
        );
        let term_context = term_parameters
            .into_iter()
            .fold(TermContext::new(), TermContext::with_bound);
        let fragment = classify_statement(
            &self.types,
            &self.constants,
            &term_context,
            &self.fragments,
            &statement,
        )?;
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

    pub fn declare_incomplete_theorem(
        &mut self,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        statement: CoreTerm,
        draft: HolDraftProof,
    ) -> Result<(TheoremId, DeclarationReceipt), SpikeError> {
        self.declare_incomplete_theorem_with_parameters(
            name,
            type_parameters,
            Vec::new(),
            statement,
            draft,
        )
    }

    /// Type-check and retain a theorem draft while keeping it outside the
    /// kernel evidence boundary. Hole and dependency status is derived from
    /// the draft rather than supplied by the caller.
    pub fn declare_incomplete_theorem_with_parameters(
        &mut self,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        term_parameters: Vec<CoreType>,
        statement: CoreTerm,
        draft: HolDraftProof,
    ) -> Result<(TheoremId, DeclarationReceipt), SpikeError> {
        let mut staged_theorems = self.theorems.clone();
        let theorem = staged_theorems.check_and_declare_incomplete_with_parameters(
            &self.types,
            &self.constants,
            &self.inductives,
            name,
            type_parameters,
            term_parameters.clone(),
            statement.clone(),
            draft,
        )?;
        let declaration = staged_theorems
            .declaration(theorem)
            .expect("a newly checked incomplete theorem is stored");
        let mut dependency_receipts = self.theorem_dependency_receipts(&declaration.audit)?;
        dependency_receipts.extend(
            declaration
                .direct_constant_dependencies
                .iter()
                .filter_map(|constant| self.definition_receipts.get(constant).cloned()),
        );
        let term_context = term_parameters
            .into_iter()
            .fold(TermContext::new(), TermContext::with_bound);
        let fragment = classify_statement(
            &self.types,
            &self.constants,
            &term_context,
            &self.fragments,
            &statement,
        )?;
        let receipt_id = DeclarationId(self.next_receipt_id);
        let next_receipt_id = self
            .next_receipt_id
            .checked_add(1)
            .ok_or_else(|| SpikeError::new("too many spike declaration receipts"))?;
        let receipt = DeclarationReceipt::incomplete_with_dependencies(
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

    pub fn declare_trusted_axiom(
        &mut self,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        statement: CoreTerm,
    ) -> Result<(TheoremId, DeclarationReceipt), SpikeError> {
        self.declare_trusted_axiom_with_parameters(name, type_parameters, Vec::new(), statement)
    }

    /// Store an explicitly trusted theorem template. Its statement is fully
    /// type-checked, but there is deliberately no proof; the receipt status
    /// makes the axiom and every transitive use policy-visible.
    pub fn declare_trusted_axiom_with_parameters(
        &mut self,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        term_parameters: Vec<CoreType>,
        statement: CoreTerm,
    ) -> Result<(TheoremId, DeclarationReceipt), SpikeError> {
        let mut staged_theorems = self.theorems.clone();
        let theorem = staged_theorems.declare_trusted_axiom_with_parameters(
            &self.types,
            &self.constants,
            name,
            type_parameters,
            term_parameters.clone(),
            statement.clone(),
        )?;
        let declaration = staged_theorems
            .declaration(theorem)
            .expect("a newly declared trusted axiom is stored");
        let dependency_receipts = declaration
            .direct_constant_dependencies
            .iter()
            .filter_map(|constant| self.definition_receipts.get(constant).cloned())
            .collect::<Vec<_>>();
        let term_context = term_parameters
            .into_iter()
            .fold(TermContext::new(), TermContext::with_bound);
        let fragment = classify_statement(
            &self.types,
            &self.constants,
            &term_context,
            &self.fragments,
            &statement,
        )?;
        let receipt_id = DeclarationId(self.next_receipt_id);
        let next_receipt_id = self
            .next_receipt_id
            .checked_add(1)
            .ok_or_else(|| SpikeError::new("too many spike declaration receipts"))?;
        let receipt = DeclarationReceipt::trusted_axiom_with_dependencies(
            receipt_id,
            fragment,
            dependency_receipts.iter(),
        );
        self.theorems = staged_theorems;
        self.theorem_receipts.insert(theorem, receipt.clone());
        self.next_receipt_id = next_receipt_id;
        Ok((theorem, receipt))
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
                    term_arguments: Vec::new(),
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
                recursive_argument_index: 0,
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
                    term_arguments: Vec::new(),
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
                    term_arguments: Vec::new(),
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

    #[test]
    fn saturated_rank_one_symbol_templates_remain_first_order() {
        let mut elaborator = SpikeElaborator::new();
        let nat_id = elaborator.declare_base_type("Nat", true).expect("Nat");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let zero = elaborator
            .declare_constant("zero", nat.clone())
            .expect("zero");
        let predicate_type = CoreType::arrow(nat.clone(), CoreType::Prop);
        let predicate = elaborator
            .declare_constant("Even", predicate_type.clone())
            .expect("Even");

        // Parameters are [P, x], hence x is Bound(0) and P is Bound(1).
        let atom = CoreTerm::apply(CoreTerm::Bound(1), CoreTerm::Bound(0));
        let (template, template_receipt) = elaborator
            .declare_theorem_with_parameters(
                "predicate_identity",
                Vec::new(),
                vec![predicate_type, nat.clone()],
                CoreTerm::implies(atom.clone(), atom.clone()),
                HolDraftProof::ImpIntro {
                    premise: atom,
                    body: Box::new(HolDraftProof::Hypothesis(0)),
                },
            )
            .expect("checked predicate-symbol template");
        assert_eq!(
            template_receipt.proof().required_fragment(),
            StatementFragment::FirstOrder
        );

        let concrete_atom =
            CoreTerm::apply(CoreTerm::Constant(predicate), CoreTerm::Constant(zero));
        let (_, instance_receipt) = elaborator
            .declare_theorem(
                "even_zero_identity",
                Vec::new(),
                CoreTerm::implies(concrete_atom.clone(), concrete_atom),
                HolDraftProof::TheoremRef {
                    theorem: template,
                    type_arguments: Vec::new(),
                    term_arguments: vec![CoreTerm::Constant(predicate), CoreTerm::Constant(zero)],
                },
            )
            .expect("first-order template instance");
        assert_eq!(
            instance_receipt.proof().required_fragment(),
            StatementFragment::FirstOrder
        );
        assert_eq!(
            instance_receipt.proof().direct_dependencies(),
            &std::collections::BTreeSet::from([template_receipt.id()])
        );
    }

    #[test]
    fn theorem_dependencies_are_classified_at_their_actual_instance() {
        let mut elaborator = SpikeElaborator::new();
        let nat_id = elaborator.declare_base_type("Nat", true).expect("Nat");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let zero = elaborator
            .declare_constant("zero", nat.clone())
            .expect("zero");
        let parameter = TypeParameter::any(66);
        let (identity, generic_receipt) = elaborator
            .declare_theorem_with_parameters(
                "identity",
                vec![parameter],
                vec![CoreType::Parameter(parameter)],
                CoreTerm::equality(
                    CoreType::Parameter(parameter),
                    CoreTerm::Bound(0),
                    CoreTerm::Bound(0),
                ),
                HolDraftProof::EqualityRefl(CoreTerm::Bound(0)),
            )
            .expect("unrestricted generic identity");
        assert_eq!(
            generic_receipt.proof().required_fragment(),
            StatementFragment::HigherOrder
        );
        let (identity_wrapper, wrapper_receipt) = elaborator
            .declare_theorem_with_parameters(
                "identity_wrapper",
                vec![parameter],
                vec![CoreType::Parameter(parameter)],
                CoreTerm::equality(
                    CoreType::Parameter(parameter),
                    CoreTerm::Bound(0),
                    CoreTerm::Bound(0),
                ),
                HolDraftProof::TheoremRef {
                    theorem: identity,
                    type_arguments: vec![CoreType::Parameter(parameter)],
                    term_arguments: vec![CoreTerm::Bound(0)],
                },
            )
            .expect("generic identity wrapper");
        assert_eq!(
            wrapper_receipt.proof().required_fragment(),
            StatementFragment::HigherOrder
        );
        let generic_quantified_statement = CoreTerm::forall(
            CoreType::Parameter(parameter),
            CoreTerm::equality(
                CoreType::Parameter(parameter),
                CoreTerm::Bound(0),
                CoreTerm::Bound(0),
            ),
        );
        let (generic_all_identity, generic_all_receipt) = elaborator
            .declare_theorem(
                "all_identity",
                vec![parameter],
                generic_quantified_statement,
                HolDraftProof::ForallIntro {
                    domain: CoreType::Parameter(parameter),
                    body: Box::new(HolDraftProof::TheoremRef {
                        theorem: identity,
                        type_arguments: vec![CoreType::Parameter(parameter)],
                        term_arguments: vec![CoreTerm::Bound(0)],
                    }),
                },
            )
            .expect("generic theorem reference under a local binder");
        assert_eq!(
            generic_all_receipt.proof().required_fragment(),
            StatementFragment::HigherOrder
        );

        let (_, nat_receipt) = elaborator
            .declare_theorem(
                "zero_identity",
                Vec::new(),
                CoreTerm::equality(
                    nat.clone(),
                    CoreTerm::Constant(zero),
                    CoreTerm::Constant(zero),
                ),
                HolDraftProof::TheoremRef {
                    theorem: identity,
                    type_arguments: vec![nat.clone()],
                    term_arguments: vec![CoreTerm::Constant(zero)],
                },
            )
            .expect("first-order identity instance");
        assert_eq!(
            nat_receipt.proof().required_fragment(),
            StatementFragment::FirstOrder
        );
        let (_, wrapped_nat_receipt) = elaborator
            .declare_theorem(
                "wrapped_zero_identity",
                Vec::new(),
                CoreTerm::equality(
                    nat.clone(),
                    CoreTerm::Constant(zero),
                    CoreTerm::Constant(zero),
                ),
                HolDraftProof::TheoremRef {
                    theorem: identity_wrapper,
                    type_arguments: vec![nat.clone()],
                    term_arguments: vec![CoreTerm::Constant(zero)],
                },
            )
            .expect("transitive generic dependencies specialize at Nat");
        assert_eq!(
            wrapped_nat_receipt.proof().required_fragment(),
            StatementFragment::FirstOrder
        );
        let quantified_statement = CoreTerm::forall(
            nat.clone(),
            CoreTerm::equality(nat.clone(), CoreTerm::Bound(0), CoreTerm::Bound(0)),
        );
        let (_, quantified_receipt) = elaborator
            .declare_theorem(
                "all_nat_identity",
                Vec::new(),
                quantified_statement,
                HolDraftProof::ForallIntro {
                    domain: nat.clone(),
                    body: Box::new(HolDraftProof::TheoremRef {
                        theorem: identity,
                        type_arguments: vec![nat.clone()],
                        term_arguments: vec![CoreTerm::Bound(0)],
                    }),
                },
            )
            .expect("instance audit retains the local binder context");
        assert_eq!(
            quantified_receipt.proof().required_fragment(),
            StatementFragment::FirstOrder
        );
        let concrete_all_statement = CoreTerm::forall(
            nat.clone(),
            CoreTerm::equality(nat.clone(), CoreTerm::Bound(0), CoreTerm::Bound(0)),
        );
        let (_, specialized_all_receipt) = elaborator
            .declare_theorem(
                "all_nat_identity_via_generic",
                Vec::new(),
                concrete_all_statement,
                HolDraftProof::TheoremRef {
                    theorem: generic_all_identity,
                    type_arguments: vec![nat.clone()],
                    term_arguments: Vec::new(),
                },
            )
            .expect("transitive instance specialization retains nested binders");
        assert_eq!(
            specialized_all_receipt.proof().required_fragment(),
            StatementFragment::FirstOrder
        );

        let predicate_type = CoreType::arrow(nat, CoreType::Prop);
        let predicate = elaborator
            .declare_constant("P", predicate_type.clone())
            .expect("P");
        let (_, predicate_receipt) = elaborator
            .declare_theorem(
                "predicate_identity",
                Vec::new(),
                CoreTerm::equality(
                    predicate_type.clone(),
                    CoreTerm::Constant(predicate),
                    CoreTerm::Constant(predicate),
                ),
                HolDraftProof::TheoremRef {
                    theorem: identity,
                    type_arguments: vec![predicate_type],
                    term_arguments: vec![CoreTerm::Constant(predicate)],
                },
            )
            .expect("higher-order identity instance");
        assert_eq!(
            predicate_receipt.proof().required_fragment(),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn trusted_axioms_taint_every_transitive_use() {
        let mut elaborator = SpikeElaborator::new();
        let (axiom, axiom_receipt) = elaborator
            .declare_trusted_axiom("trusted_truth", Vec::new(), CoreTerm::Truth)
            .expect("trusted truth axiom");
        assert_eq!(
            axiom_receipt.status(),
            crate::hol::fragments::EvidenceStatus::TrustedAxiom
        );
        let default_policy = ReceiptPolicy::new(TeachingProfile::Prop);
        assert!(default_policy.check(&axiom_receipt).contains(
            &crate::hol::fragments::PolicyViolation::TrustedAxiomNotAllowed(axiom_receipt.id())
        ));

        let (_, user_receipt) = elaborator
            .declare_theorem(
                "uses_trusted_truth",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TheoremRef {
                    theorem: axiom,
                    type_arguments: Vec::new(),
                    term_arguments: Vec::new(),
                },
            )
            .expect("theorem using trusted axiom");
        assert_eq!(
            user_receipt.proof().axiom_dependencies(),
            &std::collections::BTreeSet::from([axiom_receipt.id()])
        );
        assert!(!default_policy.check(&user_receipt).is_empty());

        let mut allowed = ReceiptPolicy::new(TeachingProfile::Prop);
        allowed.allow_axiom(axiom_receipt.id());
        assert!(allowed.check(&axiom_receipt).is_empty());
        assert!(allowed.check(&user_receipt).is_empty());
    }

    #[test]
    fn explicit_classical_evidence_taints_every_transitive_use() {
        let mut elaborator = SpikeElaborator::new();
        let atom = elaborator.declare_constant("P", CoreType::Prop).expect("P");
        let proposition = CoreTerm::Constant(atom);
        let excluded_middle = CoreTerm::or(
            proposition.clone(),
            CoreTerm::implies(proposition.clone(), CoreTerm::Falsity),
        );
        let (classical, classical_receipt) = elaborator
            .declare_theorem(
                "excluded_middle",
                Vec::new(),
                excluded_middle,
                HolDraftProof::ExcludedMiddle { proposition },
            )
            .expect("explicit classical theorem");
        assert_eq!(
            classical_receipt.proof().direct_features(),
            &std::collections::BTreeSet::from([ProofFeature::Classical])
        );

        let classical_statement = elaborator
            .theorems()
            .declaration(classical)
            .expect("classical theorem")
            .statement
            .clone();
        let (_, facade_receipt) = elaborator
            .declare_theorem(
                "classical_facade",
                Vec::new(),
                classical_statement,
                HolDraftProof::TheoremRef {
                    theorem: classical,
                    type_arguments: Vec::new(),
                    term_arguments: Vec::new(),
                },
            )
            .expect("classical facade");
        assert!(facade_receipt.proof().direct_features().is_empty());
        assert_eq!(
            facade_receipt.proof().transitive_features(),
            &std::collections::BTreeSet::from([ProofFeature::Classical])
        );
        assert!(!ReceiptPolicy::new(TeachingProfile::Prop)
            .check(&facade_receipt)
            .is_empty());
        let mut classical_policy = ReceiptPolicy::new(TeachingProfile::Prop);
        classical_policy.allow_classical();
        assert!(classical_policy.check(&facade_receipt).is_empty());
    }

    #[test]
    fn incomplete_drafts_are_policy_visible_and_cannot_be_laundered() {
        let mut elaborator = SpikeElaborator::new();
        let (unfinished, unfinished_receipt) = elaborator
            .declare_incomplete_theorem(
                "unfinished_truth",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::Sorry {
                    target: CoreTerm::Truth,
                },
            )
            .expect("typed incomplete theorem");
        assert_eq!(
            unfinished_receipt.status(),
            crate::hol::fragments::EvidenceStatus::Incomplete
        );
        let default_policy = ReceiptPolicy::new(TeachingProfile::Prop);
        assert!(default_policy.check(&unfinished_receipt).contains(
            &crate::hol::fragments::PolicyViolation::IncompleteNotAllowed(unfinished_receipt.id())
        ));
        let mut draft_policy = ReceiptPolicy::new(TeachingProfile::Prop);
        draft_policy.allow_incomplete();
        assert!(draft_policy.check(&unfinished_receipt).is_empty());

        let (_, facade_receipt) = elaborator
            .declare_incomplete_theorem(
                "unfinished_facade",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TheoremRef {
                    theorem: unfinished,
                    type_arguments: Vec::new(),
                    term_arguments: Vec::new(),
                },
            )
            .expect("incomplete dependency remains a draft");
        assert_eq!(
            facade_receipt.proof().incomplete_dependencies(),
            &std::collections::BTreeSet::from([unfinished_receipt.id()])
        );
        assert!(draft_policy.check(&facade_receipt).is_empty());

        let laundering = elaborator
            .declare_theorem(
                "laundered_truth",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TheoremRef {
                    theorem: unfinished,
                    type_arguments: Vec::new(),
                    term_arguments: Vec::new(),
                },
            )
            .expect_err("checked evidence cannot reference an incomplete theorem");
        assert!(laundering.message.contains("not kernel evidence"));
        assert!(elaborator.theorems().resolve("laundered_truth").is_none());

        let atom = elaborator.declare_constant("P", CoreType::Prop).expect("P");
        let proposition = CoreTerm::Constant(atom);
        let excluded_middle = CoreTerm::or(
            proposition.clone(),
            CoreTerm::implies(proposition.clone(), CoreTerm::Falsity),
        );
        let (_, classical_draft) = elaborator
            .declare_incomplete_theorem(
                "unfinished_classical",
                Vec::new(),
                CoreTerm::and(excluded_middle, CoreTerm::Truth),
                HolDraftProof::AndIntro(
                    Box::new(HolDraftProof::ExcludedMiddle { proposition }),
                    Box::new(HolDraftProof::Sorry {
                        target: CoreTerm::Truth,
                    }),
                ),
            )
            .expect("classical features survive draft storage");
        assert_eq!(
            classical_draft.proof().direct_features(),
            &std::collections::BTreeSet::from([ProofFeature::Classical])
        );
    }

    #[test]
    fn legacy_set_extensionality_is_first_order_but_explicitly_trusted() {
        let mut elaborator = SpikeElaborator::new();
        let nat_id = elaborator.declare_base_type("Nat", true).expect("Nat");
        elaborator
            .declare_legacy_set_type("Set")
            .expect("legacy Set");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let parameter = TypeParameter::first_order(77);
        let element_type = CoreType::Parameter(parameter);
        let set_type = elaborator
            .types()
            .legacy_set_type(element_type.clone())
            .expect("Set A");
        let in_left =
            CoreTerm::membership(element_type.clone(), CoreTerm::Bound(0), CoreTerm::Bound(2));
        let in_right =
            CoreTerm::membership(element_type.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1));
        let pointwise = CoreTerm::forall(
            element_type,
            CoreTerm::and(
                CoreTerm::implies(in_left.clone(), in_right.clone()),
                CoreTerm::implies(in_right, in_left),
            ),
        );
        let set_ext_statement = CoreTerm::implies(
            pointwise,
            CoreTerm::equality(set_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
        );
        let (set_ext, set_ext_receipt) = elaborator
            .declare_trusted_axiom_with_parameters(
                "set_ext",
                vec![parameter],
                vec![set_type.clone(), set_type],
                set_ext_statement,
            )
            .expect("typed set extensionality axiom");
        assert_eq!(
            set_ext_receipt.proof().required_fragment(),
            StatementFragment::FirstOrder
        );

        let empty = CoreTerm::empty_set(nat.clone());
        let (_, user_receipt) = elaborator
            .declare_theorem(
                "empty_extensional",
                Vec::new(),
                CoreTerm::equality(
                    elaborator
                        .types()
                        .legacy_set_type(nat.clone())
                        .expect("Set Nat"),
                    empty.clone(),
                    empty.clone(),
                ),
                HolDraftProof::ImpElim {
                    proof_implication: Box::new(HolDraftProof::TheoremRef {
                        theorem: set_ext,
                        type_arguments: vec![nat.clone()],
                        term_arguments: vec![empty.clone(), empty],
                    }),
                    proof_argument: Box::new(HolDraftProof::ForallIntro {
                        domain: nat,
                        body: Box::new(HolDraftProof::AndIntro(
                            Box::new(HolDraftProof::ImpIntro {
                                premise: CoreTerm::Falsity,
                                body: Box::new(HolDraftProof::Hypothesis(0)),
                            }),
                            Box::new(HolDraftProof::ImpIntro {
                                premise: CoreTerm::Falsity,
                                body: Box::new(HolDraftProof::Hypothesis(0)),
                            }),
                        )),
                    }),
                },
            )
            .expect("set extensionality user");
        assert_eq!(
            user_receipt.proof().axiom_dependencies(),
            &std::collections::BTreeSet::from([set_ext_receipt.id()])
        );
    }
}
