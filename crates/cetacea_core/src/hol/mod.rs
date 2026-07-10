//! Experimental constructive HOL core.
//!
//! This module is developed in parallel with the legacy checker. The production
//! command/import driver can now replay every legacy-accepted declaration into
//! this core through the opt-in HOL shadow API. The exact H4 corpus gate passes,
//! but the legacy checker remains authoritative until an explicit cutover
//! decision; a shadow mismatch never changes legacy acceptance.

pub mod declarations;
pub mod fragments;
mod h35_cardinality;
pub mod h3_examples;
pub mod inductive;
mod linked_smoke;
pub mod lowering;
pub mod prelude;
pub mod proofs;
pub mod recursion;
pub mod spike;
pub mod terms;
pub mod theorems;
pub mod types;

pub use declarations::{CompatibilityDeclarationError, CompatibilityElaborator};
pub use fragments::{
    classify_statement, proof_features_from_audit, DeclarationId, DeclarationReceipt,
    EvidenceStatus, FragmentError, FragmentMetadata, PolicyViolation, ProofFeature, ProofReceipt,
    ReceiptPolicy, StatementFragment, TeachingProfile,
};
pub use h3_examples::{
    run_finite_h3_spike, run_graph_h3_spike, run_list_h3_spike, H3FiniteSpikeReport,
    H3GraphSpikeReport, H3ListSpikeReport,
};
pub use inductive::{
    InductiveConstructor, InductiveConstructorSpec, InductiveDeclaration, InductiveError,
    InductiveFieldType, InductiveSignature, InductiveSpec, InstantiatedConstructor,
};
pub use linked_smoke::{run_linked_hol_smoke, LinkedHolSmokeReport};
pub use lowering::{CompatibilityLowerer, LoweringError};
pub use prelude::CompatibilityPrelude;
pub use proofs::{
    check_hol_proof, check_hol_proof_audit, check_hol_proof_with_inductives,
    check_hol_proof_with_inductives_audit, check_hol_proof_with_signatures_audit, HolDraftProof,
    HolKernelProof, HolProofAudit, HolProofContext, HolTheoremReferenceAudit, ProofError,
};
pub use recursion::{
    RecursionError, RecursionSignature, StructuralArmLayout, StructuralArmSpec,
    StructuralDefinition, StructuralDefinitionSpec,
};
pub use spike::{SpikeElaborator, SpikeError};
pub use terms::{
    definitionally_equal, infer_type, instantiate_binder, normalize, ConstantId, CoreTerm,
    TermContext, TermError, TermSignature, TransparentDefinition,
};
pub use theorems::{
    HolTheoremDeclaration, HolTheoremSignature, HolTheoremStatus, TheoremError, TheoremId,
};
pub use types::{
    CoreType, FirstOrderStatus, TypeConstructorId, TypeError, TypeParameter, TypeParameterClass,
    TypeParameterId, TypeSignature,
};
