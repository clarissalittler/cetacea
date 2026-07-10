//! Experimental constructive HOL core.
//!
//! This module is developed in parallel with the legacy checker. Nothing in
//! the existing parser or teaching corpus lowers to it until the H3 spike has
//! passed its stop/go gate.

pub mod fragments;
pub mod h3_examples;
pub mod inductive;
pub mod proofs;
pub mod recursion;
pub mod spike;
pub mod terms;
pub mod types;

pub use fragments::{
    classify_statement, proof_features_from_audit, DeclarationId, DeclarationReceipt,
    EvidenceStatus, FragmentError, FragmentMetadata, PolicyViolation, ProofFeature, ProofReceipt,
    ReceiptPolicy, StatementFragment, TeachingProfile,
};
pub use h3_examples::{
    run_graph_h3_spike, run_list_h3_spike, H3GraphSpikeReport, H3ListSpikeReport,
};
pub use inductive::{
    InductiveConstructor, InductiveConstructorSpec, InductiveDeclaration, InductiveError,
    InductiveFieldType, InductiveSignature, InductiveSpec, InstantiatedConstructor,
};
pub use proofs::{
    check_hol_proof, check_hol_proof_audit, check_hol_proof_with_inductives,
    check_hol_proof_with_inductives_audit, HolDraftProof, HolKernelProof, HolProofAudit,
    HolProofContext, ProofError,
};
pub use recursion::{
    RecursionError, RecursionSignature, StructuralArmLayout, StructuralArmSpec,
    StructuralDefinition, StructuralDefinitionSpec,
};
pub use spike::{CheckedSpikeTheorem, SpikeElaborator, SpikeError};
pub use terms::{
    definitionally_equal, infer_type, instantiate_binder, normalize, ConstantId, CoreTerm,
    TermContext, TermError, TermSignature,
};
pub use types::{
    CoreType, FirstOrderStatus, TypeConstructorId, TypeError, TypeParameter, TypeParameterClass,
    TypeParameterId, TypeSignature,
};
