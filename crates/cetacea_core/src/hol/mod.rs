//! Experimental constructive HOL core.
//!
//! This module is developed in parallel with the legacy checker. Nothing in
//! the existing parser or teaching corpus lowers to it until the H3 spike has
//! passed its stop/go gate.

pub mod fragments;
pub mod proofs;
pub mod terms;
pub mod types;

pub use fragments::{
    classify_statement, DeclarationId, DeclarationReceipt, EvidenceStatus, FragmentError,
    FragmentMetadata, PolicyViolation, ProofFeature, ProofReceipt, ReceiptPolicy,
    StatementFragment, TeachingProfile,
};
pub use proofs::{check_hol_proof, HolDraftProof, HolKernelProof, HolProofContext, ProofError};
pub use terms::{
    definitionally_equal, infer_type, instantiate_binder, normalize, ConstantId, CoreTerm,
    TermContext, TermError, TermSignature,
};
pub use types::{
    CoreType, FirstOrderStatus, TypeConstructorId, TypeError, TypeParameter, TypeParameterClass,
    TypeParameterId, TypeSignature,
};
