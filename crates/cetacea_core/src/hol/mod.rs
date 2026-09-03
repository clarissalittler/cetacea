//! Constructive HOL core: the kernel since the H7 cutover.
//!
//! The legacy checker in the crate root elaborates surface proofs, produces
//! goals, diagnostics and countermodels, and is not trusted. Every declaration
//! it accepts is replayed into this core through the `*_with_hol_shadow`
//! entry points, and [`crate::HolShadowReport::certified`] turns any replay
//! failure into a rejected declaration. The trusted modules are the ones
//! listed in `scripts/check_kernel_boundary.py`; see
//! `docs/hol/H7_DECISION.md` for the decision record and what remains.

pub mod declarations;
pub mod finite_library;
pub mod fragments;
pub mod graph_library;
mod h35_cardinality;
pub mod h3_examples;
pub mod inductive;
pub mod library;
pub mod library_registry;
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
pub use finite_library::{
    FiniteEnumerationEvidence, FiniteEnumerationLibrary, FiniteEnumerationNames,
};
pub use fragments::{
    classify_statement, proof_features_from_audit, DeclarationId, DeclarationReceipt,
    EvidenceStatus, FragmentError, FragmentMetadata, PolicyViolation, ProofFeature, ProofReceipt,
    ReceiptPolicy, StatementFragment, TeachingProfile,
};
pub use graph_library::{GraphLibrary, GraphLibraryNames, PathConcatenationTheorem};
pub use h35_cardinality::{
    install_cardinality_transport, install_cardinality_transport_named,
    CardinalityTransportLibrary, CardinalityTransportNames,
};
pub use h3_examples::{
    run_finite_h3_spike, run_graph_h3_spike, run_list_h3_spike, H3FiniteSpikeReport,
    H3GraphSpikeReport, H3ListSpikeReport,
};
pub use inductive::{
    InductiveConstructor, InductiveConstructorSpec, InductiveDeclaration, InductiveError,
    InductiveFieldType, InductiveSignature, InductiveSpec, InstantiatedConstructor,
};
pub use library::{ListLength, ListLibrary, ListLibraryNames};
pub use library_registry::{
    HolLibraryRegistry, InstalledCardinalityLibrary, InstalledFiniteLibrary,
    InstalledLibraryPackage, InstalledListLibrary, LibraryDeclaration, LibraryDeclarationKind,
    LibraryPackageId, LibraryPackageProvenance, LibraryPackageRecord, LibraryPackageSource,
    BUILTIN_CARDINALITY_V1_MODULE, BUILTIN_CARDINALITY_V1_NAMESPACE, BUILTIN_FINITE_V1_MODULE,
    BUILTIN_FINITE_V1_NAMESPACE, BUILTIN_LIST_V1_MODULE, BUILTIN_LIST_V1_NAMESPACE,
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
