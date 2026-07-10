//! Experimental constructive HOL core.
//!
//! This module is developed in parallel with the legacy checker. Nothing in
//! the existing parser or teaching corpus lowers to it until the H3 spike has
//! passed its stop/go gate.

pub mod terms;
pub mod types;

pub use terms::{
    definitionally_equal, infer_type, normalize, ConstantId, CoreTerm, TermContext, TermError,
    TermSignature,
};
pub use types::{
    CoreType, FirstOrderStatus, TypeConstructorId, TypeError, TypeParameter, TypeParameterClass,
    TypeParameterId, TypeSignature,
};
