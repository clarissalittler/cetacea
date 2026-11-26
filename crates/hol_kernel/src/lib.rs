//! The trusted kernel of Cetacea 2.
//!
//! This crate is the whole trusted computing base of the prover:
//!
//! - [`Type`] and [`Term`]: simply typed lambda terms in locally nameless
//!   form, well typed by construction.
//! - [`Thm`]: a hypothesis set, a conclusion, and [`Tags`] recording
//!   classical reasoning, `sorry`, axioms, and datatype packages the
//!   theorem depends on. Only this crate can construct a `Thm`.
//! - [`rules`]: the primitive natural deduction and equality rules.
//! - [`Theory`]: the signature and the definitional principles (types,
//!   constants, definitions, axioms, datatypes, structurally recursive
//!   functions).
//! - [`derived`]: convenience rules built from the primitives, which are
//!   therefore not trusted.
//! - [`record`]: an optional, write-only log of rule applications for
//!   explanations and diagnostics. No rule reads it.
//!
//! The kernel has no parser, no tactics, and no dependencies.

mod derived;
mod error;
mod logic;
mod name;
mod print;
pub mod record;
mod rules;
mod signature;
mod term;
mod theory;
mod thm;
mod types;

pub use derived::{
    beta_norm, beta_norm_conv, discharge, funext, generalize, iff_left, iff_right, spec, subst,
};
pub use error::{KernelError, Result};
pub use logic::{AND, EQ, EXISTS, FALSE, FORALL, IMP, MEM, OR, SET_OF, TRUE};
pub use name::{fresh_name, Name};
pub use rules::*;
pub use signature::Signature;
pub use term::{Term, TermView};
pub use theory::{
    CtorInfo, CtorSpec, DatatypeInfo, DatatypeSpec, RecFunSpec, Theory, MEM_SET_OF, SET_EXT,
};
pub use thm::{Tags, Thm};
pub use types::{Type, TypeSubst, FUN, PROP, SET};
