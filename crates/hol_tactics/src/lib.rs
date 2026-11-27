//! The tactic engine of Cetacea 2: goals, proof states, proof
//! expressions, unification, conversions, and the tactic interpreter.

pub mod conv;
pub mod decide;
pub mod pexpr;
pub mod proof;
pub mod simp_rules;
pub mod tactics;
pub mod unify;
pub mod uses;

pub use conv::{head_unfold, normal_form, normalize, Rule, Rules};
pub use pexpr::{strip_meta_suffixes, ProofCtx};
pub use proof::{DerivationStep, Goal, Justification, ProofState};
pub use tactics::{prove, Failure, Outcome, StepRecord};
pub use unify::{schematize, Subst, TermNorm};
pub use uses::TheoremUse;
