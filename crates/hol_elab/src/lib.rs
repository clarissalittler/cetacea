//! Elaboration for Cetacea 2: surface syntax to kernel terms, the
//! checking environment, tier checks, the prelude, and the
//! surface-syntax printer.

pub mod decl;
pub mod diag;
pub mod env;
pub mod expr;
pub mod prelude;
pub mod print;
pub mod types;

pub use decl::{elab_command, elab_params, elab_theorem_header, TheoremHeader};
pub use diag::{Diagnostic, Result};
pub use env::{ConstInfo, DefInfo, Env, ParamInfo, Status, SymbolKind, TheoremInfo};
pub use expr::{Elab, Scope};
pub use prelude::{install, new_env, PRELUDE_SOURCE};
pub use print::{describe_term, print_term, print_type};
pub use types::{elab_type, is_meta, TypePosition, TypeScope, Unifier};
