//! Public boundary for the legacy kernel during the HOL migration.
//!
//! The current implementation still delegates to the legacy environment
//! internally. Keeping that reference opaque prevents new callers from making
//! the full checker environment part of the long-term kernel API.

use crate::Env;

#[derive(Clone, Copy)]
pub struct KernelSignature<'env> {
    environment: &'env Env,
}

impl<'env> KernelSignature<'env> {
    pub(crate) fn environment(self) -> &'env Env {
        self.environment
    }
}

impl Env {
    /// Return the read-only signature view accepted by the public kernel API.
    pub fn kernel_signature(&self) -> KernelSignature<'_> {
        KernelSignature { environment: self }
    }
}
