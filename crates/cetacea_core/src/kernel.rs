//! Public proof-kernel boundary.
//!
//! During H1 this module adapts the legacy recursive checker in the crate root.
//! Its public types and function are the seam that the parallel HOL kernel will
//! eventually implement without exposing parser, tactic, model, or driver state.

use crate::{check_kernel_proof_node, Context, Env, Formula, KernelError, KernelProof, LogicMode};

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

pub fn check_proof(
    signature: &KernelSignature<'_>,
    context: &Context,
    proof: &KernelProof,
    expected: &Formula,
    allowed_mode: LogicMode,
) -> Result<LogicMode, KernelError> {
    check_kernel_proof_node(
        signature.environment(),
        context,
        &proof.0,
        expected,
        allowed_mode,
    )
}
