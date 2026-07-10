//! Stable storage for previously kernel-checked HOL theorems.

use std::collections::{BTreeSet, HashMap};
use std::fmt;

use super::inductive::InductiveSignature;
use super::proofs::{
    check_hol_proof_with_signatures_audit, validate_kernel_proof_type_scheme, HolKernelProof,
    HolProofAudit, HolProofContext, ProofError,
};
use super::terms::{
    instantiate_term_type_scheme, term_constant_dependencies, validate_term_type_scheme,
    ConstantId, CoreTerm, TermContext, TermError, TermSignature,
};
use super::types::{CoreType, TypeError, TypeParameter, TypeSignature};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TheoremId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HolTheoremDeclaration {
    pub name: String,
    pub type_parameters: Vec<TypeParameter>,
    pub statement: CoreTerm,
    pub direct_dependencies: BTreeSet<TheoremId>,
    pub direct_constant_dependencies: BTreeSet<ConstantId>,
    pub audit: HolProofAudit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremError {
    pub message: String,
}

impl TheoremError {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for TheoremError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for TheoremError {}

impl From<TypeError> for TheoremError {
    fn from(error: TypeError) -> Self {
        Self::new(error.message)
    }
}

impl From<TermError> for TheoremError {
    fn from(error: TermError) -> Self {
        Self::new(error.message)
    }
}

impl From<ProofError> for TheoremError {
    fn from(error: ProofError) -> Self {
        Self::new(error.message)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HolTheoremSignature {
    declarations: Vec<HolTheoremDeclaration>,
    names: HashMap<String, TheoremId>,
}

impl HolTheoremSignature {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve(&self, name: &str) -> Option<TheoremId> {
        self.names.get(name).copied()
    }

    pub fn declaration(&self, id: TheoremId) -> Option<&HolTheoremDeclaration> {
        self.declarations.get(id.0 as usize)
    }

    pub fn instantiate_statement(
        &self,
        types: &TypeSignature,
        id: TheoremId,
        type_arguments: &[CoreType],
    ) -> Result<CoreTerm, TheoremError> {
        let declaration = self
            .declaration(id)
            .ok_or_else(|| TheoremError::new(format!("unknown checked theorem id `{}`", id.0)))?;
        Ok(instantiate_term_type_scheme(
            types,
            &declaration.type_parameters,
            &declaration.statement,
            type_arguments,
        )?)
    }

    pub fn check_and_declare(
        &mut self,
        types: &TypeSignature,
        constants: &TermSignature,
        inductives: &InductiveSignature,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        statement: CoreTerm,
        proof: HolKernelProof,
    ) -> Result<TheoremId, TheoremError> {
        let name = name.into();
        let id = self.reserve_id(&name)?;
        types.validate_scheme(&type_parameters, &CoreType::Prop)?;
        validate_term_type_scheme(types, &type_parameters, &statement)?;
        validate_kernel_proof_type_scheme(types, &type_parameters, &proof)?;
        let audit = check_hol_proof_with_signatures_audit(
            types,
            constants,
            inductives,
            self,
            &TermContext::new(),
            &HolProofContext::new(),
            &proof,
            &statement,
        )?;
        let direct_dependencies = audit.theorem_dependencies().clone();
        let mut direct_constant_dependencies = term_constant_dependencies(&statement);
        direct_constant_dependencies.extend(audit.constant_dependencies().iter().copied());
        self.insert_checked(
            id,
            HolTheoremDeclaration {
                name,
                type_parameters,
                statement,
                direct_dependencies,
                direct_constant_dependencies,
                audit,
            },
        )?;
        Ok(id)
    }

    fn reserve_id(&self, name: &str) -> Result<TheoremId, TheoremError> {
        if self.names.contains_key(name) {
            return Err(TheoremError::new(format!(
                "checked theorem `{name}` is already declared"
            )));
        }
        u32::try_from(self.declarations.len())
            .map(TheoremId)
            .map_err(|_| TheoremError::new("too many checked theorems"))
    }

    fn insert_checked(
        &mut self,
        id: TheoremId,
        declaration: HolTheoremDeclaration,
    ) -> Result<(), TheoremError> {
        let expected = self.reserve_id(&declaration.name)?;
        if id != expected {
            return Err(TheoremError::new(
                "checked theorem signature declaration history is inconsistent",
            ));
        }
        self.names.insert(declaration.name.clone(), id);
        self.declarations.push(declaration);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::proofs::HolDraftProof;
    use crate::hol::terms::{ConstantId, CoreTerm};
    use crate::hol::types::TypeParameter;

    struct Fixture {
        types: TypeSignature,
        constants: TermSignature,
        inductives: InductiveSignature,
        nat: CoreType,
        zero: ConstantId,
    }

    fn fixture() -> Fixture {
        let mut types = TypeSignature::new();
        let nat_id = types.declare("Nat", 0, true).expect("Nat");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let mut constants = TermSignature::new();
        let zero = constants
            .declare(&types, "zero", nat.clone())
            .expect("zero");
        Fixture {
            types,
            constants,
            inductives: InductiveSignature::new(),
            nat,
            zero,
        }
    }

    fn kernel(proof: HolDraftProof) -> HolKernelProof {
        HolKernelProof::try_from(proof).expect("hole-free theorem proof")
    }

    #[test]
    fn checked_polymorphic_theorems_can_be_referenced_at_explicit_types() {
        let fixture = fixture();
        let mut theorems = HolTheoremSignature::new();
        let parameter = TypeParameter::any(0);
        let identity_statement = CoreTerm::forall(
            CoreType::Parameter(parameter),
            CoreTerm::equality(
                CoreType::Parameter(parameter),
                CoreTerm::Bound(0),
                CoreTerm::Bound(0),
            ),
        );
        let identity = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "identity",
                vec![parameter],
                identity_statement,
                kernel(HolDraftProof::ForallIntro {
                    domain: CoreType::Parameter(parameter),
                    body: Box::new(HolDraftProof::EqualityRefl(CoreTerm::Bound(0))),
                }),
            )
            .expect("generic equality identity");

        let zero_statement = CoreTerm::equality(
            fixture.nat.clone(),
            CoreTerm::Constant(fixture.zero),
            CoreTerm::Constant(fixture.zero),
        );
        let zero_identity = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "zero_identity",
                Vec::new(),
                zero_statement,
                kernel(HolDraftProof::ForallElim {
                    proof_forall: Box::new(HolDraftProof::TheoremRef {
                        theorem: identity,
                        type_arguments: vec![fixture.nat.clone()],
                    }),
                    argument: CoreTerm::Constant(fixture.zero),
                }),
            )
            .expect("instantiate identity at Nat");
        let declaration = theorems
            .declaration(zero_identity)
            .expect("stored zero theorem");
        assert_eq!(declaration.direct_dependencies, BTreeSet::from([identity]));
        assert_eq!(
            declaration.direct_constant_dependencies,
            BTreeSet::from([fixture.zero])
        );
        assert_eq!(theorems.resolve("identity"), Some(identity));

        let hidden_constant = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "hidden_constant",
                Vec::new(),
                CoreTerm::Truth,
                kernel(HolDraftProof::OrElim {
                    proof_or: Box::new(HolDraftProof::OrIntroLeft {
                        proof_left: Box::new(HolDraftProof::TruthIntro),
                        right: CoreTerm::equality(
                            fixture.nat.clone(),
                            CoreTerm::Constant(fixture.zero),
                            CoreTerm::Constant(fixture.zero),
                        ),
                    }),
                    left_case: Box::new(HolDraftProof::TruthIntro),
                    right_case: Box::new(HolDraftProof::TruthIntro),
                    target: CoreTerm::Truth,
                }),
            )
            .expect("constant in proof evidence");
        assert_eq!(
            theorems
                .declaration(hidden_constant)
                .expect("stored hidden constant theorem")
                .direct_constant_dependencies,
            BTreeSet::from([fixture.zero])
        );
    }

    #[test]
    fn theorem_declarations_reject_unknown_refs_duplicates_and_free_type_parameters() {
        let fixture = fixture();
        let mut theorems = HolTheoremSignature::new();
        let unknown = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "unknown_ref",
                Vec::new(),
                CoreTerm::Truth,
                kernel(HolDraftProof::TheoremRef {
                    theorem: TheoremId(99),
                    type_arguments: Vec::new(),
                }),
            )
            .expect_err("unknown theorem reference must fail");
        assert!(unknown.message.contains("unknown checked theorem id"));
        assert_eq!(theorems.resolve("unknown_ref"), None);

        let first = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "truth",
                Vec::new(),
                CoreTerm::Truth,
                kernel(HolDraftProof::TruthIntro),
            )
            .expect("truth");
        let duplicate = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "truth",
                Vec::new(),
                CoreTerm::Truth,
                kernel(HolDraftProof::TruthIntro),
            )
            .expect_err("duplicate theorem name must fail");
        assert!(duplicate.message.contains("already declared"));
        assert_eq!(theorems.declaration(first).expect("truth").name, "truth");

        let free = TypeParameter::any(77);
        let free_error = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "free_type",
                Vec::new(),
                CoreTerm::forall(CoreType::Parameter(free), CoreTerm::Truth),
                kernel(HolDraftProof::ForallIntro {
                    domain: CoreType::Parameter(free),
                    body: Box::new(HolDraftProof::TruthIntro),
                }),
            )
            .expect_err("free type parameter must fail");
        assert!(free_error.message.contains("is not declared"));
        assert_eq!(theorems.resolve("free_type"), None);
    }
}
