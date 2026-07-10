//! Stable storage for previously kernel-checked HOL theorems.

use std::collections::{BTreeSet, HashMap};
use std::fmt;

use super::inductive::InductiveSignature;
use super::proofs::{
    check_hol_draft_with_signatures_audit, check_hol_proof_with_signatures_audit,
    validate_draft_proof_type_scheme, validate_kernel_proof_type_scheme, HolDraftProof,
    HolKernelProof, HolProofAudit, HolProofContext, ProofError,
};
use super::terms::{
    infer_type, instantiate_term_parameters, instantiate_term_type_scheme,
    term_constant_dependencies, validate_term_type_scheme, ConstantId, CoreTerm, TermContext,
    TermError, TermSignature,
};
use super::types::{CoreType, TypeError, TypeParameter, TypeSignature};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TheoremId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HolTheoremStatus {
    Checked,
    Incomplete,
    TrustedAxiom,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HolTheoremDeclaration {
    pub name: String,
    pub status: HolTheoremStatus,
    pub type_parameters: Vec<TypeParameter>,
    pub term_parameters: Vec<CoreType>,
    pub statement: CoreTerm,
    pub direct_dependencies: BTreeSet<TheoremId>,
    pub direct_constant_dependencies: BTreeSet<ConstantId>,
    pub audit: HolProofAudit,
    /// Retained only for incomplete declarations. Checked evidence has already
    /// crossed the kernel boundary; trusted axioms deliberately have none.
    pub incomplete_draft: Option<HolDraftProof>,
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
        constants: &TermSignature,
        context: &TermContext,
        id: TheoremId,
        type_arguments: &[CoreType],
        term_arguments: &[CoreTerm],
    ) -> Result<CoreTerm, TheoremError> {
        self.instantiate_statement_internal(
            types,
            constants,
            context,
            id,
            type_arguments,
            term_arguments,
            false,
        )
    }

    pub(crate) fn instantiate_draft_statement(
        &self,
        types: &TypeSignature,
        constants: &TermSignature,
        context: &TermContext,
        id: TheoremId,
        type_arguments: &[CoreType],
        term_arguments: &[CoreTerm],
    ) -> Result<CoreTerm, TheoremError> {
        self.instantiate_statement_internal(
            types,
            constants,
            context,
            id,
            type_arguments,
            term_arguments,
            true,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn instantiate_statement_internal(
        &self,
        types: &TypeSignature,
        constants: &TermSignature,
        context: &TermContext,
        id: TheoremId,
        type_arguments: &[CoreType],
        term_arguments: &[CoreTerm],
        allow_incomplete: bool,
    ) -> Result<CoreTerm, TheoremError> {
        let declaration = self
            .declaration(id)
            .ok_or_else(|| TheoremError::new(format!("unknown checked theorem id `{}`", id.0)))?;
        if declaration.status == HolTheoremStatus::Incomplete && !allow_incomplete {
            return Err(TheoremError::new(format!(
                "incomplete theorem `{}` is not kernel evidence",
                declaration.name
            )));
        }
        if term_arguments.len() != declaration.term_parameters.len() {
            return Err(TheoremError::new(format!(
                "checked theorem `{}` expects {} explicit term argument(s), but got {}",
                declaration.name,
                declaration.term_parameters.len(),
                term_arguments.len()
            )));
        }
        let statement = instantiate_term_type_scheme(
            types,
            &declaration.type_parameters,
            &declaration.statement,
            type_arguments,
        )?;
        for (parameter, argument) in declaration.term_parameters.iter().zip(term_arguments) {
            let parameter = types.instantiate_scheme(
                &declaration.type_parameters,
                parameter,
                type_arguments,
            )?;
            let actual = infer_type(types, constants, context, argument)?;
            if actual != parameter {
                return Err(TheoremError::new(format!(
                    "checked theorem `{}` term argument has type `{actual:?}`, but expected `{parameter:?}`",
                    declaration.name
                )));
            }
        }
        let statement = instantiate_term_parameters(&statement, term_arguments)?;
        let actual = infer_type(types, constants, context, &statement)?;
        if actual != CoreType::Prop {
            return Err(TheoremError::new(format!(
                "instantiated checked theorem `{}` has type `{actual:?}`, not `Prop`",
                declaration.name
            )));
        }
        Ok(statement)
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
        self.check_and_declare_with_parameters(
            types,
            constants,
            inductives,
            name,
            type_parameters,
            Vec::new(),
            statement,
            proof,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn check_and_declare_with_parameters(
        &mut self,
        types: &TypeSignature,
        constants: &TermSignature,
        inductives: &InductiveSignature,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        term_parameters: Vec<CoreType>,
        statement: CoreTerm,
        proof: HolKernelProof,
    ) -> Result<TheoremId, TheoremError> {
        let name = name.into();
        let id = self.reserve_id(&name)?;
        types.validate_scheme(&type_parameters, &CoreType::Prop)?;
        for parameter in &term_parameters {
            types.validate_scheme(&type_parameters, parameter)?;
        }
        validate_term_type_scheme(types, &type_parameters, &statement)?;
        validate_kernel_proof_type_scheme(types, &type_parameters, &proof)?;
        let term_context = term_parameters
            .iter()
            .cloned()
            .fold(TermContext::new(), TermContext::with_bound);
        let audit = check_hol_proof_with_signatures_audit(
            types,
            constants,
            inductives,
            self,
            &term_context,
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
                status: HolTheoremStatus::Checked,
                type_parameters,
                term_parameters,
                statement,
                direct_dependencies,
                direct_constant_dependencies,
                audit,
                incomplete_draft: None,
            },
        )?;
        Ok(id)
    }

    pub fn check_and_declare_incomplete(
        &mut self,
        types: &TypeSignature,
        constants: &TermSignature,
        inductives: &InductiveSignature,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        statement: CoreTerm,
        draft: HolDraftProof,
    ) -> Result<TheoremId, TheoremError> {
        self.check_and_declare_incomplete_with_parameters(
            types,
            constants,
            inductives,
            name,
            type_parameters,
            Vec::new(),
            statement,
            draft,
        )
    }

    /// Type-check and retain a theorem draft without admitting it as kernel
    /// evidence. A draft is incomplete when it contains a typed `sorry` hole
    /// or depends directly on another incomplete theorem.
    #[allow(clippy::too_many_arguments)]
    pub fn check_and_declare_incomplete_with_parameters(
        &mut self,
        types: &TypeSignature,
        constants: &TermSignature,
        inductives: &InductiveSignature,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        term_parameters: Vec<CoreType>,
        statement: CoreTerm,
        draft: HolDraftProof,
    ) -> Result<TheoremId, TheoremError> {
        let name = name.into();
        let id = self.reserve_id(&name)?;
        types.validate_scheme(&type_parameters, &CoreType::Prop)?;
        for parameter in &term_parameters {
            types.validate_scheme(&type_parameters, parameter)?;
        }
        validate_term_type_scheme(types, &type_parameters, &statement)?;
        validate_draft_proof_type_scheme(types, &type_parameters, &draft)?;
        let term_context = term_parameters
            .iter()
            .cloned()
            .fold(TermContext::new(), TermContext::with_bound);
        let audit = check_hol_draft_with_signatures_audit(
            types,
            constants,
            inductives,
            self,
            &term_context,
            &HolProofContext::new(),
            &draft,
            &statement,
        )?;
        let direct_dependencies = audit.theorem_dependencies().clone();
        let depends_on_incomplete = direct_dependencies.iter().any(|dependency| {
            self.declaration(*dependency)
                .is_some_and(|declaration| declaration.status == HolTheoremStatus::Incomplete)
        });
        if !audit.has_holes() && !depends_on_incomplete {
            return Err(TheoremError::new(format!(
                "theorem draft `{name}` is complete; declare it as checked evidence"
            )));
        }
        let mut direct_constant_dependencies = term_constant_dependencies(&statement);
        direct_constant_dependencies.extend(audit.constant_dependencies().iter().copied());
        self.insert_checked(
            id,
            HolTheoremDeclaration {
                name,
                status: HolTheoremStatus::Incomplete,
                type_parameters,
                term_parameters,
                statement,
                direct_dependencies,
                direct_constant_dependencies,
                audit,
                incomplete_draft: Some(draft),
            },
        )?;
        Ok(id)
    }

    pub fn declare_trusted_axiom(
        &mut self,
        types: &TypeSignature,
        constants: &TermSignature,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        statement: CoreTerm,
    ) -> Result<TheoremId, TheoremError> {
        self.declare_trusted_axiom_with_parameters(
            types,
            constants,
            name,
            type_parameters,
            Vec::new(),
            statement,
        )
    }

    pub fn declare_trusted_axiom_with_parameters(
        &mut self,
        types: &TypeSignature,
        constants: &TermSignature,
        name: impl Into<String>,
        type_parameters: Vec<TypeParameter>,
        term_parameters: Vec<CoreType>,
        statement: CoreTerm,
    ) -> Result<TheoremId, TheoremError> {
        let name = name.into();
        let id = self.reserve_id(&name)?;
        types.validate_scheme(&type_parameters, &CoreType::Prop)?;
        for parameter in &term_parameters {
            types.validate_scheme(&type_parameters, parameter)?;
        }
        validate_term_type_scheme(types, &type_parameters, &statement)?;
        let term_context = term_parameters
            .iter()
            .cloned()
            .fold(TermContext::new(), TermContext::with_bound);
        let actual = infer_type(types, constants, &term_context, &statement)?;
        if actual != CoreType::Prop {
            return Err(TheoremError::new(format!(
                "trusted axiom `{name}` has type `{actual:?}`, not `Prop`"
            )));
        }
        let direct_constant_dependencies = term_constant_dependencies(&statement);
        self.insert_checked(
            id,
            HolTheoremDeclaration {
                name,
                status: HolTheoremStatus::TrustedAxiom,
                type_parameters,
                term_parameters,
                statement,
                direct_dependencies: BTreeSet::new(),
                direct_constant_dependencies,
                audit: HolProofAudit::default(),
                incomplete_draft: None,
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
                        term_arguments: Vec::new(),
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
    fn checked_term_templates_instantiate_simultaneously_under_ambient_binders() {
        let fixture = fixture();
        let mut theorems = HolTheoremSignature::new();
        // Declaration order is x, ignored; the nearest template binder is the
        // last parameter, so x is Bound(1).
        let first_identity = theorems
            .check_and_declare_with_parameters(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "first_identity",
                Vec::new(),
                vec![fixture.nat.clone(), fixture.nat.clone()],
                CoreTerm::equality(fixture.nat.clone(), CoreTerm::Bound(1), CoreTerm::Bound(1)),
                kernel(HolDraftProof::EqualityRefl(CoreTerm::Bound(1))),
            )
            .expect("two-parameter theorem template");

        let ambient_statement = CoreTerm::forall(
            fixture.nat.clone(),
            CoreTerm::equality(fixture.nat.clone(), CoreTerm::Bound(0), CoreTerm::Bound(0)),
        );
        let ambient = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "ambient_identity",
                Vec::new(),
                ambient_statement,
                kernel(HolDraftProof::ForallIntro {
                    domain: fixture.nat.clone(),
                    body: Box::new(HolDraftProof::TheoremRef {
                        theorem: first_identity,
                        type_arguments: Vec::new(),
                        term_arguments: vec![CoreTerm::Bound(0), CoreTerm::Constant(fixture.zero)],
                    }),
                }),
            )
            .expect("ambient variable survives simultaneous instantiation");
        assert_eq!(
            theorems
                .declaration(ambient)
                .expect("stored ambient theorem")
                .direct_dependencies,
            BTreeSet::from([first_identity])
        );

        let missing = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "missing_term_argument",
                Vec::new(),
                CoreTerm::Truth,
                kernel(HolDraftProof::TheoremRef {
                    theorem: first_identity,
                    type_arguments: Vec::new(),
                    term_arguments: vec![CoreTerm::Constant(fixture.zero)],
                }),
            )
            .expect_err("term-template arity is explicit");
        assert!(missing.message.contains("expects 2 explicit term argument"));
        assert_eq!(theorems.resolve("missing_term_argument"), None);

        let wrong_type = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "wrong_term_argument",
                Vec::new(),
                CoreTerm::Truth,
                kernel(HolDraftProof::TheoremRef {
                    theorem: first_identity,
                    type_arguments: Vec::new(),
                    term_arguments: vec![CoreTerm::Truth, CoreTerm::Constant(fixture.zero)],
                }),
            )
            .expect_err("term-template argument types are checked");
        assert!(wrong_type.message.contains("term argument has type"));
        assert_eq!(theorems.resolve("wrong_term_argument"), None);
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
                    term_arguments: Vec::new(),
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

    #[test]
    fn explicitly_trusted_axioms_are_typed_and_referenceable() {
        let fixture = fixture();
        let mut theorems = HolTheoremSignature::new();
        let axiom = theorems
            .declare_trusted_axiom(
                &fixture.types,
                &fixture.constants,
                "trusted_truth",
                Vec::new(),
                CoreTerm::Truth,
            )
            .expect("typed trusted axiom");
        assert_eq!(
            theorems.declaration(axiom).expect("stored axiom").status,
            HolTheoremStatus::TrustedAxiom
        );

        let user = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "uses_trusted_truth",
                Vec::new(),
                CoreTerm::Truth,
                kernel(HolDraftProof::TheoremRef {
                    theorem: axiom,
                    type_arguments: Vec::new(),
                    term_arguments: Vec::new(),
                }),
            )
            .expect("kernel-visible trusted axiom");
        assert_eq!(
            theorems
                .declaration(user)
                .expect("stored axiom user")
                .direct_dependencies,
            BTreeSet::from([axiom])
        );

        let non_prop = theorems
            .declare_trusted_axiom(
                &fixture.types,
                &fixture.constants,
                "bad_axiom",
                Vec::new(),
                CoreTerm::Constant(fixture.zero),
            )
            .expect_err("axioms must still be propositions");
        assert!(non_prop.message.contains("not `Prop`"));
        assert_eq!(theorems.resolve("bad_axiom"), None);
    }

    #[test]
    fn incomplete_drafts_are_stored_but_never_become_kernel_evidence() {
        let fixture = fixture();
        let mut theorems = HolTheoremSignature::new();
        let hole = theorems
            .check_and_declare_incomplete(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "unfinished_truth",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::Sorry {
                    target: CoreTerm::Truth,
                },
            )
            .expect("typed incomplete theorem");
        let hole_declaration = theorems.declaration(hole).expect("stored draft");
        assert_eq!(hole_declaration.status, HolTheoremStatus::Incomplete);
        assert!(hole_declaration.audit.has_holes());
        assert!(hole_declaration.incomplete_draft.is_some());

        let rejected_kernel_user = theorems
            .check_and_declare(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "laundered_truth",
                Vec::new(),
                CoreTerm::Truth,
                kernel(HolDraftProof::TheoremRef {
                    theorem: hole,
                    type_arguments: Vec::new(),
                    term_arguments: Vec::new(),
                }),
            )
            .expect_err("an incomplete theorem is not kernel evidence");
        assert!(rejected_kernel_user.message.contains("not kernel evidence"));
        assert_eq!(theorems.resolve("laundered_truth"), None);

        let dependent = theorems
            .check_and_declare_incomplete(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "unfinished_facade",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TheoremRef {
                    theorem: hole,
                    type_arguments: Vec::new(),
                    term_arguments: Vec::new(),
                },
            )
            .expect("incompleteness propagates through draft references");
        let dependent = theorems
            .declaration(dependent)
            .expect("stored facade draft");
        assert_eq!(dependent.status, HolTheoremStatus::Incomplete);
        assert!(!dependent.audit.has_holes());
        assert_eq!(dependent.direct_dependencies, BTreeSet::from([hole]));
        assert!(dependent.incomplete_draft.is_some());

        let complete = theorems
            .check_and_declare_incomplete(
                &fixture.types,
                &fixture.constants,
                &fixture.inductives,
                "actually_complete",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TruthIntro,
            )
            .expect_err("complete evidence belongs in a checked declaration");
        assert!(complete.message.contains("is complete"));
        assert_eq!(theorems.resolve("actually_complete"), None);
    }
}
