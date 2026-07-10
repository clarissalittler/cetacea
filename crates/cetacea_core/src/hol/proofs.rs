use std::fmt;

use super::inductive::{InductiveError, InductiveSignature};
use super::terms::{
    definitionally_equal, infer_type, instantiate_binder, normalize, shift_under_new_binder,
    CoreTerm, TermContext, TermError, TermSignature,
};
use super::types::{CoreType, TypeConstructorId, TypeError, TypeSignature};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HolDraftProof {
    Hypothesis(u32),
    TruthIntro,
    FalseElim {
        proof_false: Box<HolDraftProof>,
        target: CoreTerm,
    },
    AndIntro(Box<HolDraftProof>, Box<HolDraftProof>),
    AndElimLeft(Box<HolDraftProof>),
    AndElimRight(Box<HolDraftProof>),
    OrIntroLeft {
        proof_left: Box<HolDraftProof>,
        right: CoreTerm,
    },
    OrIntroRight {
        left: CoreTerm,
        proof_right: Box<HolDraftProof>,
    },
    OrElim {
        proof_or: Box<HolDraftProof>,
        left_case: Box<HolDraftProof>,
        right_case: Box<HolDraftProof>,
        target: CoreTerm,
    },
    ImpIntro {
        premise: CoreTerm,
        body: Box<HolDraftProof>,
    },
    ImpElim {
        proof_implication: Box<HolDraftProof>,
        proof_argument: Box<HolDraftProof>,
    },
    EqualityRefl(CoreTerm),
    EqualityElim {
        proof_equality: Box<HolDraftProof>,
        motive: CoreTerm,
        proof_left: Box<HolDraftProof>,
    },
    ConstructorDisjoint {
        proof_equality: Box<HolDraftProof>,
    },
    ConstructorInjective {
        proof_equality: Box<HolDraftProof>,
        field: usize,
    },
    ForallIntro {
        domain: CoreType,
        body: Box<HolDraftProof>,
    },
    ForallElim {
        proof_forall: Box<HolDraftProof>,
        argument: CoreTerm,
    },
    ExistsIntro {
        domain: CoreType,
        body: CoreTerm,
        witness: CoreTerm,
        proof_body: Box<HolDraftProof>,
    },
    ExistsElim {
        proof_exists: Box<HolDraftProof>,
        body: Box<HolDraftProof>,
        target: CoreTerm,
    },
    Induction {
        datatype: TypeConstructorId,
        type_arguments: Vec<CoreType>,
        motive: CoreTerm,
        scrutinee: CoreTerm,
        /// One case per constructor, in declaration order.
        cases: Vec<HolDraftProof>,
    },
    Sorry {
        target: CoreTerm,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HolKernelProof(HolDraftProof);

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HolProofAudit {
    uses_induction: bool,
}

impl HolProofAudit {
    pub fn uses_induction(self) -> bool {
        self.uses_induction
    }
}

impl TryFrom<HolDraftProof> for HolKernelProof {
    type Error = ProofError;

    fn try_from(proof: HolDraftProof) -> Result<Self, Self::Error> {
        if proof_has_hole(&proof) {
            Err(ProofError::new(
                "HOL draft proof contains `sorry`; incomplete drafts are not kernel proofs",
            ))
        } else {
            Ok(Self(proof))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofError {
    pub message: String,
}

impl ProofError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for ProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ProofError {}

impl From<TermError> for ProofError {
    fn from(error: TermError) -> Self {
        Self::new(error.message)
    }
}

impl From<TypeError> for ProofError {
    fn from(error: TypeError) -> Self {
        Self::new(error.message)
    }
}

impl From<InductiveError> for ProofError {
    fn from(error: InductiveError) -> Self {
        Self::new(error.message)
    }
}

/// Propositions available as proof hypotheses, nearest binder first.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HolProofContext {
    hypotheses: Vec<CoreTerm>,
}

impl HolProofContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_assumption(
        mut self,
        types: &TypeSignature,
        constants: &TermSignature,
        term_context: &TermContext,
        proposition: CoreTerm,
    ) -> Result<Self, ProofError> {
        expect_proposition(types, constants, term_context, &proposition, "hypothesis")?;
        self.hypotheses.insert(0, proposition);
        Ok(self)
    }

    fn lookup(&self, index: u32) -> Result<&CoreTerm, ProofError> {
        self.hypotheses.get(index as usize).ok_or_else(|| {
            ProofError::new(format!(
                "unknown proof hypothesis index `{index}` in context of depth {}",
                self.hypotheses.len()
            ))
        })
    }

    fn under_term_binder(&self) -> Result<Self, ProofError> {
        Ok(Self {
            hypotheses: self
                .hypotheses
                .iter()
                .map(shift_under_new_binder)
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

pub fn check_hol_proof(
    types: &TypeSignature,
    constants: &TermSignature,
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolKernelProof,
    expected: &CoreTerm,
) -> Result<(), ProofError> {
    check_hol_proof_audit(
        types,
        constants,
        term_context,
        proof_context,
        proof,
        expected,
    )
    .map(|_| ())
}

pub fn check_hol_proof_audit(
    types: &TypeSignature,
    constants: &TermSignature,
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolKernelProof,
    expected: &CoreTerm,
) -> Result<HolProofAudit, ProofError> {
    check_hol_proof_internal(
        types,
        constants,
        None,
        term_context,
        proof_context,
        proof,
        expected,
    )?;
    Ok(audit_proof(&proof.0))
}

pub fn check_hol_proof_with_inductives(
    types: &TypeSignature,
    constants: &TermSignature,
    inductives: &InductiveSignature,
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolKernelProof,
    expected: &CoreTerm,
) -> Result<(), ProofError> {
    check_hol_proof_with_inductives_audit(
        types,
        constants,
        inductives,
        term_context,
        proof_context,
        proof,
        expected,
    )
    .map(|_| ())
}

pub fn check_hol_proof_with_inductives_audit(
    types: &TypeSignature,
    constants: &TermSignature,
    inductives: &InductiveSignature,
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolKernelProof,
    expected: &CoreTerm,
) -> Result<HolProofAudit, ProofError> {
    check_hol_proof_internal(
        types,
        constants,
        Some(inductives),
        term_context,
        proof_context,
        proof,
        expected,
    )?;
    Ok(audit_proof(&proof.0))
}

fn check_hol_proof_internal(
    types: &TypeSignature,
    constants: &TermSignature,
    inductives: Option<&InductiveSignature>,
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolKernelProof,
    expected: &CoreTerm,
) -> Result<(), ProofError> {
    expect_proposition(types, constants, term_context, expected, "proof target")?;
    let actual = infer_proof(
        types,
        constants,
        inductives,
        term_context,
        proof_context,
        &proof.0,
    )?;
    if proposition_equal(types, constants, term_context, &actual, expected)? {
        Ok(())
    } else {
        Err(ProofError::new(format!(
            "proof establishes `{actual:?}`, but expected `{expected:?}`"
        )))
    }
}

fn infer_proof(
    types: &TypeSignature,
    constants: &TermSignature,
    inductives: Option<&InductiveSignature>,
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolDraftProof,
) -> Result<CoreTerm, ProofError> {
    match proof {
        HolDraftProof::Hypothesis(index) => Ok(proof_context.lookup(*index)?.clone()),
        HolDraftProof::TruthIntro => Ok(CoreTerm::Truth),
        HolDraftProof::FalseElim {
            proof_false,
            target,
        } => {
            check_draft(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_false,
                &CoreTerm::Falsity,
            )?;
            expect_proposition(
                types,
                constants,
                term_context,
                target,
                "false-elimination target",
            )?;
            Ok(target.clone())
        }
        HolDraftProof::AndIntro(left, right) => Ok(CoreTerm::and(
            infer_proof(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                left,
            )?,
            infer_proof(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                right,
            )?,
        )),
        HolDraftProof::AndElimLeft(proof_and) => {
            let proposition = normalized_proof_formula(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_and,
            )?;
            let CoreTerm::And(left, _) = proposition else {
                return Err(ProofError::new(
                    "and-left elimination expects a conjunction",
                ));
            };
            Ok(*left)
        }
        HolDraftProof::AndElimRight(proof_and) => {
            let proposition = normalized_proof_formula(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_and,
            )?;
            let CoreTerm::And(_, right) = proposition else {
                return Err(ProofError::new(
                    "and-right elimination expects a conjunction",
                ));
            };
            Ok(*right)
        }
        HolDraftProof::OrIntroLeft { proof_left, right } => {
            expect_proposition(types, constants, term_context, right, "right disjunct")?;
            Ok(CoreTerm::or(
                infer_proof(
                    types,
                    constants,
                    inductives,
                    term_context,
                    proof_context,
                    proof_left,
                )?,
                right.clone(),
            ))
        }
        HolDraftProof::OrIntroRight { left, proof_right } => {
            expect_proposition(types, constants, term_context, left, "left disjunct")?;
            Ok(CoreTerm::or(
                left.clone(),
                infer_proof(
                    types,
                    constants,
                    inductives,
                    term_context,
                    proof_context,
                    proof_right,
                )?,
            ))
        }
        HolDraftProof::OrElim {
            proof_or,
            left_case,
            right_case,
            target,
        } => {
            expect_proposition(
                types,
                constants,
                term_context,
                target,
                "or-elimination target",
            )?;
            let proposition = normalized_proof_formula(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_or,
            )?;
            let CoreTerm::Or(left, right) = proposition else {
                return Err(ProofError::new("or elimination expects a disjunction"));
            };
            let left_context =
                proof_context
                    .clone()
                    .with_assumption(types, constants, term_context, *left)?;
            let right_context =
                proof_context
                    .clone()
                    .with_assumption(types, constants, term_context, *right)?;
            check_draft(
                types,
                constants,
                inductives,
                term_context,
                &left_context,
                left_case,
                target,
            )?;
            check_draft(
                types,
                constants,
                inductives,
                term_context,
                &right_context,
                right_case,
                target,
            )?;
            Ok(target.clone())
        }
        HolDraftProof::ImpIntro { premise, body } => {
            let body_context = proof_context.clone().with_assumption(
                types,
                constants,
                term_context,
                premise.clone(),
            )?;
            let conclusion = infer_proof(
                types,
                constants,
                inductives,
                term_context,
                &body_context,
                body,
            )?;
            Ok(CoreTerm::implies(premise.clone(), conclusion))
        }
        HolDraftProof::ImpElim {
            proof_implication,
            proof_argument,
        } => {
            let proposition = normalized_proof_formula(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_implication,
            )?;
            let CoreTerm::Implies(premise, conclusion) = proposition else {
                return Err(ProofError::new(
                    "implication elimination expects an implication",
                ));
            };
            check_draft(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_argument,
                &premise,
            )?;
            Ok(*conclusion)
        }
        HolDraftProof::EqualityRefl(term) => {
            let ty = infer_type(types, constants, term_context, term)?;
            Ok(CoreTerm::equality(ty, term.clone(), term.clone()))
        }
        HolDraftProof::EqualityElim {
            proof_equality,
            motive,
            proof_left,
        } => {
            let equality = normalized_proof_formula(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_equality,
            )?;
            let CoreTerm::Equality { ty, left, right } = equality else {
                return Err(ProofError::new(
                    "equality elimination expects an equality proof",
                ));
            };
            let motive_type = infer_type(types, constants, term_context, motive)?;
            let expected_motive = CoreType::arrow(ty, CoreType::Prop);
            if motive_type != expected_motive {
                return Err(ProofError::new(format!(
                    "equality motive has type `{motive_type:?}`, but expected `{expected_motive:?}`"
                )));
            }
            let left_target = normalize(
                types,
                constants,
                term_context,
                &CoreTerm::apply(motive.clone(), *left),
            )?;
            check_draft(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_left,
                &left_target,
            )?;
            Ok(normalize(
                types,
                constants,
                term_context,
                &CoreTerm::apply(motive.clone(), *right),
            )?)
        }
        HolDraftProof::ConstructorDisjoint { proof_equality } => {
            let inductive_signature = inductives.ok_or_else(|| {
                ProofError::new(
                    "constructor disjointness requires a checked inductive signature at the kernel boundary",
                )
            })?;
            let equality = normalized_proof_formula(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_equality,
            )?;
            let CoreTerm::Equality { left, right, .. } = equality else {
                return Err(ProofError::new(
                    "constructor disjointness expects an equality proof",
                ));
            };
            let left = constructor_application(inductive_signature, &left)?;
            let right = constructor_application(inductive_signature, &right)?;
            if left.datatype != right.datatype {
                return Err(ProofError::new(
                    "constructor equality compares different inductive datatypes",
                ));
            }
            if left.constructor == right.constructor {
                return Err(ProofError::new(
                    "constructor disjointness needs two distinct constructors",
                ));
            }
            Ok(CoreTerm::Falsity)
        }
        HolDraftProof::ConstructorInjective {
            proof_equality,
            field,
        } => {
            let inductive_signature = inductives.ok_or_else(|| {
                ProofError::new(
                    "constructor injectivity requires a checked inductive signature at the kernel boundary",
                )
            })?;
            let equality = normalized_proof_formula(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_equality,
            )?;
            let CoreTerm::Equality { left, right, .. } = equality else {
                return Err(ProofError::new(
                    "constructor injectivity expects an equality proof",
                ));
            };
            let left = constructor_application(inductive_signature, &left)?;
            let right = constructor_application(inductive_signature, &right)?;
            if left.datatype != right.datatype || left.constructor != right.constructor {
                return Err(ProofError::new(
                    "constructor injectivity needs applications of the same constructor",
                ));
            }
            let left_field = left.fields.get(*field).ok_or_else(|| {
                ProofError::new(format!(
                    "constructor `{}` has {} field(s), so field `{field}` is invalid",
                    left.constructor.0,
                    left.fields.len()
                ))
            })?;
            let right_field = right.fields.get(*field).ok_or_else(|| {
                ProofError::new(format!(
                    "constructor `{}` has {} field(s), so field `{field}` is invalid",
                    right.constructor.0,
                    right.fields.len()
                ))
            })?;
            let field_type = infer_type(types, constants, term_context, left_field)?;
            Ok(CoreTerm::equality(
                field_type,
                (*left_field).clone(),
                (*right_field).clone(),
            ))
        }
        HolDraftProof::ForallIntro { domain, body } => {
            types.validate(domain)?;
            let body_term_context = term_context.clone().with_bound(domain.clone());
            let body_proof_context = proof_context.under_term_binder()?;
            let proposition = infer_proof(
                types,
                constants,
                inductives,
                &body_term_context,
                &body_proof_context,
                body,
            )?;
            Ok(CoreTerm::forall(domain.clone(), proposition))
        }
        HolDraftProof::ForallElim {
            proof_forall,
            argument,
        } => {
            let proposition = normalized_proof_formula(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_forall,
            )?;
            let CoreTerm::Forall { domain, body } = proposition else {
                return Err(ProofError::new(
                    "forall elimination expects a universal proof",
                ));
            };
            Ok(instantiate_binder(
                types,
                constants,
                term_context,
                &domain,
                &body,
                argument,
            )?)
        }
        HolDraftProof::ExistsIntro {
            domain,
            body,
            witness,
            proof_body,
        } => {
            let existential = CoreTerm::exists(domain.clone(), body.clone());
            expect_proposition(
                types,
                constants,
                term_context,
                &existential,
                "existential target",
            )?;
            let instantiated =
                instantiate_binder(types, constants, term_context, domain, body, witness)?;
            check_draft(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_body,
                &instantiated,
            )?;
            Ok(existential)
        }
        HolDraftProof::ExistsElim {
            proof_exists,
            body,
            target,
        } => {
            expect_proposition(
                types,
                constants,
                term_context,
                target,
                "exists-elimination target",
            )?;
            let proposition = normalized_proof_formula(
                types,
                constants,
                inductives,
                term_context,
                proof_context,
                proof_exists,
            )?;
            let CoreTerm::Exists {
                domain,
                body: exists_body,
            } = proposition
            else {
                return Err(ProofError::new(
                    "exists elimination expects an existential proof",
                ));
            };
            let body_term_context = term_context.clone().with_bound(domain);
            let shifted_target = shift_under_new_binder(target)?;
            let body_proof_context = proof_context.under_term_binder()?.with_assumption(
                types,
                constants,
                &body_term_context,
                *exists_body,
            )?;
            check_draft(
                types,
                constants,
                inductives,
                &body_term_context,
                &body_proof_context,
                body,
                &shifted_target,
            )?;
            Ok(target.clone())
        }
        HolDraftProof::Induction {
            datatype,
            type_arguments,
            motive,
            scrutinee,
            cases,
        } => {
            let inductive_signature = inductives.ok_or_else(|| {
                ProofError::new(
                    "induction proof requires a checked inductive signature at the kernel boundary",
                )
            })?;
            let declaration = inductive_signature.declaration(*datatype).ok_or_else(|| {
                ProofError::new(format!(
                    "type constructor `{}` is not a checked inductive datatype",
                    datatype.0
                ))
            })?;
            let datatype_type = CoreType::constructor(*datatype, type_arguments.clone());
            types.validate(&datatype_type)?;
            let actual_scrutinee = infer_type(types, constants, term_context, scrutinee)?;
            if actual_scrutinee != datatype_type {
                return Err(ProofError::new(format!(
                    "induction scrutinee has type `{actual_scrutinee:?}`, but expected `{datatype_type:?}`"
                )));
            }
            let actual_motive = infer_type(types, constants, term_context, motive)?;
            let expected_motive = CoreType::arrow(datatype_type, CoreType::Prop);
            if actual_motive != expected_motive {
                return Err(ProofError::new(format!(
                    "induction motive has type `{actual_motive:?}`, but expected `{expected_motive:?}`"
                )));
            }
            if cases.len() != declaration.constructors.len() {
                return Err(ProofError::new(format!(
                    "induction over `{}` needs {} case(s), but got {}",
                    declaration.name,
                    declaration.constructors.len(),
                    cases.len()
                )));
            }

            for (case, constructor) in cases.iter().zip(&declaration.constructors) {
                let instantiated = inductive_signature.instantiate_constructor(
                    types,
                    constructor.constant,
                    type_arguments,
                )?;
                let mut case_term_context = term_context.clone();
                for field_type in instantiated.field_types.iter().rev() {
                    case_term_context = case_term_context.with_bound(field_type.clone());
                }

                let mut case_proof_context = proof_context.clone();
                let mut shifted_motive = motive.clone();
                for _ in &instantiated.field_types {
                    case_proof_context = case_proof_context.under_term_binder()?;
                    shifted_motive = shift_under_new_binder(&shifted_motive)?;
                }

                let mut constructor_term =
                    CoreTerm::instantiate_constant(constructor.constant, type_arguments.clone());
                for field_index in 0..instantiated.field_types.len() {
                    constructor_term =
                        CoreTerm::apply(constructor_term, CoreTerm::Bound(field_index as u32));
                }
                let case_target = normalize(
                    types,
                    constants,
                    &case_term_context,
                    &CoreTerm::apply(shifted_motive.clone(), constructor_term),
                )?;

                for recursive_field in instantiated.recursive_fields.iter().rev() {
                    let induction_hypothesis = normalize(
                        types,
                        constants,
                        &case_term_context,
                        &CoreTerm::apply(
                            shifted_motive.clone(),
                            CoreTerm::Bound(*recursive_field as u32),
                        ),
                    )?;
                    case_proof_context = case_proof_context.with_assumption(
                        types,
                        constants,
                        &case_term_context,
                        induction_hypothesis,
                    )?;
                }
                check_draft(
                    types,
                    constants,
                    inductives,
                    &case_term_context,
                    &case_proof_context,
                    case,
                    &case_target,
                )?;
            }

            Ok(normalize(
                types,
                constants,
                term_context,
                &CoreTerm::apply(motive.clone(), scrutinee.clone()),
            )?)
        }
        HolDraftProof::Sorry { .. } => Err(ProofError::new(
            "kernel proof unexpectedly contains a `sorry` hole",
        )),
    }
}

struct ConstructorApplication<'a> {
    datatype: TypeConstructorId,
    constructor: super::terms::ConstantId,
    fields: Vec<&'a CoreTerm>,
}

fn constructor_application<'a>(
    inductives: &InductiveSignature,
    term: &'a CoreTerm,
) -> Result<ConstructorApplication<'a>, ProofError> {
    let mut fields = Vec::new();
    let head = constructor_application_spine(term, &mut fields);
    let constructor = match head {
        CoreTerm::Constant(id) => *id,
        CoreTerm::TypeApplication { constant, .. } => *constant,
        _ => {
            return Err(ProofError::new(
                "no-confusion rule expects fully applied constructor terms",
            ));
        }
    };
    let (declaration, metadata) =
        inductives
            .constructor_declaration(constructor)
            .ok_or_else(|| {
                ProofError::new(format!(
                    "constant `{}` is not an inductive constructor",
                    constructor.0
                ))
            })?;
    if fields.len() != metadata.field_types.len() {
        return Err(ProofError::new(format!(
            "constructor `{}` expects {} field(s), but no-confusion received {}",
            metadata.name,
            metadata.field_types.len(),
            fields.len()
        )));
    }
    Ok(ConstructorApplication {
        datatype: declaration.type_constructor,
        constructor,
        fields,
    })
}

fn constructor_application_spine<'a>(
    term: &'a CoreTerm,
    fields: &mut Vec<&'a CoreTerm>,
) -> &'a CoreTerm {
    match term {
        CoreTerm::Apply { function, argument } => {
            let head = constructor_application_spine(function, fields);
            fields.push(argument);
            head
        }
        _ => term,
    }
}

fn check_draft(
    types: &TypeSignature,
    constants: &TermSignature,
    inductives: Option<&InductiveSignature>,
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolDraftProof,
    expected: &CoreTerm,
) -> Result<(), ProofError> {
    let actual = infer_proof(
        types,
        constants,
        inductives,
        term_context,
        proof_context,
        proof,
    )?;
    if proposition_equal(types, constants, term_context, &actual, expected)? {
        Ok(())
    } else {
        Err(ProofError::new(format!(
            "proof establishes `{actual:?}`, but expected `{expected:?}`"
        )))
    }
}

fn normalized_proof_formula(
    types: &TypeSignature,
    constants: &TermSignature,
    inductives: Option<&InductiveSignature>,
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolDraftProof,
) -> Result<CoreTerm, ProofError> {
    let proposition = infer_proof(
        types,
        constants,
        inductives,
        term_context,
        proof_context,
        proof,
    )?;
    Ok(normalize(types, constants, term_context, &proposition)?)
}

fn proposition_equal(
    types: &TypeSignature,
    constants: &TermSignature,
    term_context: &TermContext,
    left: &CoreTerm,
    right: &CoreTerm,
) -> Result<bool, ProofError> {
    Ok(definitionally_equal(
        types,
        constants,
        term_context,
        left,
        right,
    )?)
}

fn expect_proposition(
    types: &TypeSignature,
    constants: &TermSignature,
    term_context: &TermContext,
    proposition: &CoreTerm,
    role: &str,
) -> Result<(), ProofError> {
    let actual = infer_type(types, constants, term_context, proposition)?;
    if actual == CoreType::Prop {
        Ok(())
    } else {
        Err(ProofError::new(format!(
            "{role} must have type `Prop`, but has type `{actual:?}`"
        )))
    }
}

fn proof_has_hole(proof: &HolDraftProof) -> bool {
    match proof {
        HolDraftProof::Sorry { .. } => true,
        HolDraftProof::Hypothesis(_)
        | HolDraftProof::TruthIntro
        | HolDraftProof::EqualityRefl(_) => false,
        HolDraftProof::FalseElim { proof_false, .. }
        | HolDraftProof::AndElimLeft(proof_false)
        | HolDraftProof::AndElimRight(proof_false)
        | HolDraftProof::ForallIntro {
            body: proof_false, ..
        }
        | HolDraftProof::ForallElim {
            proof_forall: proof_false,
            ..
        } => proof_has_hole(proof_false),
        HolDraftProof::AndIntro(left, right)
        | HolDraftProof::ImpElim {
            proof_implication: left,
            proof_argument: right,
        } => proof_has_hole(left) || proof_has_hole(right),
        HolDraftProof::OrIntroLeft { proof_left, .. } => proof_has_hole(proof_left),
        HolDraftProof::OrIntroRight { proof_right, .. } => proof_has_hole(proof_right),
        HolDraftProof::OrElim {
            proof_or,
            left_case,
            right_case,
            ..
        } => proof_has_hole(proof_or) || proof_has_hole(left_case) || proof_has_hole(right_case),
        HolDraftProof::ImpIntro { body, .. } => proof_has_hole(body),
        HolDraftProof::EqualityElim {
            proof_equality,
            proof_left,
            ..
        } => proof_has_hole(proof_equality) || proof_has_hole(proof_left),
        HolDraftProof::ConstructorDisjoint { proof_equality }
        | HolDraftProof::ConstructorInjective { proof_equality, .. } => {
            proof_has_hole(proof_equality)
        }
        HolDraftProof::ExistsIntro { proof_body, .. } => proof_has_hole(proof_body),
        HolDraftProof::ExistsElim {
            proof_exists, body, ..
        } => proof_has_hole(proof_exists) || proof_has_hole(body),
        HolDraftProof::Induction { cases, .. } => cases.iter().any(proof_has_hole),
    }
}

fn audit_proof(proof: &HolDraftProof) -> HolProofAudit {
    HolProofAudit {
        uses_induction: proof_uses_induction(proof),
    }
}

fn proof_uses_induction(proof: &HolDraftProof) -> bool {
    match proof {
        HolDraftProof::Induction { .. } => true,
        HolDraftProof::Hypothesis(_)
        | HolDraftProof::TruthIntro
        | HolDraftProof::EqualityRefl(_)
        | HolDraftProof::Sorry { .. } => false,
        HolDraftProof::FalseElim { proof_false, .. }
        | HolDraftProof::AndElimLeft(proof_false)
        | HolDraftProof::AndElimRight(proof_false)
        | HolDraftProof::ForallIntro {
            body: proof_false, ..
        }
        | HolDraftProof::ForallElim {
            proof_forall: proof_false,
            ..
        }
        | HolDraftProof::OrIntroLeft {
            proof_left: proof_false,
            ..
        }
        | HolDraftProof::OrIntroRight {
            proof_right: proof_false,
            ..
        }
        | HolDraftProof::ConstructorDisjoint {
            proof_equality: proof_false,
        }
        | HolDraftProof::ConstructorInjective {
            proof_equality: proof_false,
            ..
        }
        | HolDraftProof::ExistsIntro {
            proof_body: proof_false,
            ..
        } => proof_uses_induction(proof_false),
        HolDraftProof::AndIntro(left, right)
        | HolDraftProof::ImpElim {
            proof_implication: left,
            proof_argument: right,
        } => proof_uses_induction(left) || proof_uses_induction(right),
        HolDraftProof::OrElim {
            proof_or,
            left_case,
            right_case,
            ..
        } => {
            proof_uses_induction(proof_or)
                || proof_uses_induction(left_case)
                || proof_uses_induction(right_case)
        }
        HolDraftProof::ImpIntro { body, .. } => proof_uses_induction(body),
        HolDraftProof::EqualityElim {
            proof_equality,
            proof_left,
            ..
        } => proof_uses_induction(proof_equality) || proof_uses_induction(proof_left),
        HolDraftProof::ExistsElim {
            proof_exists, body, ..
        } => proof_uses_induction(proof_exists) || proof_uses_induction(body),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
    use crate::hol::terms::ConstantId;
    use crate::hol::types::TypeParameter;

    struct Fixture {
        types: TypeSignature,
        terms: TermSignature,
        nat: CoreType,
        zero: ConstantId,
        one: ConstantId,
        atom_a: ConstantId,
        atom_b: ConstantId,
        predicate: ConstantId,
    }

    impl Fixture {
        fn new() -> Self {
            let mut types = TypeSignature::new();
            let nat_id = types.declare("Nat", 0, true).expect("declare Nat");
            let nat = CoreType::constructor(nat_id, Vec::new());
            let mut terms = TermSignature::new();
            let zero = terms
                .declare(&types, "zero", nat.clone())
                .expect("declare zero");
            let one = terms
                .declare(&types, "one", nat.clone())
                .expect("declare one");
            let atom_a = terms
                .declare(&types, "A", CoreType::Prop)
                .expect("declare A");
            let atom_b = terms
                .declare(&types, "B", CoreType::Prop)
                .expect("declare B");
            let predicate = terms
                .declare(&types, "P", CoreType::arrow(nat.clone(), CoreType::Prop))
                .expect("declare P");
            Self {
                types,
                terms,
                nat,
                zero,
                one,
                atom_a,
                atom_b,
                predicate,
            }
        }

        fn atom_a(&self) -> CoreTerm {
            CoreTerm::Constant(self.atom_a)
        }

        fn atom_b(&self) -> CoreTerm {
            CoreTerm::Constant(self.atom_b)
        }

        fn pred(&self, argument: CoreTerm) -> CoreTerm {
            CoreTerm::apply(CoreTerm::Constant(self.predicate), argument)
        }

        fn kernel(&self, proof: HolDraftProof) -> HolKernelProof {
            HolKernelProof::try_from(proof).expect("test proof should be hole-free")
        }

        fn check(
            &self,
            proof_context: &HolProofContext,
            proof: HolDraftProof,
            expected: &CoreTerm,
        ) -> Result<(), ProofError> {
            check_hol_proof(
                &self.types,
                &self.terms,
                &TermContext::new(),
                proof_context,
                &self.kernel(proof),
                expected,
            )
        }
    }

    fn declare_list(
        fixture: &mut Fixture,
    ) -> (
        InductiveSignature,
        TypeConstructorId,
        ConstantId,
        ConstantId,
    ) {
        let parameter = TypeParameter::any(90);
        let mut inductives = InductiveSignature::new();
        let list = inductives
            .declare(
                &mut fixture.types,
                &mut fixture.terms,
                InductiveSpec::new(
                    "List",
                    vec![parameter],
                    vec![
                        InductiveConstructorSpec::new("nil", Vec::new()),
                        InductiveConstructorSpec::new(
                            "cons",
                            vec![
                                InductiveFieldType::existing(CoreType::Parameter(parameter)),
                                InductiveFieldType::Recursive,
                            ],
                        ),
                    ],
                ),
            )
            .expect("List");
        let nil = fixture.terms.resolve("nil").expect("nil");
        let cons = fixture.terms.resolve("cons").expect("cons");
        (inductives, list, nil, cons)
    }

    #[test]
    fn implication_identity_checks_constructively() {
        let fixture = Fixture::new();
        let proof = HolDraftProof::ImpIntro {
            premise: fixture.atom_a(),
            body: Box::new(HolDraftProof::Hypothesis(0)),
        };
        fixture
            .check(
                &HolProofContext::new(),
                proof,
                &CoreTerm::implies(fixture.atom_a(), fixture.atom_a()),
            )
            .expect("A implies A");
    }

    #[test]
    fn conjunction_commutativity_checks() {
        let fixture = Fixture::new();
        let premise = CoreTerm::and(fixture.atom_a(), fixture.atom_b());
        let proof = HolDraftProof::ImpIntro {
            premise: premise.clone(),
            body: Box::new(HolDraftProof::AndIntro(
                Box::new(HolDraftProof::AndElimRight(Box::new(
                    HolDraftProof::Hypothesis(0),
                ))),
                Box::new(HolDraftProof::AndElimLeft(Box::new(
                    HolDraftProof::Hypothesis(0),
                ))),
            )),
        };
        fixture
            .check(
                &HolProofContext::new(),
                proof,
                &CoreTerm::implies(premise, CoreTerm::and(fixture.atom_b(), fixture.atom_a())),
            )
            .expect("and commutativity");
    }

    #[test]
    fn disjunction_elimination_checks_both_branches() {
        let fixture = Fixture::new();
        let premise = CoreTerm::or(fixture.atom_a(), fixture.atom_b());
        let target = CoreTerm::or(fixture.atom_b(), fixture.atom_a());
        let proof = HolDraftProof::ImpIntro {
            premise: premise.clone(),
            body: Box::new(HolDraftProof::OrElim {
                proof_or: Box::new(HolDraftProof::Hypothesis(0)),
                left_case: Box::new(HolDraftProof::OrIntroRight {
                    left: fixture.atom_b(),
                    proof_right: Box::new(HolDraftProof::Hypothesis(0)),
                }),
                right_case: Box::new(HolDraftProof::OrIntroLeft {
                    proof_left: Box::new(HolDraftProof::Hypothesis(0)),
                    right: fixture.atom_a(),
                }),
                target: target.clone(),
            }),
        };
        fixture
            .check(
                &HolProofContext::new(),
                proof,
                &CoreTerm::implies(premise, target),
            )
            .expect("or commutativity");
    }

    #[test]
    fn universal_elimination_instantiates_a_first_order_predicate() {
        let fixture = Fixture::new();
        let universal = CoreTerm::forall(fixture.nat.clone(), fixture.pred(CoreTerm::Bound(0)));
        let context = HolProofContext::new()
            .with_assumption(
                &fixture.types,
                &fixture.terms,
                &TermContext::new(),
                universal,
            )
            .expect("universal hypothesis");
        fixture
            .check(
                &context,
                HolDraftProof::ForallElim {
                    proof_forall: Box::new(HolDraftProof::Hypothesis(0)),
                    argument: CoreTerm::Constant(fixture.zero),
                },
                &fixture.pred(CoreTerm::Constant(fixture.zero)),
            )
            .expect("forall elimination");
    }

    #[test]
    fn higher_order_universal_introduction_is_supported() {
        let fixture = Fixture::new();
        let predicate_type = CoreType::arrow(fixture.nat.clone(), CoreType::Prop);
        let applied = CoreTerm::apply(CoreTerm::Bound(0), CoreTerm::Constant(fixture.zero));
        let expected = CoreTerm::forall(
            predicate_type.clone(),
            CoreTerm::implies(applied.clone(), applied.clone()),
        );
        let proof = HolDraftProof::ForallIntro {
            domain: predicate_type,
            body: Box::new(HolDraftProof::ImpIntro {
                premise: applied,
                body: Box::new(HolDraftProof::Hypothesis(0)),
            }),
        };
        fixture
            .check(&HolProofContext::new(), proof, &expected)
            .expect("higher-order forall introduction");
    }

    #[test]
    fn equality_elimination_uses_an_explicit_predicate_motive() {
        let fixture = Fixture::new();
        let equality = CoreTerm::equality(
            fixture.nat.clone(),
            CoreTerm::Constant(fixture.zero),
            CoreTerm::Constant(fixture.one),
        );
        let left_fact = fixture.pred(CoreTerm::Constant(fixture.zero));
        let context = HolProofContext::new()
            .with_assumption(
                &fixture.types,
                &fixture.terms,
                &TermContext::new(),
                equality,
            )
            .expect("equality hypothesis")
            .with_assumption(
                &fixture.types,
                &fixture.terms,
                &TermContext::new(),
                left_fact,
            )
            .expect("left fact");
        fixture
            .check(
                &context,
                HolDraftProof::EqualityElim {
                    proof_equality: Box::new(HolDraftProof::Hypothesis(1)),
                    motive: CoreTerm::Constant(fixture.predicate),
                    proof_left: Box::new(HolDraftProof::Hypothesis(0)),
                },
                &fixture.pred(CoreTerm::Constant(fixture.one)),
            )
            .expect("equality substitution");
    }

    #[test]
    fn equality_elimination_beta_reduces_a_lambda_motive() {
        let fixture = Fixture::new();
        let equality = CoreTerm::equality(
            fixture.nat.clone(),
            CoreTerm::Constant(fixture.zero),
            CoreTerm::Constant(fixture.one),
        );
        let context = HolProofContext::new()
            .with_assumption(
                &fixture.types,
                &fixture.terms,
                &TermContext::new(),
                equality,
            )
            .expect("equality hypothesis");
        let motive = CoreTerm::lambda(
            fixture.nat.clone(),
            CoreTerm::equality(fixture.nat.clone(), CoreTerm::Bound(0), CoreTerm::Bound(0)),
        );
        fixture
            .check(
                &context,
                HolDraftProof::EqualityElim {
                    proof_equality: Box::new(HolDraftProof::Hypothesis(0)),
                    motive,
                    proof_left: Box::new(HolDraftProof::EqualityRefl(CoreTerm::Constant(
                        fixture.zero,
                    ))),
                },
                &CoreTerm::equality(
                    fixture.nat.clone(),
                    CoreTerm::Constant(fixture.one),
                    CoreTerm::Constant(fixture.one),
                ),
            )
            .expect("lambda motive should beta-reduce on the right side");
    }

    #[test]
    fn existential_introduction_checks_the_witness_instance() {
        let fixture = Fixture::new();
        let body = fixture.pred(CoreTerm::Bound(0));
        let left_fact = fixture.pred(CoreTerm::Constant(fixture.zero));
        let context = HolProofContext::new()
            .with_assumption(
                &fixture.types,
                &fixture.terms,
                &TermContext::new(),
                left_fact,
            )
            .expect("P zero");
        fixture
            .check(
                &context,
                HolDraftProof::ExistsIntro {
                    domain: fixture.nat.clone(),
                    body: body.clone(),
                    witness: CoreTerm::Constant(fixture.zero),
                    proof_body: Box::new(HolDraftProof::Hypothesis(0)),
                },
                &CoreTerm::exists(fixture.nat.clone(), body),
            )
            .expect("exists introduction");
    }

    #[test]
    fn existential_elimination_preserves_outer_term_bindings() {
        let fixture = Fixture::new();
        let term_context = TermContext::new().with_bound(fixture.nat.clone());
        let existential = CoreTerm::exists(fixture.nat.clone(), fixture.pred(CoreTerm::Bound(0)));
        let outer_target = fixture.pred(CoreTerm::Bound(0));
        let proof_context = HolProofContext::new()
            .with_assumption(&fixture.types, &fixture.terms, &term_context, existential)
            .expect("exists hypothesis")
            .with_assumption(
                &fixture.types,
                &fixture.terms,
                &term_context,
                outer_target.clone(),
            )
            .expect("outer P(z)");
        let proof = fixture.kernel(HolDraftProof::ExistsElim {
            proof_exists: Box::new(HolDraftProof::Hypothesis(1)),
            // Under the witness and its property, the shifted outer P(z) is
            // still hypothesis 1. Hypothesis 0 is P(witness).
            body: Box::new(HolDraftProof::Hypothesis(1)),
            target: outer_target.clone(),
        });
        check_hol_proof(
            &fixture.types,
            &fixture.terms,
            &term_context,
            &proof_context,
            &proof,
            &outer_target,
        )
        .expect("exists elimination must not capture outer z");
    }

    #[test]
    fn false_elimination_can_target_any_proposition() {
        let fixture = Fixture::new();
        let context = HolProofContext::new()
            .with_assumption(
                &fixture.types,
                &fixture.terms,
                &TermContext::new(),
                CoreTerm::Falsity,
            )
            .expect("False hypothesis");
        fixture
            .check(
                &context,
                HolDraftProof::FalseElim {
                    proof_false: Box::new(HolDraftProof::Hypothesis(0)),
                    target: fixture.atom_a(),
                },
                &fixture.atom_a(),
            )
            .expect("false elimination");
    }

    #[test]
    fn draft_holes_never_cross_the_hol_kernel_boundary() {
        let fixture = Fixture::new();
        let draft = HolDraftProof::ImpIntro {
            premise: fixture.atom_a(),
            body: Box::new(HolDraftProof::Sorry {
                target: fixture.atom_a(),
            }),
        };
        let error = HolKernelProof::try_from(draft).expect_err("nested sorry must fail");
        assert!(error.message.contains("not kernel proofs"));
    }

    #[test]
    fn proof_hypothesis_indices_are_checked() {
        let fixture = Fixture::new();
        let error = fixture
            .check(
                &HolProofContext::new(),
                HolDraftProof::Hypothesis(0),
                &fixture.atom_a(),
            )
            .expect_err("empty proof context has no hypothesis zero");
        assert!(error.message.contains("unknown proof hypothesis index `0`"));
    }

    #[test]
    fn list_induction_checks_the_constructive_induction_principle() {
        let mut fixture = Fixture::new();
        let (inductives, list, nil, cons) = declare_list(&mut fixture);
        let list_nat = CoreType::constructor(list, vec![fixture.nat.clone()]);
        let property = fixture
            .terms
            .declare(
                &fixture.types,
                "ListProperty",
                CoreType::arrow(list_nat.clone(), CoreType::Prop),
            )
            .expect("list property");
        let property_of = |term| CoreTerm::apply(CoreTerm::Constant(property), term);
        let nil_nat = CoreTerm::instantiate_constant(nil, vec![fixture.nat.clone()]);

        // forall head, forall tail, P(tail) -> P(cons head tail)
        let cons_in_step = CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(cons, vec![fixture.nat.clone()]),
                CoreTerm::Bound(1),
            ),
            CoreTerm::Bound(0),
        );
        let step = CoreTerm::forall(
            fixture.nat.clone(),
            CoreTerm::forall(
                list_nat.clone(),
                CoreTerm::implies(property_of(CoreTerm::Bound(0)), property_of(cons_in_step)),
            ),
        );
        let expected = CoreTerm::implies(
            property_of(nil_nat.clone()),
            CoreTerm::implies(
                step.clone(),
                CoreTerm::forall(list_nat.clone(), property_of(CoreTerm::Bound(0))),
            ),
        );

        let cons_case = HolDraftProof::ImpElim {
            proof_implication: Box::new(HolDraftProof::ForallElim {
                proof_forall: Box::new(HolDraftProof::ForallElim {
                    // In the cons case: IH is hypothesis 0, the shifted step
                    // hypothesis is 1, head is term 0, and tail is term 1.
                    proof_forall: Box::new(HolDraftProof::Hypothesis(1)),
                    argument: CoreTerm::Bound(0),
                }),
                argument: CoreTerm::Bound(1),
            }),
            proof_argument: Box::new(HolDraftProof::Hypothesis(0)),
        };
        let proof = HolDraftProof::ImpIntro {
            premise: property_of(nil_nat),
            body: Box::new(HolDraftProof::ImpIntro {
                premise: step,
                body: Box::new(HolDraftProof::ForallIntro {
                    domain: list_nat,
                    body: Box::new(HolDraftProof::Induction {
                        datatype: list,
                        type_arguments: vec![fixture.nat.clone()],
                        motive: CoreTerm::Constant(property),
                        scrutinee: CoreTerm::Bound(0),
                        cases: vec![HolDraftProof::Hypothesis(1), cons_case],
                    }),
                }),
            }),
        };
        let kernel = fixture.kernel(proof);
        let audit = check_hol_proof_with_inductives_audit(
            &fixture.types,
            &fixture.terms,
            &inductives,
            &TermContext::new(),
            &HolProofContext::new(),
            &kernel,
            &expected,
        )
        .expect("constructive list induction principle");
        assert!(audit.uses_induction());
    }

    #[test]
    fn induction_requires_all_cases_and_the_inductive_kernel_signature() {
        let mut fixture = Fixture::new();
        let (inductives, list, nil, _) = declare_list(&mut fixture);
        let list_nat = CoreType::constructor(list, vec![fixture.nat.clone()]);
        let nil_nat = CoreTerm::instantiate_constant(nil, vec![fixture.nat.clone()]);
        let complete = HolDraftProof::Induction {
            datatype: list,
            type_arguments: vec![fixture.nat.clone()],
            motive: CoreTerm::lambda(list_nat.clone(), CoreTerm::Truth),
            scrutinee: nil_nat.clone(),
            cases: vec![HolDraftProof::TruthIntro, HolDraftProof::TruthIntro],
        };
        let kernel = fixture.kernel(complete);
        let missing_signature = check_hol_proof(
            &fixture.types,
            &fixture.terms,
            &TermContext::new(),
            &HolProofContext::new(),
            &kernel,
            &CoreTerm::Truth,
        )
        .expect_err("induction metadata is part of the kernel signature");
        assert!(missing_signature.message.contains("inductive signature"));

        let missing_case = fixture.kernel(HolDraftProof::Induction {
            datatype: list,
            type_arguments: vec![fixture.nat.clone()],
            motive: CoreTerm::lambda(list_nat, CoreTerm::Truth),
            scrutinee: nil_nat,
            cases: vec![HolDraftProof::TruthIntro],
        });
        let error = check_hol_proof_with_inductives(
            &fixture.types,
            &fixture.terms,
            &inductives,
            &TermContext::new(),
            &HolProofContext::new(),
            &missing_case,
            &CoreTerm::Truth,
        )
        .expect_err("one case cannot cover List");
        assert!(error.message.contains("needs 2 case"));
    }

    #[test]
    fn holes_inside_induction_cases_never_become_kernel_evidence() {
        let draft = HolDraftProof::Induction {
            datatype: TypeConstructorId(0),
            type_arguments: Vec::new(),
            motive: CoreTerm::lambda(CoreType::Prop, CoreTerm::Truth),
            scrutinee: CoreTerm::Truth,
            cases: vec![HolDraftProof::Sorry {
                target: CoreTerm::Truth,
            }],
        };
        let error = HolKernelProof::try_from(draft).expect_err("induction hole must fail");
        assert!(error.message.contains("not kernel proofs"));
    }

    #[test]
    fn datatype_no_confusion_proves_disjointness_and_field_injectivity() {
        let mut fixture = Fixture::new();
        let (inductives, list, nil, cons) = declare_list(&mut fixture);
        let list_nat = CoreType::constructor(list, vec![fixture.nat.clone()]);
        let nil_nat = CoreTerm::instantiate_constant(nil, vec![fixture.nat.clone()]);
        let cons_term = |head: CoreTerm| {
            CoreTerm::apply(
                CoreTerm::apply(
                    CoreTerm::instantiate_constant(cons, vec![fixture.nat.clone()]),
                    head,
                ),
                nil_nat.clone(),
            )
        };

        let disjoint_equality = CoreTerm::equality(
            list_nat.clone(),
            nil_nat.clone(),
            cons_term(CoreTerm::Constant(fixture.zero)),
        );
        let disjoint_context = HolProofContext::new()
            .with_assumption(
                &fixture.types,
                &fixture.terms,
                &TermContext::new(),
                disjoint_equality,
            )
            .expect("impossible constructor equality hypothesis");
        check_hol_proof_with_inductives(
            &fixture.types,
            &fixture.terms,
            &inductives,
            &TermContext::new(),
            &disjoint_context,
            &fixture.kernel(HolDraftProof::ConstructorDisjoint {
                proof_equality: Box::new(HolDraftProof::Hypothesis(0)),
            }),
            &CoreTerm::Falsity,
        )
        .expect("nil and cons are disjoint");

        let injective_equality = CoreTerm::equality(
            list_nat,
            cons_term(CoreTerm::Constant(fixture.zero)),
            cons_term(CoreTerm::Constant(fixture.one)),
        );
        let injective_context = HolProofContext::new()
            .with_assumption(
                &fixture.types,
                &fixture.terms,
                &TermContext::new(),
                injective_equality,
            )
            .expect("constructor equality hypothesis");
        check_hol_proof_with_inductives(
            &fixture.types,
            &fixture.terms,
            &inductives,
            &TermContext::new(),
            &injective_context,
            &fixture.kernel(HolDraftProof::ConstructorInjective {
                proof_equality: Box::new(HolDraftProof::Hypothesis(0)),
                field: 0,
            }),
            &CoreTerm::equality(
                fixture.nat.clone(),
                CoreTerm::Constant(fixture.zero),
                CoreTerm::Constant(fixture.one),
            ),
        )
        .expect("cons is injective in its head");
    }
}
