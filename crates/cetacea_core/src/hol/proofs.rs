use std::fmt;

use super::terms::{
    definitionally_equal, infer_type, instantiate_binder, normalize, shift_under_new_binder,
    CoreTerm, TermContext, TermError, TermSignature,
};
use super::types::{CoreType, TypeError, TypeSignature};

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
    Sorry {
        target: CoreTerm,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HolKernelProof(HolDraftProof);

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
    expect_proposition(types, constants, term_context, expected, "proof target")?;
    let actual = infer_proof(types, constants, term_context, proof_context, &proof.0)?;
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
            infer_proof(types, constants, term_context, proof_context, left)?,
            infer_proof(types, constants, term_context, proof_context, right)?,
        )),
        HolDraftProof::AndElimLeft(proof_and) => {
            let proposition =
                normalized_proof_formula(types, constants, term_context, proof_context, proof_and)?;
            let CoreTerm::And(left, _) = proposition else {
                return Err(ProofError::new(
                    "and-left elimination expects a conjunction",
                ));
            };
            Ok(*left)
        }
        HolDraftProof::AndElimRight(proof_and) => {
            let proposition =
                normalized_proof_formula(types, constants, term_context, proof_context, proof_and)?;
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
                infer_proof(types, constants, term_context, proof_context, proof_left)?,
                right.clone(),
            ))
        }
        HolDraftProof::OrIntroRight { left, proof_right } => {
            expect_proposition(types, constants, term_context, left, "left disjunct")?;
            Ok(CoreTerm::or(
                left.clone(),
                infer_proof(types, constants, term_context, proof_context, proof_right)?,
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
            let proposition =
                normalized_proof_formula(types, constants, term_context, proof_context, proof_or)?;
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
                term_context,
                &left_context,
                left_case,
                target,
            )?;
            check_draft(
                types,
                constants,
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
            let conclusion = infer_proof(types, constants, term_context, &body_context, body)?;
            Ok(CoreTerm::implies(premise.clone(), conclusion))
        }
        HolDraftProof::ImpElim {
            proof_implication,
            proof_argument,
        } => {
            let proposition = normalized_proof_formula(
                types,
                constants,
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
        HolDraftProof::ForallIntro { domain, body } => {
            types.validate(domain)?;
            let body_term_context = term_context.clone().with_bound(domain.clone());
            let body_proof_context = proof_context.under_term_binder()?;
            let proposition = infer_proof(
                types,
                constants,
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
                &body_term_context,
                &body_proof_context,
                body,
                &shifted_target,
            )?;
            Ok(target.clone())
        }
        HolDraftProof::Sorry { .. } => Err(ProofError::new(
            "kernel proof unexpectedly contains a `sorry` hole",
        )),
    }
}

fn check_draft(
    types: &TypeSignature,
    constants: &TermSignature,
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolDraftProof,
    expected: &CoreTerm,
) -> Result<(), ProofError> {
    let actual = infer_proof(types, constants, term_context, proof_context, proof)?;
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
    term_context: &TermContext,
    proof_context: &HolProofContext,
    proof: &HolDraftProof,
) -> Result<CoreTerm, ProofError> {
    let proposition = infer_proof(types, constants, term_context, proof_context, proof)?;
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
        HolDraftProof::ExistsIntro { proof_body, .. } => proof_has_hole(proof_body),
        HolDraftProof::ExistsElim {
            proof_exists, body, ..
        } => proof_has_hole(proof_exists) || proof_has_hole(body),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::terms::ConstantId;

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
}
