//! Executable H3 stop/go examples.
//!
//! These examples intentionally use the tiny name-resolving spike elaborator,
//! not hand-installed kernel metadata. Each report contains checked receipts
//! and the diagnostics from deliberate rejection cases.

use super::fragments::{DeclarationId, DeclarationReceipt, ProofFeature, StatementFragment};
use super::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{infer_type, CoreTerm, TermContext};
use super::types::{CoreType, TypeParameter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct H3ListSpikeReport {
    pub nodup_singleton: DeclarationReceipt,
    pub induction_theorem: DeclarationReceipt,
    pub declared_definitions: Vec<String>,
    pub type_error: String,
    pub termination_error: String,
    pub positivity_error: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct H3GraphSpikeReport {
    pub path_concatenation: DeclarationReceipt,
    pub declared_definitions: Vec<String>,
    pub type_error: String,
    pub termination_error: String,
    pub positivity_error: String,
}

/// Build and check the first H3 example: `List A`, `All`, `Member`, `Nodup`,
/// `append`, `length`, a computation proof, and a structural induction proof.
pub fn run_list_h3_spike() -> Result<H3ListSpikeReport, SpikeError> {
    let mut elaborator = SpikeElaborator::new();
    let nat_id = elaborator.declare_base_type("Nat", true)?;
    let nat = CoreType::constructor(nat_id, Vec::new());
    let zero = elaborator.declare_constant("zero", nat.clone())?;
    let succ = elaborator.declare_constant("succ", CoreType::arrow(nat.clone(), nat.clone()))?;

    let parameter = TypeParameter::any(0);
    let parameter_type = CoreType::Parameter(parameter);
    let list = elaborator.declare_inductive(InductiveSpec::new(
        "List",
        vec![parameter],
        vec![
            InductiveConstructorSpec::new("nil", Vec::new()),
            InductiveConstructorSpec::new(
                "cons",
                vec![
                    InductiveFieldType::existing(parameter_type.clone()),
                    InductiveFieldType::Recursive,
                ],
            ),
        ],
    ))?;
    let nil = elaborator.resolve_constant("nil")?;
    let cons = elaborator.resolve_constant("cons")?;
    let list_parameter = CoreType::constructor(list, vec![parameter_type.clone()]);

    let nil_layout = StructuralArmLayout::new(0, 0, 1);
    let cons_predicate_layout = StructuralArmLayout::new(2, 1, 1);
    let all = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "All".to_string(),
        type_parameters: vec![parameter],
        datatype: list,
        datatype_arguments: vec![parameter_type.clone()],
        fixed_parameter_types: vec![CoreType::arrow(parameter_type.clone(), CoreType::Prop)],
        result_type: CoreType::Prop,
        arms: vec![
            StructuralArmSpec::new(nil, CoreTerm::Truth),
            StructuralArmSpec::new(
                cons,
                CoreTerm::and(
                    CoreTerm::apply(
                        cons_predicate_layout
                            .fixed_parameter(0)
                            .expect("All predicate binder"),
                        cons_predicate_layout.field(0).expect("All head binder"),
                    ),
                    cons_predicate_layout
                        .recursive_result(0)
                        .expect("All recursive result"),
                ),
            ),
        ],
    })?;

    let member = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "Member".to_string(),
        type_parameters: vec![parameter],
        datatype: list,
        datatype_arguments: vec![parameter_type.clone()],
        fixed_parameter_types: vec![parameter_type.clone()],
        result_type: CoreType::Prop,
        arms: vec![
            StructuralArmSpec::new(nil, CoreTerm::Falsity),
            StructuralArmSpec::new(
                cons,
                CoreTerm::or(
                    CoreTerm::equality(
                        parameter_type.clone(),
                        cons_predicate_layout
                            .fixed_parameter(0)
                            .expect("Member needle binder"),
                        cons_predicate_layout.field(0).expect("Member head binder"),
                    ),
                    cons_predicate_layout
                        .recursive_result(0)
                        .expect("Member recursive result"),
                ),
            ),
        ],
    })?;

    let cons_nodup_layout = StructuralArmLayout::new(2, 1, 0);
    let member_of_tail = CoreTerm::apply(
        CoreTerm::apply(
            CoreTerm::instantiate_constant(member, vec![parameter_type.clone()]),
            cons_nodup_layout.field(0).expect("Nodup head binder"),
        ),
        cons_nodup_layout.field(1).expect("Nodup tail binder"),
    );
    let nodup = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "Nodup".to_string(),
        type_parameters: vec![parameter],
        datatype: list,
        datatype_arguments: vec![parameter_type.clone()],
        fixed_parameter_types: Vec::new(),
        result_type: CoreType::Prop,
        arms: vec![
            StructuralArmSpec::new(nil, CoreTerm::Truth),
            StructuralArmSpec::new(
                cons,
                CoreTerm::and(
                    CoreTerm::implies(member_of_tail, CoreTerm::Falsity),
                    cons_nodup_layout
                        .recursive_result(0)
                        .expect("Nodup recursive result"),
                ),
            ),
        ],
    })?;

    let append_layout = StructuralArmLayout::new(2, 1, 1);
    let append = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "append".to_string(),
        type_parameters: vec![parameter],
        datatype: list,
        datatype_arguments: vec![parameter_type.clone()],
        fixed_parameter_types: vec![list_parameter.clone()],
        result_type: list_parameter.clone(),
        arms: vec![
            StructuralArmSpec::new(
                nil,
                nil_layout
                    .fixed_parameter(0)
                    .expect("append right list binder"),
            ),
            StructuralArmSpec::new(
                cons,
                CoreTerm::apply(
                    CoreTerm::apply(
                        CoreTerm::instantiate_constant(cons, vec![parameter_type.clone()]),
                        append_layout.field(0).expect("append head binder"),
                    ),
                    append_layout
                        .recursive_result(0)
                        .expect("append recursive result"),
                ),
            ),
        ],
    })?;

    let length_layout = StructuralArmLayout::new(2, 1, 0);
    let length = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "length".to_string(),
        type_parameters: vec![parameter],
        datatype: list,
        datatype_arguments: vec![parameter_type.clone()],
        fixed_parameter_types: Vec::new(),
        result_type: nat.clone(),
        arms: vec![
            StructuralArmSpec::new(nil, CoreTerm::Constant(zero)),
            StructuralArmSpec::new(
                cons,
                CoreTerm::apply(
                    CoreTerm::Constant(succ),
                    length_layout
                        .recursive_result(0)
                        .expect("length recursive result"),
                ),
            ),
        ],
    })?;

    let structural_receipt = |id| {
        DeclarationReceipt::checked(
            DeclarationId(id),
            StatementFragment::FirstOrderInductive,
            [ProofFeature::StructuralRecursion],
            [],
        )
    };
    let _all_receipt = structural_receipt(1);
    let member_receipt = structural_receipt(2);
    let nodup_receipt = DeclarationReceipt::checked(
        DeclarationId(3),
        StatementFragment::FirstOrderInductive,
        [ProofFeature::StructuralRecursion],
        [&member_receipt],
    );
    let _append_receipt = structural_receipt(4);
    let _length_receipt = structural_receipt(5);

    let nil_nat = CoreTerm::instantiate_constant(nil, vec![nat.clone()]);
    let singleton = CoreTerm::apply(
        CoreTerm::apply(
            CoreTerm::instantiate_constant(cons, vec![nat.clone()]),
            CoreTerm::Constant(zero),
        ),
        nil_nat.clone(),
    );
    let nodup_singleton_statement = CoreTerm::apply(
        CoreTerm::instantiate_constant(nodup, vec![nat.clone()]),
        singleton,
    );
    let nodup_singleton = elaborator
        .check_theorem(
            DeclarationId(10),
            &nodup_singleton_statement,
            HolDraftProof::AndIntro(
                Box::new(HolDraftProof::ImpIntro {
                    premise: CoreTerm::Falsity,
                    body: Box::new(HolDraftProof::Hypothesis(0)),
                }),
                Box::new(HolDraftProof::TruthIntro),
            ),
            [&nodup_receipt],
        )?
        .receipt;

    let list_nat = CoreType::constructor(list, vec![nat.clone()]);
    let induction_statement = CoreTerm::forall(list_nat.clone(), CoreTerm::Truth);
    let induction_theorem = elaborator
        .check_theorem(
            DeclarationId(11),
            &induction_statement,
            HolDraftProof::ForallIntro {
                domain: list_nat.clone(),
                body: Box::new(HolDraftProof::Induction {
                    datatype: list,
                    type_arguments: vec![nat.clone()],
                    motive: CoreTerm::lambda(list_nat, CoreTerm::Truth),
                    scrutinee: CoreTerm::Bound(0),
                    cases: vec![HolDraftProof::TruthIntro, HolDraftProof::TruthIntro],
                }),
            },
            [],
        )?
        .receipt;

    let malformed_cons = CoreTerm::apply(
        CoreTerm::apply(
            CoreTerm::instantiate_constant(cons, vec![nat.clone()]),
            CoreTerm::Truth,
        ),
        nil_nat,
    );
    let type_error = infer_type(
        elaborator.types(),
        elaborator.constants(),
        &TermContext::new(),
        &malformed_cons,
    )
    .expect_err("cons[Nat] cannot contain a proposition")
    .message;

    let proposed_bad = elaborator.constants().next_constant_id()?;
    let bad_call = CoreTerm::apply(
        CoreTerm::instantiate_constant(proposed_bad, vec![parameter_type.clone()]),
        StructuralArmLayout::new(2, 1, 0)
            .field(1)
            .expect("bad recursive argument"),
    );
    let termination_error = elaborator
        .declare_structural_definition(StructuralDefinitionSpec {
            name: "bad_length".to_string(),
            type_parameters: vec![parameter],
            datatype: list,
            datatype_arguments: vec![parameter_type],
            fixed_parameter_types: Vec::new(),
            result_type: nat.clone(),
            arms: vec![
                StructuralArmSpec::new(nil, CoreTerm::Constant(zero)),
                StructuralArmSpec::new(cons, bad_call),
            ],
        })
        .expect_err("direct recursive call must be rejected")
        .message;

    let positivity_error = elaborator
        .declare_inductive(InductiveSpec::new(
            "Bad",
            Vec::new(),
            vec![InductiveConstructorSpec::new(
                "make_bad",
                vec![InductiveFieldType::arrow(
                    InductiveFieldType::Recursive,
                    InductiveFieldType::existing(nat),
                )],
            )],
        ))
        .expect_err("negative recursive occurrence must be rejected")
        .message;

    Ok(H3ListSpikeReport {
        nodup_singleton,
        induction_theorem,
        declared_definitions: vec![
            format!("All#{}", all.0),
            format!("Member#{}", member.0),
            format!("Nodup#{}", nodup.0),
            format!("append#{}", append.0),
            format!("length#{}", length.0),
        ],
        type_error,
        termination_error,
        positivity_error,
    })
}

/// Build a generic edge relation, an endpoint-aware `ValidPath` predicate, and
/// prove that concatenating valid paths preserves validity.
pub fn run_graph_h3_spike() -> Result<H3GraphSpikeReport, SpikeError> {
    let mut elaborator = SpikeElaborator::new();
    let vertex_id = elaborator.declare_base_type("Vertex", true)?;
    let vertex = CoreType::constructor(vertex_id, Vec::new());
    let vertex_a = elaborator.declare_constant("vertex_a", vertex.clone())?;

    let parameter = TypeParameter::first_order(20);
    let parameter_type = CoreType::Parameter(parameter);
    let list = elaborator.declare_inductive(InductiveSpec::new(
        "List",
        vec![parameter],
        vec![
            InductiveConstructorSpec::new("nil", Vec::new()),
            InductiveConstructorSpec::new(
                "cons",
                vec![
                    InductiveFieldType::existing(parameter_type.clone()),
                    InductiveFieldType::Recursive,
                ],
            ),
        ],
    ))?;
    let nil = elaborator.resolve_constant("nil")?;
    let cons = elaborator.resolve_constant("cons")?;
    let list_parameter = CoreType::constructor(list, vec![parameter_type.clone()]);

    let edge = elaborator.declare_polymorphic_constant(
        "Edge",
        vec![parameter],
        CoreType::arrow(
            parameter_type.clone(),
            CoreType::arrow(parameter_type.clone(), CoreType::Prop),
        ),
    )?;

    // The structural argument is last in the primitive definition, so the
    // checked constant has type List A -> List A -> List A as
    // `append right left`. The helper below presents the usual left/right order.
    let append_layout = StructuralArmLayout::new(2, 1, 1);
    let append = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "append".to_string(),
        type_parameters: vec![parameter],
        datatype: list,
        datatype_arguments: vec![parameter_type.clone()],
        fixed_parameter_types: vec![list_parameter.clone()],
        result_type: list_parameter.clone(),
        arms: vec![
            StructuralArmSpec::new(
                nil,
                StructuralArmLayout::new(0, 0, 1)
                    .fixed_parameter(0)
                    .expect("append right list"),
            ),
            StructuralArmSpec::new(
                cons,
                CoreTerm::apply(
                    CoreTerm::apply(
                        CoreTerm::instantiate_constant(cons, vec![parameter_type.clone()]),
                        append_layout.field(0).expect("append head"),
                    ),
                    append_layout
                        .recursive_result(0)
                        .expect("append recursive result"),
                ),
            ),
        ],
    })?;

    // ValidPath xs start finish means that following every vertex in xs from
    // `start` ends at `finish`. The recursive result is itself the binary
    // predicate for the tail, which permits the start vertex to advance.
    let chain_layout = StructuralArmLayout::new(2, 1, 0);
    let chain = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "ValidPath".to_string(),
        type_parameters: vec![parameter],
        datatype: list,
        datatype_arguments: vec![parameter_type.clone()],
        fixed_parameter_types: Vec::new(),
        result_type: CoreType::arrow(
            parameter_type.clone(),
            CoreType::arrow(parameter_type.clone(), CoreType::Prop),
        ),
        arms: vec![
            StructuralArmSpec::new(
                nil,
                CoreTerm::lambda(
                    parameter_type.clone(),
                    CoreTerm::lambda(
                        parameter_type.clone(),
                        // finish = start
                        CoreTerm::equality(
                            parameter_type.clone(),
                            CoreTerm::Bound(0),
                            CoreTerm::Bound(1),
                        ),
                    ),
                ),
            ),
            StructuralArmSpec::new(
                cons,
                CoreTerm::lambda(
                    parameter_type.clone(),
                    CoreTerm::lambda(
                        parameter_type.clone(),
                        CoreTerm::and(
                            // Under start and finish: finish 0, start 1,
                            // head 2, tail 3, recursive result 4.
                            CoreTerm::apply(
                                CoreTerm::apply(
                                    CoreTerm::instantiate_constant(
                                        edge,
                                        vec![parameter_type.clone()],
                                    ),
                                    CoreTerm::Bound(1),
                                ),
                                CoreTerm::Bound(2),
                            ),
                            CoreTerm::apply(
                                CoreTerm::apply(CoreTerm::Bound(4), CoreTerm::Bound(2)),
                                CoreTerm::Bound(0),
                            ),
                        ),
                    ),
                ),
            ),
        ],
    })?;

    let append_term = |left: CoreTerm, right: CoreTerm| {
        CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(append, vec![vertex.clone()]),
                right,
            ),
            left,
        )
    };
    let valid_path = |path: CoreTerm, start: CoreTerm, finish: CoreTerm| {
        CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::apply(
                    CoreTerm::instantiate_constant(chain, vec![vertex.clone()]),
                    path,
                ),
                start,
            ),
            finish,
        )
    };

    let list_vertex = CoreType::constructor(list, vec![vertex.clone()]);
    // Inside the five quantifiers: finish 0, middle 1, start 2,
    // right path 3, left path 4.
    let theorem_body = CoreTerm::implies(
        valid_path(CoreTerm::Bound(4), CoreTerm::Bound(2), CoreTerm::Bound(1)),
        CoreTerm::implies(
            valid_path(CoreTerm::Bound(3), CoreTerm::Bound(1), CoreTerm::Bound(0)),
            valid_path(
                append_term(CoreTerm::Bound(4), CoreTerm::Bound(3)),
                CoreTerm::Bound(2),
                CoreTerm::Bound(0),
            ),
        ),
    );
    let path_concatenation_statement = CoreTerm::forall(
        list_vertex.clone(),
        CoreTerm::forall(
            list_vertex.clone(),
            CoreTerm::forall(
                vertex.clone(),
                CoreTerm::forall(
                    vertex.clone(),
                    CoreTerm::forall(vertex.clone(), theorem_body),
                ),
            ),
        ),
    );

    // Motive for induction on the left path. Under the motive lambda and four
    // quantifiers: finish 0, middle 1, start 2, right 3, candidate left 4.
    let motive_body = CoreTerm::implies(
        valid_path(CoreTerm::Bound(4), CoreTerm::Bound(2), CoreTerm::Bound(1)),
        CoreTerm::implies(
            valid_path(CoreTerm::Bound(3), CoreTerm::Bound(1), CoreTerm::Bound(0)),
            valid_path(
                append_term(CoreTerm::Bound(4), CoreTerm::Bound(3)),
                CoreTerm::Bound(2),
                CoreTerm::Bound(0),
            ),
        ),
    );
    let motive = CoreTerm::lambda(
        list_vertex.clone(),
        CoreTerm::forall(
            list_vertex.clone(),
            CoreTerm::forall(
                vertex.clone(),
                CoreTerm::forall(
                    vertex.clone(),
                    CoreTerm::forall(vertex.clone(), motive_body),
                ),
            ),
        ),
    );

    // Nil case after right/start/middle/finish binders: finish 0, middle 1,
    // start 2, right 3. The normalized first premise is middle = start.
    let nil_equality = CoreTerm::equality(vertex.clone(), CoreTerm::Bound(1), CoreTerm::Bound(2));
    let nil_right_path = valid_path(CoreTerm::Bound(3), CoreTerm::Bound(1), CoreTerm::Bound(0));
    let equality_motive = CoreTerm::lambda(
        vertex.clone(),
        // Inside the equality motive: replacement start 0, finish 1,
        // old middle 2, old start 3, right 4.
        valid_path(CoreTerm::Bound(4), CoreTerm::Bound(0), CoreTerm::Bound(1)),
    );
    let nil_case = HolDraftProof::ForallIntro {
        domain: list_vertex.clone(),
        body: Box::new(HolDraftProof::ForallIntro {
            domain: vertex.clone(),
            body: Box::new(HolDraftProof::ForallIntro {
                domain: vertex.clone(),
                body: Box::new(HolDraftProof::ForallIntro {
                    domain: vertex.clone(),
                    body: Box::new(HolDraftProof::ImpIntro {
                        premise: nil_equality,
                        body: Box::new(HolDraftProof::ImpIntro {
                            premise: nil_right_path,
                            body: Box::new(HolDraftProof::EqualityElim {
                                proof_equality: Box::new(HolDraftProof::Hypothesis(1)),
                                motive: equality_motive,
                                proof_left: Box::new(HolDraftProof::Hypothesis(0)),
                            }),
                        }),
                    }),
                }),
            }),
        }),
    };

    // Cons case field binders are head 0 and tail 1 before the four forall
    // binders. Afterwards: finish 0, middle 1, start 2, right 3, head 4,
    // tail 5. Proof hypotheses after the implications are right-path 0,
    // decomposed-left-path 1, and induction hypothesis 2.
    let cons_left_premise = CoreTerm::and(
        CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(edge, vec![vertex.clone()]),
                CoreTerm::Bound(2),
            ),
            CoreTerm::Bound(4),
        ),
        valid_path(CoreTerm::Bound(5), CoreTerm::Bound(4), CoreTerm::Bound(1)),
    );
    let cons_right_premise = valid_path(CoreTerm::Bound(3), CoreTerm::Bound(1), CoreTerm::Bound(0));
    let mut induction_hypothesis = HolDraftProof::Hypothesis(2);
    for argument in [
        CoreTerm::Bound(3),
        CoreTerm::Bound(4),
        CoreTerm::Bound(1),
        CoreTerm::Bound(0),
    ] {
        induction_hypothesis = HolDraftProof::ForallElim {
            proof_forall: Box::new(induction_hypothesis),
            argument,
        };
    }
    let tail_concatenation = HolDraftProof::ImpElim {
        proof_implication: Box::new(HolDraftProof::ImpElim {
            proof_implication: Box::new(induction_hypothesis),
            proof_argument: Box::new(HolDraftProof::AndElimRight(Box::new(
                HolDraftProof::Hypothesis(1),
            ))),
        }),
        proof_argument: Box::new(HolDraftProof::Hypothesis(0)),
    };
    let cons_case = HolDraftProof::ForallIntro {
        domain: list_vertex.clone(),
        body: Box::new(HolDraftProof::ForallIntro {
            domain: vertex.clone(),
            body: Box::new(HolDraftProof::ForallIntro {
                domain: vertex.clone(),
                body: Box::new(HolDraftProof::ForallIntro {
                    domain: vertex.clone(),
                    body: Box::new(HolDraftProof::ImpIntro {
                        premise: cons_left_premise,
                        body: Box::new(HolDraftProof::ImpIntro {
                            premise: cons_right_premise,
                            body: Box::new(HolDraftProof::AndIntro(
                                Box::new(HolDraftProof::AndElimLeft(Box::new(
                                    HolDraftProof::Hypothesis(1),
                                ))),
                                Box::new(tail_concatenation),
                            )),
                        }),
                    }),
                }),
            }),
        }),
    };

    let proof = HolDraftProof::ForallIntro {
        domain: list_vertex.clone(),
        body: Box::new(HolDraftProof::Induction {
            datatype: list,
            type_arguments: vec![vertex.clone()],
            motive,
            scrutinee: CoreTerm::Bound(0),
            cases: vec![nil_case, cons_case],
        }),
    };
    let append_receipt = DeclarationReceipt::checked(
        DeclarationId(100),
        StatementFragment::FirstOrderInductive,
        [ProofFeature::StructuralRecursion],
        [],
    );
    let path_receipt = DeclarationReceipt::checked(
        DeclarationId(101),
        StatementFragment::FirstOrderInductive,
        [ProofFeature::StructuralRecursion],
        [],
    );
    let path_concatenation = elaborator
        .check_theorem(
            DeclarationId(102),
            &path_concatenation_statement,
            proof,
            [&append_receipt, &path_receipt],
        )?
        .receipt;

    let malformed_edge = CoreTerm::apply(
        CoreTerm::instantiate_constant(edge, vec![vertex.clone()]),
        CoreTerm::instantiate_constant(nil, vec![vertex.clone()]),
    );
    let type_error = infer_type(
        elaborator.types(),
        elaborator.constants(),
        &TermContext::new(),
        &malformed_edge,
    )
    .expect_err("an edge endpoint cannot be a list")
    .message;

    let proposed_bad = elaborator.constants().next_constant_id()?;
    let bad_recursive_call = CoreTerm::apply(
        CoreTerm::instantiate_constant(proposed_bad, vec![parameter_type.clone()]),
        chain_layout.field(1).expect("tail"),
    );
    let termination_error = elaborator
        .declare_structural_definition(StructuralDefinitionSpec {
            name: "BadPath".to_string(),
            type_parameters: vec![parameter],
            datatype: list,
            datatype_arguments: vec![parameter_type],
            fixed_parameter_types: Vec::new(),
            result_type: CoreType::arrow(
                CoreType::Parameter(parameter),
                CoreType::arrow(CoreType::Parameter(parameter), CoreType::Prop),
            ),
            arms: vec![
                StructuralArmSpec::new(
                    nil,
                    CoreTerm::lambda(
                        CoreType::Parameter(parameter),
                        CoreTerm::lambda(CoreType::Parameter(parameter), CoreTerm::Truth),
                    ),
                ),
                StructuralArmSpec::new(cons, bad_recursive_call),
            ],
        })
        .expect_err("arbitrary direct recursive call must fail")
        .message;

    let positivity_error = elaborator
        .declare_inductive(InductiveSpec::new(
            "BadGraph",
            Vec::new(),
            vec![InductiveConstructorSpec::new(
                "bad_graph",
                vec![InductiveFieldType::arrow(
                    InductiveFieldType::Recursive,
                    InductiveFieldType::existing(vertex),
                )],
            )],
        ))
        .expect_err("negative graph datatype must fail")
        .message;

    Ok(H3GraphSpikeReport {
        path_concatenation,
        declared_definitions: vec![
            format!("append#{}", append.0),
            format!("ValidPath#{}", chain.0),
            format!("Edge#{}", edge.0),
            format!("vertex_a#{}", vertex_a.0),
        ],
        type_error,
        termination_error,
        positivity_error,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{ReceiptPolicy, TeachingProfile};

    #[test]
    fn list_h3_spike_is_positive_trust_free_and_policy_accurate() {
        let report = run_list_h3_spike().expect("List H3 spike");
        assert_eq!(report.declared_definitions.len(), 5);
        assert_eq!(
            report.nodup_singleton.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert!(report
            .nodup_singleton
            .proof()
            .transitive_features()
            .contains(&ProofFeature::StructuralRecursion));
        assert!(report
            .nodup_singleton
            .proof()
            .axiom_dependencies()
            .is_empty());
        assert!(report
            .nodup_singleton
            .proof()
            .incomplete_dependencies()
            .is_empty());
        assert!(report
            .induction_theorem
            .proof()
            .direct_features()
            .contains(&ProofFeature::Induction));
        assert!(ReceiptPolicy::new(TeachingProfile::FirstOrderInductive)
            .check(&report.nodup_singleton)
            .is_empty());
        assert!(ReceiptPolicy::new(TeachingProfile::FirstOrderInductive)
            .check(&report.induction_theorem)
            .is_empty());
        assert!(report.type_error.contains("application argument has type"));
        assert!(report.termination_error.contains("calls itself directly"));
        assert!(report.positivity_error.contains("occurs negatively"));
    }

    #[test]
    fn graph_h3_spike_proves_path_concatenation_in_fol_with_induction() {
        let report = run_graph_h3_spike().expect("graph H3 spike");
        assert_eq!(
            report.path_concatenation.proof().statement_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            report.path_concatenation.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            report.path_concatenation.proof().transitive_features(),
            &std::collections::BTreeSet::from([
                ProofFeature::Induction,
                ProofFeature::StructuralRecursion,
            ])
        );
        assert!(report
            .path_concatenation
            .proof()
            .axiom_dependencies()
            .is_empty());
        assert!(ReceiptPolicy::new(TeachingProfile::FirstOrderInductive)
            .check(&report.path_concatenation)
            .is_empty());
        assert!(report.type_error.contains("application argument has type"));
        assert!(report.termination_error.contains("calls itself directly"));
        assert!(report.positivity_error.contains("occurs negatively"));
    }
}
