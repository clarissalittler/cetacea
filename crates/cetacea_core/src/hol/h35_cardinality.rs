//! Reusable H3.5 cardinality transport over a checked list enumeration.
//!
//! This module is deliberately elaborator-side: it builds ordinary core terms
//! and proof evidence, then submits every lemma to the same HOL kernel boundary
//! used by the spike examples.

use super::library::{ListLength, ListLibrary};
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{ConstantId, CoreTerm};
use super::theorems::TheoremId;
use super::types::{CoreType, TypeParameter};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CardinalityTransportLibrary {
    pub map: ConstantId,
    pub theorem: TheoremId,
}

pub(crate) fn declare_cardinality_transport(
    elaborator: &mut SpikeElaborator,
    lists: &ListLibrary,
    length: &ListLength,
) -> Result<CardinalityTransportLibrary, SpikeError> {
    let mut staged = elaborator.clone();
    let library = declare_cardinality_transport_into(&mut staged, lists, length)?;
    *elaborator = staged;
    Ok(library)
}

fn declare_cardinality_transport_into(
    elaborator: &mut SpikeElaborator,
    lists: &ListLibrary,
    list_length: &ListLength,
) -> Result<CardinalityTransportLibrary, SpikeError> {
    let list = lists.datatype;
    let nil = lists.nil;
    let cons = lists.cons;
    let member = lists.member;
    let nodup = lists.nodup;
    let length = list_length.constant;
    let nat = list_length.natural_type.clone();
    let succ = list_length.successor;
    let a_parameter = TypeParameter::any(100);
    let b_parameter = TypeParameter::any(101);
    let a = CoreType::Parameter(a_parameter);
    let b = CoreType::Parameter(b_parameter);
    let list_a = CoreType::constructor(list, vec![a.clone()]);
    let list_b = CoreType::constructor(list, vec![b.clone()]);
    let f_type = CoreType::arrow(a.clone(), b.clone());
    let g_type = CoreType::arrow(b.clone(), a.clone());

    let map_layout = StructuralArmLayout::new(2, 1, 1);
    let map = stage(
        "map definition",
        elaborator.declare_structural_definition(StructuralDefinitionSpec {
            name: "map".to_string(),
            type_parameters: vec![a_parameter, b_parameter],
            datatype: list,
            datatype_arguments: vec![a.clone()],
            fixed_parameter_types: vec![f_type.clone()],
            recursive_argument_index: 1,
            result_type: list_b.clone(),
            arms: vec![
                StructuralArmSpec::new(nil, CoreTerm::instantiate_constant(nil, vec![b.clone()])),
                StructuralArmSpec::new(
                    cons,
                    CoreTerm::apply(
                        CoreTerm::apply(
                            CoreTerm::instantiate_constant(cons, vec![b.clone()]),
                            CoreTerm::apply(
                                map_layout.fixed_parameter(0).expect("map function"),
                                map_layout.field(0).expect("map head"),
                            ),
                        ),
                        map_layout.recursive_result(0).expect("mapped tail"),
                    ),
                ),
            ],
        }),
    )?;

    let map_term = |function: CoreTerm, values: CoreTerm| {
        apply2(
            CoreTerm::instantiate_constant(map, vec![a.clone(), b.clone()]),
            function,
            values,
        )
    };
    let member_a = |value: CoreTerm, values: CoreTerm| {
        apply2(
            CoreTerm::instantiate_constant(member, vec![a.clone()]),
            value,
            values,
        )
    };
    let member_b = |value: CoreTerm, values: CoreTerm| {
        apply2(
            CoreTerm::instantiate_constant(member, vec![b.clone()]),
            value,
            values,
        )
    };
    let nodup_a = |values| {
        CoreTerm::apply(
            CoreTerm::instantiate_constant(nodup, vec![a.clone()]),
            values,
        )
    };
    let nodup_b = |values| {
        CoreTerm::apply(
            CoreTerm::instantiate_constant(nodup, vec![b.clone()]),
            values,
        )
    };
    let length_a = |values| {
        CoreTerm::apply(
            CoreTerm::instantiate_constant(length, vec![a.clone()]),
            values,
        )
    };
    let length_b = |values| {
        CoreTerm::apply(
            CoreTerm::instantiate_constant(length, vec![b.clone()]),
            values,
        )
    };

    // length (map f xs) = length xs
    let length_statement = CoreTerm::forall(
        f_type.clone(),
        CoreTerm::forall(
            list_a.clone(),
            CoreTerm::equality(
                nat.clone(),
                length_b(map_term(CoreTerm::Bound(1), CoreTerm::Bound(0))),
                length_a(CoreTerm::Bound(0)),
            ),
        ),
    );
    let nil_a = CoreTerm::instantiate_constant(nil, vec![a.clone()]);
    let tail_map_length = length_b(map_term(CoreTerm::Bound(3), CoreTerm::Bound(1)));
    let succ_tail_map_length = CoreTerm::apply(CoreTerm::Constant(succ), tail_map_length.clone());
    let length_cons_case = HolDraftProof::EqualityElim {
        proof_equality: Box::new(HolDraftProof::Hypothesis(0)),
        motive: CoreTerm::lambda(
            nat.clone(),
            CoreTerm::equality(
                nat.clone(),
                CoreTerm::apply(
                    CoreTerm::Constant(succ),
                    length_b(map_term(CoreTerm::Bound(4), CoreTerm::Bound(2))),
                ),
                CoreTerm::apply(CoreTerm::Constant(succ), CoreTerm::Bound(0)),
            ),
        ),
        proof_left: Box::new(HolDraftProof::EqualityRefl(succ_tail_map_length)),
    };
    let length_motive = CoreTerm::lambda(
        list_a.clone(),
        CoreTerm::equality(
            nat.clone(),
            length_b(map_term(CoreTerm::Bound(2), CoreTerm::Bound(0))),
            length_a(CoreTerm::Bound(0)),
        ),
    );
    let length_proof = HolDraftProof::ForallIntro {
        domain: f_type.clone(),
        body: Box::new(HolDraftProof::ForallIntro {
            domain: list_a.clone(),
            body: Box::new(HolDraftProof::Induction {
                datatype: list,
                type_arguments: vec![a.clone()],
                motive: length_motive,
                scrutinee: CoreTerm::Bound(0),
                cases: vec![
                    HolDraftProof::EqualityRefl(length_a(nil_a)),
                    length_cons_case,
                ],
            }),
        }),
    };
    let (map_length, _) = stage(
        "map_length theorem",
        elaborator.declare_theorem(
            "map_length",
            vec![a_parameter, b_parameter],
            length_statement,
            length_proof,
        ),
    )?;

    // Member x xs -> Member (f x) (map f xs)
    let forward_body = CoreTerm::implies(
        member_a(CoreTerm::Bound(0), CoreTerm::Bound(1)),
        member_b(
            CoreTerm::apply(CoreTerm::Bound(2), CoreTerm::Bound(0)),
            map_term(CoreTerm::Bound(2), CoreTerm::Bound(1)),
        ),
    );
    let forward_statement = CoreTerm::forall(
        f_type.clone(),
        CoreTerm::forall(list_a.clone(), CoreTerm::forall(a.clone(), forward_body)),
    );
    let forward_motive = CoreTerm::lambda(
        list_a.clone(),
        CoreTerm::forall(
            a.clone(),
            CoreTerm::implies(
                member_a(CoreTerm::Bound(0), CoreTerm::Bound(1)),
                member_b(
                    CoreTerm::apply(CoreTerm::Bound(3), CoreTerm::Bound(0)),
                    map_term(CoreTerm::Bound(3), CoreTerm::Bound(1)),
                ),
            ),
        ),
    );
    let forward_nil_case = HolDraftProof::ForallIntro {
        domain: a.clone(),
        body: Box::new(HolDraftProof::ImpIntro {
            premise: CoreTerm::Falsity,
            body: Box::new(HolDraftProof::Hypothesis(0)),
        }),
    };
    let fx = CoreTerm::apply(CoreTerm::Bound(4), CoreTerm::Bound(0));
    let fhead = CoreTerm::apply(CoreTerm::Bound(4), CoreTerm::Bound(1));
    let mapped_tail = map_term(CoreTerm::Bound(4), CoreTerm::Bound(2));
    let mapped_membership = member_b(fx.clone(), mapped_tail.clone());
    let mapped_equality = CoreTerm::equality(b.clone(), fx.clone(), fhead.clone());
    let forward_left = HolDraftProof::OrIntroLeft {
        proof_left: Box::new(HolDraftProof::EqualityElim {
            proof_equality: Box::new(HolDraftProof::Hypothesis(0)),
            motive: CoreTerm::lambda(
                a.clone(),
                CoreTerm::equality(
                    b.clone(),
                    CoreTerm::apply(CoreTerm::Bound(5), CoreTerm::Bound(1)),
                    CoreTerm::apply(CoreTerm::Bound(5), CoreTerm::Bound(0)),
                ),
            ),
            proof_left: Box::new(HolDraftProof::EqualityRefl(fx.clone())),
        }),
        right: mapped_membership.clone(),
    };
    let forward_tail = imp_elim(
        forall_elim(HolDraftProof::Hypothesis(2), CoreTerm::Bound(0)),
        HolDraftProof::Hypothesis(0),
    );
    let forward_right = HolDraftProof::OrIntroRight {
        left: mapped_equality,
        proof_right: Box::new(forward_tail),
    };
    let forward_cons_case = HolDraftProof::ForallIntro {
        domain: a.clone(),
        body: Box::new(HolDraftProof::ImpIntro {
            premise: CoreTerm::or(
                CoreTerm::equality(a.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1)),
                member_a(CoreTerm::Bound(0), CoreTerm::Bound(2)),
            ),
            body: Box::new(HolDraftProof::OrElim {
                proof_or: Box::new(HolDraftProof::Hypothesis(0)),
                left_case: Box::new(forward_left),
                right_case: Box::new(forward_right),
                target: CoreTerm::or(CoreTerm::equality(b.clone(), fx, fhead), mapped_membership),
            }),
        }),
    };
    let forward_proof = HolDraftProof::ForallIntro {
        domain: f_type.clone(),
        body: Box::new(HolDraftProof::ForallIntro {
            domain: list_a.clone(),
            body: Box::new(HolDraftProof::Induction {
                datatype: list,
                type_arguments: vec![a.clone()],
                motive: forward_motive,
                scrutinee: CoreTerm::Bound(0),
                cases: vec![forward_nil_case, forward_cons_case],
            }),
        }),
    };
    let (member_map_forward, _) = stage(
        "member_map_forward theorem",
        elaborator.declare_theorem(
            "member_map_forward",
            vec![a_parameter, b_parameter],
            forward_statement,
            forward_proof,
        ),
    )?;

    let left_inverse = CoreTerm::forall(
        a.clone(),
        CoreTerm::equality(
            a.clone(),
            CoreTerm::apply(
                CoreTerm::Bound(1),
                CoreTerm::apply(CoreTerm::Bound(2), CoreTerm::Bound(0)),
            ),
            CoreTerm::Bound(0),
        ),
    );
    let right_inverse = CoreTerm::forall(
        b.clone(),
        CoreTerm::equality(
            b.clone(),
            CoreTerm::apply(
                CoreTerm::Bound(2),
                CoreTerm::apply(CoreTerm::Bound(1), CoreTerm::Bound(0)),
            ),
            CoreTerm::Bound(0),
        ),
    );

    // A left inverse lets membership in map f xs reflect back to xs.
    let reverse_statement = CoreTerm::forall(
        f_type.clone(),
        CoreTerm::forall(
            g_type.clone(),
            CoreTerm::implies(
                left_inverse.clone(),
                CoreTerm::forall(
                    list_a.clone(),
                    CoreTerm::forall(
                        a.clone(),
                        CoreTerm::implies(
                            member_b(
                                CoreTerm::apply(CoreTerm::Bound(3), CoreTerm::Bound(0)),
                                map_term(CoreTerm::Bound(3), CoreTerm::Bound(1)),
                            ),
                            member_a(CoreTerm::Bound(0), CoreTerm::Bound(1)),
                        ),
                    ),
                ),
            ),
        ),
    );
    let reverse_motive = CoreTerm::lambda(
        list_a.clone(),
        CoreTerm::forall(
            a.clone(),
            CoreTerm::implies(
                member_b(
                    CoreTerm::apply(CoreTerm::Bound(4), CoreTerm::Bound(0)),
                    map_term(CoreTerm::Bound(4), CoreTerm::Bound(1)),
                ),
                member_a(CoreTerm::Bound(0), CoreTerm::Bound(1)),
            ),
        ),
    );
    let reverse_nil_case = HolDraftProof::ForallIntro {
        domain: a.clone(),
        body: Box::new(HolDraftProof::ImpIntro {
            premise: CoreTerm::Falsity,
            body: Box::new(HolDraftProof::Hypothesis(0)),
        }),
    };
    let gfx = CoreTerm::apply(
        CoreTerm::Bound(4),
        CoreTerm::apply(CoreTerm::Bound(5), CoreTerm::Bound(0)),
    );
    let inverse_x = forall_elim(HolDraftProof::Hypothesis(3), CoreTerm::Bound(0));
    let inverse_head = forall_elim(HolDraftProof::Hypothesis(3), CoreTerm::Bound(1));
    let mapped_equality_under_g = HolDraftProof::EqualityElim {
        proof_equality: Box::new(HolDraftProof::Hypothesis(0)),
        motive: CoreTerm::lambda(
            b.clone(),
            CoreTerm::equality(
                a.clone(),
                CoreTerm::apply(
                    CoreTerm::Bound(5),
                    CoreTerm::apply(CoreTerm::Bound(6), CoreTerm::Bound(1)),
                ),
                CoreTerm::apply(CoreTerm::Bound(5), CoreTerm::Bound(0)),
            ),
        ),
        proof_left: Box::new(HolDraftProof::EqualityRefl(gfx.clone())),
    };
    let gfhead_equals_x = HolDraftProof::EqualityElim {
        proof_equality: Box::new(mapped_equality_under_g),
        motive: CoreTerm::lambda(
            a.clone(),
            CoreTerm::equality(a.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1)),
        ),
        proof_left: Box::new(inverse_x),
    };
    let x_equals_head = HolDraftProof::EqualityElim {
        proof_equality: Box::new(gfhead_equals_x),
        motive: CoreTerm::lambda(
            a.clone(),
            CoreTerm::equality(a.clone(), CoreTerm::Bound(0), CoreTerm::Bound(2)),
        ),
        proof_left: Box::new(inverse_head),
    };
    let reverse_left = HolDraftProof::OrIntroLeft {
        proof_left: Box::new(x_equals_head),
        right: member_a(CoreTerm::Bound(0), CoreTerm::Bound(2)),
    };
    let reverse_tail = imp_elim(
        forall_elim(HolDraftProof::Hypothesis(2), CoreTerm::Bound(0)),
        HolDraftProof::Hypothesis(0),
    );
    let reverse_right = HolDraftProof::OrIntroRight {
        left: CoreTerm::equality(a.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1)),
        proof_right: Box::new(reverse_tail),
    };
    let reverse_cons_case = HolDraftProof::ForallIntro {
        domain: a.clone(),
        body: Box::new(HolDraftProof::ImpIntro {
            premise: CoreTerm::or(
                CoreTerm::equality(
                    b.clone(),
                    CoreTerm::apply(CoreTerm::Bound(5), CoreTerm::Bound(0)),
                    CoreTerm::apply(CoreTerm::Bound(5), CoreTerm::Bound(1)),
                ),
                member_b(
                    CoreTerm::apply(CoreTerm::Bound(5), CoreTerm::Bound(0)),
                    map_term(CoreTerm::Bound(5), CoreTerm::Bound(2)),
                ),
            ),
            body: Box::new(HolDraftProof::OrElim {
                proof_or: Box::new(HolDraftProof::Hypothesis(0)),
                left_case: Box::new(reverse_left),
                right_case: Box::new(reverse_right),
                target: CoreTerm::or(
                    CoreTerm::equality(a.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1)),
                    member_a(CoreTerm::Bound(0), CoreTerm::Bound(2)),
                ),
            }),
        }),
    };
    let reverse_proof = HolDraftProof::ForallIntro {
        domain: f_type.clone(),
        body: Box::new(HolDraftProof::ForallIntro {
            domain: g_type.clone(),
            body: Box::new(HolDraftProof::ImpIntro {
                premise: left_inverse.clone(),
                body: Box::new(HolDraftProof::ForallIntro {
                    domain: list_a.clone(),
                    body: Box::new(HolDraftProof::Induction {
                        datatype: list,
                        type_arguments: vec![a.clone()],
                        motive: reverse_motive,
                        scrutinee: CoreTerm::Bound(0),
                        cases: vec![reverse_nil_case, reverse_cons_case],
                    }),
                }),
            }),
        }),
    };
    let (member_map_reverse, _) = stage(
        "member_map_reverse theorem",
        elaborator.declare_theorem(
            "member_map_reverse",
            vec![a_parameter, b_parameter],
            reverse_statement,
            reverse_proof,
        ),
    )?;

    // A map by an injective function preserves duplicate-freedom.
    let nodup_statement = CoreTerm::forall(
        f_type.clone(),
        CoreTerm::forall(
            g_type.clone(),
            CoreTerm::implies(
                left_inverse.clone(),
                CoreTerm::forall(
                    list_a.clone(),
                    CoreTerm::implies(
                        nodup_a(CoreTerm::Bound(0)),
                        nodup_b(map_term(CoreTerm::Bound(2), CoreTerm::Bound(0))),
                    ),
                ),
            ),
        ),
    );
    let nodup_motive = CoreTerm::lambda(
        list_a.clone(),
        CoreTerm::implies(
            nodup_a(CoreTerm::Bound(0)),
            nodup_b(map_term(CoreTerm::Bound(3), CoreTerm::Bound(0))),
        ),
    );
    let nodup_nil_case = HolDraftProof::ImpIntro {
        premise: CoreTerm::Truth,
        body: Box::new(HolDraftProof::TruthIntro),
    };
    let reverse_member = imp_elim(
        forall_elim(
            forall_elim(
                imp_elim(
                    forall_elim(
                        forall_elim(
                            theorem_ref(member_map_reverse, &[a.clone(), b.clone()]),
                            CoreTerm::Bound(4),
                        ),
                        CoreTerm::Bound(3),
                    ),
                    HolDraftProof::Hypothesis(3),
                ),
                CoreTerm::Bound(1),
            ),
            CoreTerm::Bound(0),
        ),
        HolDraftProof::Hypothesis(0),
    );
    let mapped_not_member = imp_elim(
        HolDraftProof::AndElimLeft(Box::new(HolDraftProof::Hypothesis(1))),
        reverse_member,
    );
    let mapped_tail_nodup = imp_elim(
        HolDraftProof::Hypothesis(1),
        HolDraftProof::AndElimRight(Box::new(HolDraftProof::Hypothesis(0))),
    );
    let nodup_cons_case = HolDraftProof::ImpIntro {
        premise: CoreTerm::and(
            CoreTerm::implies(
                member_a(CoreTerm::Bound(0), CoreTerm::Bound(1)),
                CoreTerm::Falsity,
            ),
            nodup_a(CoreTerm::Bound(1)),
        ),
        body: Box::new(HolDraftProof::AndIntro(
            Box::new(HolDraftProof::ImpIntro {
                premise: member_b(
                    CoreTerm::apply(CoreTerm::Bound(4), CoreTerm::Bound(0)),
                    map_term(CoreTerm::Bound(4), CoreTerm::Bound(1)),
                ),
                body: Box::new(mapped_not_member),
            }),
            Box::new(mapped_tail_nodup),
        )),
    };
    let nodup_proof = HolDraftProof::ForallIntro {
        domain: f_type.clone(),
        body: Box::new(HolDraftProof::ForallIntro {
            domain: g_type.clone(),
            body: Box::new(HolDraftProof::ImpIntro {
                premise: left_inverse.clone(),
                body: Box::new(HolDraftProof::ForallIntro {
                    domain: list_a.clone(),
                    body: Box::new(HolDraftProof::Induction {
                        datatype: list,
                        type_arguments: vec![a.clone()],
                        motive: nodup_motive,
                        scrutinee: CoreTerm::Bound(0),
                        cases: vec![nodup_nil_case, nodup_cons_case],
                    }),
                }),
            }),
        }),
    };
    let (nodup_map, _) = stage(
        "nodup_map_injective theorem",
        elaborator.declare_theorem(
            "nodup_map_injective",
            vec![a_parameter, b_parameter],
            nodup_statement,
            nodup_proof,
        ),
    )?;

    // Surjectivity plus forward membership makes the mapped list exhaustive.
    let coverage_a = CoreTerm::forall(a.clone(), member_a(CoreTerm::Bound(0), CoreTerm::Bound(1)));
    let coverage_b = CoreTerm::forall(
        b.clone(),
        member_b(
            CoreTerm::Bound(0),
            map_term(CoreTerm::Bound(3), CoreTerm::Bound(1)),
        ),
    );
    let coverage_statement = CoreTerm::forall(
        f_type.clone(),
        CoreTerm::forall(
            g_type.clone(),
            CoreTerm::implies(
                right_inverse.clone(),
                CoreTerm::forall(list_a.clone(), CoreTerm::implies(coverage_a, coverage_b)),
            ),
        ),
    );
    let gb = CoreTerm::apply(CoreTerm::Bound(2), CoreTerm::Bound(0));
    let source_member = forall_elim(HolDraftProof::Hypothesis(0), gb.clone());
    let forward_member = imp_elim(
        forall_elim(
            forall_elim(
                forall_elim(
                    theorem_ref(member_map_forward, &[a.clone(), b.clone()]),
                    CoreTerm::Bound(3),
                ),
                CoreTerm::Bound(1),
            ),
            gb.clone(),
        ),
        source_member,
    );
    let inverse_b = forall_elim(HolDraftProof::Hypothesis(1), CoreTerm::Bound(0));
    let coverage_proof = HolDraftProof::ForallIntro {
        domain: f_type.clone(),
        body: Box::new(HolDraftProof::ForallIntro {
            domain: g_type.clone(),
            body: Box::new(HolDraftProof::ImpIntro {
                premise: right_inverse.clone(),
                body: Box::new(HolDraftProof::ForallIntro {
                    domain: list_a.clone(),
                    body: Box::new(HolDraftProof::ImpIntro {
                        premise: CoreTerm::forall(
                            a.clone(),
                            member_a(CoreTerm::Bound(0), CoreTerm::Bound(1)),
                        ),
                        body: Box::new(HolDraftProof::ForallIntro {
                            domain: b.clone(),
                            body: Box::new(HolDraftProof::EqualityElim {
                                proof_equality: Box::new(inverse_b),
                                motive: CoreTerm::lambda(
                                    b.clone(),
                                    member_b(
                                        CoreTerm::Bound(0),
                                        map_term(CoreTerm::Bound(4), CoreTerm::Bound(2)),
                                    ),
                                ),
                                proof_left: Box::new(forward_member),
                            }),
                        }),
                    }),
                }),
            }),
        }),
    };
    let (map_coverage, _) = stage(
        "map_coverage_surjective theorem",
        elaborator.declare_theorem(
            "map_coverage_surjective",
            vec![a_parameter, b_parameter],
            coverage_statement,
            coverage_proof,
        ),
    )?;

    // Package the three reusable list facts as cardinality preservation.
    let transport_conclusion = CoreTerm::and(
        nodup_b(map_term(CoreTerm::Bound(2), CoreTerm::Bound(0))),
        CoreTerm::and(
            CoreTerm::equality(
                nat.clone(),
                length_b(map_term(CoreTerm::Bound(2), CoreTerm::Bound(0))),
                length_a(CoreTerm::Bound(0)),
            ),
            CoreTerm::forall(
                b.clone(),
                member_b(
                    CoreTerm::Bound(0),
                    map_term(CoreTerm::Bound(3), CoreTerm::Bound(1)),
                ),
            ),
        ),
    );
    let transport_statement = CoreTerm::forall(
        f_type.clone(),
        CoreTerm::forall(
            g_type.clone(),
            CoreTerm::implies(
                left_inverse.clone(),
                CoreTerm::implies(
                    right_inverse.clone(),
                    CoreTerm::forall(
                        list_a.clone(),
                        CoreTerm::implies(
                            nodup_a(CoreTerm::Bound(0)),
                            CoreTerm::implies(
                                CoreTerm::forall(
                                    a.clone(),
                                    member_a(CoreTerm::Bound(0), CoreTerm::Bound(1)),
                                ),
                                transport_conclusion,
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    let mapped_nodup = imp_elim(
        forall_elim(
            imp_elim(
                forall_elim(
                    forall_elim(
                        theorem_ref(nodup_map, &[a.clone(), b.clone()]),
                        CoreTerm::Bound(2),
                    ),
                    CoreTerm::Bound(1),
                ),
                HolDraftProof::Hypothesis(3),
            ),
            CoreTerm::Bound(0),
        ),
        HolDraftProof::Hypothesis(1),
    );
    let mapped_length = forall_elim(
        forall_elim(
            theorem_ref(map_length, &[a.clone(), b.clone()]),
            CoreTerm::Bound(2),
        ),
        CoreTerm::Bound(0),
    );
    let mapped_coverage = imp_elim(
        forall_elim(
            imp_elim(
                forall_elim(
                    forall_elim(
                        theorem_ref(map_coverage, &[a.clone(), b.clone()]),
                        CoreTerm::Bound(2),
                    ),
                    CoreTerm::Bound(1),
                ),
                HolDraftProof::Hypothesis(2),
            ),
            CoreTerm::Bound(0),
        ),
        HolDraftProof::Hypothesis(0),
    );
    let transport_proof = HolDraftProof::ForallIntro {
        domain: f_type,
        body: Box::new(HolDraftProof::ForallIntro {
            domain: g_type,
            body: Box::new(HolDraftProof::ImpIntro {
                premise: left_inverse,
                body: Box::new(HolDraftProof::ImpIntro {
                    premise: right_inverse,
                    body: Box::new(HolDraftProof::ForallIntro {
                        domain: list_a,
                        body: Box::new(HolDraftProof::ImpIntro {
                            premise: nodup_a(CoreTerm::Bound(0)),
                            body: Box::new(HolDraftProof::ImpIntro {
                                premise: CoreTerm::forall(
                                    a.clone(),
                                    member_a(CoreTerm::Bound(0), CoreTerm::Bound(1)),
                                ),
                                body: Box::new(HolDraftProof::AndIntro(
                                    Box::new(mapped_nodup),
                                    Box::new(HolDraftProof::AndIntro(
                                        Box::new(mapped_length),
                                        Box::new(mapped_coverage),
                                    )),
                                )),
                            }),
                        }),
                    }),
                }),
            }),
        }),
    };
    let (theorem, _) = stage(
        "cardinality_transport theorem",
        elaborator.declare_theorem(
            "cardinality_transport",
            vec![a_parameter, b_parameter],
            transport_statement,
            transport_proof,
        ),
    )?;

    Ok(CardinalityTransportLibrary { map, theorem })
}

fn apply2(function: CoreTerm, first: CoreTerm, second: CoreTerm) -> CoreTerm {
    CoreTerm::apply(CoreTerm::apply(function, first), second)
}

fn theorem_ref(theorem: TheoremId, arguments: &[CoreType]) -> HolDraftProof {
    HolDraftProof::TheoremRef {
        theorem,
        type_arguments: arguments.to_vec(),
        term_arguments: Vec::new(),
    }
}

fn forall_elim(proof: HolDraftProof, argument: CoreTerm) -> HolDraftProof {
    HolDraftProof::ForallElim {
        proof_forall: Box::new(proof),
        argument,
    }
}

fn imp_elim(implication: HolDraftProof, argument: HolDraftProof) -> HolDraftProof {
    HolDraftProof::ImpElim {
        proof_implication: Box::new(implication),
        proof_argument: Box::new(argument),
    }
}

fn stage<T>(label: &str, result: Result<T, SpikeError>) -> Result<T, SpikeError> {
    result.map_err(|error| SpikeError {
        message: format!("{label}: {}", error.message),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cardinality_transport_package_is_transactional_on_a_late_collision() {
        let mut elaborator = SpikeElaborator::new();
        let nat_id = elaborator
            .declare_base_type("Nat", true)
            .expect("declare Nat");
        let nat = CoreType::constructor(nat_id, Vec::new());
        let zero = elaborator
            .declare_constant("zero", nat.clone())
            .expect("declare zero");
        let successor = elaborator
            .declare_constant("succ", CoreType::arrow(nat.clone(), nat.clone()))
            .expect("declare successor");
        let lists = ListLibrary::install(&mut elaborator).expect("install List package");
        let length = lists
            .install_length(&mut elaborator, nat, zero, successor)
            .expect("install length");

        elaborator
            .declare_theorem(
                "member_map_reverse",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TruthIntro,
            )
            .expect("reserve a theorem name reached after earlier package declarations");
        let before = elaborator.clone();
        let error = declare_cardinality_transport(&mut elaborator, &lists, &length)
            .expect_err("late collision must reject the package");
        assert!(error.message.contains("member_map_reverse"));
        assert_eq!(elaborator, before);
    }
}
