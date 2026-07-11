//! Executable H3 stop/go examples.
//!
//! These examples intentionally use the tiny name-resolving spike elaborator,
//! not hand-installed kernel metadata. Each report contains checked receipts
//! and the diagnostics from deliberate rejection cases.

use super::finite_library::FiniteEnumerationLibrary;
use super::fragments::DeclarationReceipt;
use super::graph_library::GraphLibrary;
use super::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
use super::install_cardinality_transport;
use super::library::ListLibrary;
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{infer_type, CoreTerm, TermContext};
use super::types::CoreType;

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct H3FiniteSpikeReport {
    pub bijection_cardinality: DeclarationReceipt,
    pub generic_transport_instance: DeclarationReceipt,
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

    let lists = ListLibrary::install(&mut elaborator)?;
    let parameter = lists.element_parameter;
    let parameter_type = CoreType::Parameter(parameter);
    let list = lists.datatype;
    let nil = lists.nil;
    let cons = lists.cons;
    let all = lists.all;
    let member = lists.member;
    let nodup = lists.nodup;
    let append = lists.append;

    let list_length = lists.install_length(&mut elaborator, nat.clone(), zero, succ)?;
    let length = list_length.constant;

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
    let (_, nodup_singleton) = elaborator.declare_theorem(
        "nodup_singleton",
        Vec::new(),
        nodup_singleton_statement,
        HolDraftProof::AndIntro(
            Box::new(HolDraftProof::ImpIntro {
                premise: CoreTerm::Falsity,
                body: Box::new(HolDraftProof::Hypothesis(0)),
            }),
            Box::new(HolDraftProof::TruthIntro),
        ),
    )?;

    let list_nat = CoreType::constructor(list, vec![nat.clone()]);
    let induction_statement = CoreTerm::forall(list_nat.clone(), CoreTerm::Truth);
    let (_, induction_theorem) = elaborator.declare_theorem(
        "list_truth_induction",
        Vec::new(),
        induction_statement,
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
    )?;

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
            recursive_argument_index: 0,
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

    let lists = ListLibrary::install(&mut elaborator)?;
    let parameter = lists.element_parameter;
    let parameter_type = CoreType::Parameter(parameter);
    let list = lists.datatype;
    let nil = lists.nil;
    let cons = lists.cons;
    let append = lists.append;

    let edge = elaborator.declare_polymorphic_constant(
        "Edge",
        vec![parameter],
        CoreType::arrow(
            parameter_type.clone(),
            CoreType::arrow(parameter_type.clone(), CoreType::Prop),
        ),
    )?;
    let graphs = GraphLibrary::install(&mut elaborator, &lists, edge)?;
    let chain = graphs.valid_path;

    let path_concatenation = graphs
        .declare_path_concatenation(
            &mut elaborator,
            &lists,
            "path_concatenation",
            vertex.clone(),
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

    let chain_layout = StructuralArmLayout::new(2, 1, 0);
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
            recursive_argument_index: 0,
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

/// Construct two finite two-element types, explicit enumeration evidence, and
/// a checked bijection whose inverse laws and common cardinality witness are
/// proved without axioms.
pub fn run_finite_h3_spike() -> Result<H3FiniteSpikeReport, SpikeError> {
    let mut elaborator = SpikeElaborator::new();
    let nat_id = elaborator.declare_base_type("Nat", true)?;
    let nat = CoreType::constructor(nat_id, Vec::new());
    let zero = elaborator.declare_constant("zero", nat.clone())?;
    let succ = elaborator.declare_constant("succ", CoreType::arrow(nat.clone(), nat.clone()))?;
    let one = CoreTerm::apply(CoreTerm::Constant(succ), CoreTerm::Constant(zero));
    let two = CoreTerm::apply(CoreTerm::Constant(succ), one);

    let lists = ListLibrary::install(&mut elaborator)?;
    let member = lists.member;
    let nodup = lists.nodup;
    let list_length = lists.install_length(&mut elaborator, nat.clone(), zero, succ)?;
    let length = list_length.constant;
    let finite = FiniteEnumerationLibrary::install(&mut elaborator, &lists, &list_length)?;

    let color = elaborator.declare_inductive(InductiveSpec::new(
        "Color",
        Vec::new(),
        vec![
            InductiveConstructorSpec::new("red", Vec::new()),
            InductiveConstructorSpec::new("blue", Vec::new()),
        ],
    ))?;
    let red = elaborator.resolve_constant("red")?;
    let blue = elaborator.resolve_constant("blue")?;
    let color_type = CoreType::constructor(color, Vec::new());

    let bit = elaborator.declare_inductive(InductiveSpec::new(
        "Bit",
        Vec::new(),
        vec![
            InductiveConstructorSpec::new("off", Vec::new()),
            InductiveConstructorSpec::new("on", Vec::new()),
        ],
    ))?;
    let off = elaborator.resolve_constant("off")?;
    let on = elaborator.resolve_constant("on")?;
    let bit_type = CoreType::constructor(bit, Vec::new());

    let color_evidence =
        finite.declare_nullary_inductive(&mut elaborator, "color_has_card", color)?;
    let bit_evidence = finite.declare_nullary_inductive(&mut elaborator, "bit_has_card", bit)?;
    let color_enumeration = color_evidence.enumeration.clone();
    let bit_enumeration = bit_evidence.enumeration.clone();

    let transport = install_cardinality_transport(&mut elaborator, &lists, &list_length)?;

    let encode = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "encode".to_string(),
        type_parameters: Vec::new(),
        datatype: color,
        datatype_arguments: Vec::new(),
        fixed_parameter_types: Vec::new(),
        recursive_argument_index: 0,
        result_type: bit_type.clone(),
        arms: vec![
            StructuralArmSpec::new(red, CoreTerm::Constant(off)),
            StructuralArmSpec::new(blue, CoreTerm::Constant(on)),
        ],
    })?;
    let decode = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "decode".to_string(),
        type_parameters: Vec::new(),
        datatype: bit,
        datatype_arguments: Vec::new(),
        fixed_parameter_types: Vec::new(),
        recursive_argument_index: 0,
        result_type: color_type.clone(),
        arms: vec![
            StructuralArmSpec::new(off, CoreTerm::Constant(red)),
            StructuralArmSpec::new(on, CoreTerm::Constant(blue)),
        ],
    })?;

    let encode_term = |value| CoreTerm::apply(CoreTerm::Constant(encode), value);
    let decode_term = |value| CoreTerm::apply(CoreTerm::Constant(decode), value);
    let color_inverse = CoreTerm::forall(
        color_type.clone(),
        CoreTerm::equality(
            color_type.clone(),
            decode_term(encode_term(CoreTerm::Bound(0))),
            CoreTerm::Bound(0),
        ),
    );
    let bit_inverse = CoreTerm::forall(
        bit_type.clone(),
        CoreTerm::equality(
            bit_type.clone(),
            encode_term(decode_term(CoreTerm::Bound(0))),
            CoreTerm::Bound(0),
        ),
    );
    let bijection = CoreTerm::and(color_inverse, bit_inverse);
    let body = CoreTerm::and(
        bijection,
        CoreTerm::and(
            finite.has_card_term(
                color_type.clone(),
                color_enumeration.clone(),
                CoreTerm::Bound(0),
            ),
            finite.has_card_term(
                bit_type.clone(),
                bit_enumeration.clone(),
                CoreTerm::Bound(0),
            ),
        ),
    );
    let statement = CoreTerm::exists(nat.clone(), body.clone());

    let color_inverse_proof = HolDraftProof::ForallIntro {
        domain: color_type.clone(),
        body: Box::new(HolDraftProof::Induction {
            datatype: color,
            type_arguments: Vec::new(),
            motive: CoreTerm::lambda(
                color_type.clone(),
                CoreTerm::equality(
                    color_type.clone(),
                    decode_term(encode_term(CoreTerm::Bound(0))),
                    CoreTerm::Bound(0),
                ),
            ),
            scrutinee: CoreTerm::Bound(0),
            cases: vec![
                HolDraftProof::EqualityRefl(CoreTerm::Constant(red)),
                HolDraftProof::EqualityRefl(CoreTerm::Constant(blue)),
            ],
        }),
    };
    let bit_inverse_proof = HolDraftProof::ForallIntro {
        domain: bit_type.clone(),
        body: Box::new(HolDraftProof::Induction {
            datatype: bit,
            type_arguments: Vec::new(),
            motive: CoreTerm::lambda(
                bit_type.clone(),
                CoreTerm::equality(
                    bit_type.clone(),
                    encode_term(decode_term(CoreTerm::Bound(0))),
                    CoreTerm::Bound(0),
                ),
            ),
            scrutinee: CoreTerm::Bound(0),
            cases: vec![
                HolDraftProof::EqualityRefl(CoreTerm::Constant(off)),
                HolDraftProof::EqualityRefl(CoreTerm::Constant(on)),
            ],
        }),
    };

    let color_has_card_proof = HolDraftProof::TheoremRef {
        theorem: color_evidence.theorem,
        type_arguments: Vec::new(),
        term_arguments: Vec::new(),
    };
    let direct_bit_has_card_proof = HolDraftProof::TheoremRef {
        theorem: bit_evidence.theorem,
        type_arguments: Vec::new(),
        term_arguments: Vec::new(),
    };
    let mut transported_bit_has_card_proof = HolDraftProof::TheoremRef {
        theorem: transport.theorem,
        type_arguments: vec![color_type.clone(), bit_type.clone()],
        term_arguments: Vec::new(),
    };
    for argument in [CoreTerm::Constant(encode), CoreTerm::Constant(decode)] {
        transported_bit_has_card_proof = HolDraftProof::ForallElim {
            proof_forall: Box::new(transported_bit_has_card_proof),
            argument,
        };
    }
    for argument in [color_inverse_proof.clone(), bit_inverse_proof.clone()] {
        transported_bit_has_card_proof = HolDraftProof::ImpElim {
            proof_implication: Box::new(transported_bit_has_card_proof),
            proof_argument: Box::new(argument),
        };
    }
    transported_bit_has_card_proof = HolDraftProof::ForallElim {
        proof_forall: Box::new(transported_bit_has_card_proof),
        argument: color_enumeration,
    };
    for argument in [
        HolDraftProof::AndElimLeft(Box::new(color_has_card_proof.clone())),
        HolDraftProof::AndElimRight(Box::new(HolDraftProof::AndElimRight(Box::new(
            color_has_card_proof.clone(),
        )))),
    ] {
        transported_bit_has_card_proof = HolDraftProof::ImpElim {
            proof_implication: Box::new(transported_bit_has_card_proof),
            proof_argument: Box::new(argument),
        };
    }
    let package_cardinality = |bit_has_card_proof| HolDraftProof::ExistsIntro {
        domain: nat.clone(),
        body: body.clone(),
        witness: two.clone(),
        proof_body: Box::new(HolDraftProof::AndIntro(
            Box::new(HolDraftProof::AndIntro(
                Box::new(color_inverse_proof.clone()),
                Box::new(bit_inverse_proof.clone()),
            )),
            Box::new(HolDraftProof::AndIntro(
                Box::new(color_has_card_proof.clone()),
                Box::new(bit_has_card_proof),
            )),
        )),
    };

    let (_, bijection_cardinality) = elaborator.declare_theorem(
        "bijection_cardinality",
        Vec::new(),
        statement.clone(),
        package_cardinality(direct_bit_has_card_proof),
    )?;
    let (_, generic_transport_instance) = elaborator.declare_theorem(
        "bijection_cardinality_via_transport",
        Vec::new(),
        statement,
        package_cardinality(transported_bit_has_card_proof),
    )?;

    let malformed_encode = CoreTerm::apply(CoreTerm::Constant(encode), CoreTerm::Constant(off));
    let type_error = infer_type(
        elaborator.types(),
        elaborator.constants(),
        &TermContext::new(),
        &malformed_encode,
    )
    .expect_err("encode expects Color, not Bit")
    .message;

    let proposed_bad = elaborator.constants().next_constant_id()?;
    let bad_call = CoreTerm::apply(CoreTerm::Constant(proposed_bad), CoreTerm::Constant(red));
    let termination_error = elaborator
        .declare_structural_definition(StructuralDefinitionSpec {
            name: "bad_encode".to_string(),
            type_parameters: Vec::new(),
            datatype: color,
            datatype_arguments: Vec::new(),
            fixed_parameter_types: Vec::new(),
            recursive_argument_index: 0,
            result_type: bit_type,
            arms: vec![
                StructuralArmSpec::new(red, bad_call),
                StructuralArmSpec::new(blue, CoreTerm::Constant(on)),
            ],
        })
        .expect_err("direct self-call in finite map must fail")
        .message;

    let positivity_error = elaborator
        .declare_inductive(InductiveSpec::new(
            "BadFinite",
            Vec::new(),
            vec![InductiveConstructorSpec::new(
                "bad_finite",
                vec![InductiveFieldType::arrow(
                    InductiveFieldType::Recursive,
                    InductiveFieldType::existing(color_type),
                )],
            )],
        ))
        .expect_err("negative finite datatype must fail")
        .message;

    Ok(H3FiniteSpikeReport {
        bijection_cardinality,
        generic_transport_instance,
        declared_definitions: vec![
            format!("Member#{}", member.0),
            format!("Nodup#{}", nodup.0),
            format!("length#{}", length.0),
            format!("HasCard#{}", finite.has_card.0),
            format!("map#{}", transport.map.0),
            format!("encode#{}", encode.0),
            format!("decode#{}", decode.0),
        ],
        type_error,
        termination_error,
        positivity_error,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{ProofFeature, ReceiptPolicy, StatementFragment, TeachingProfile};

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

    #[test]
    fn finite_h3_spike_checks_bijection_and_shared_cardinality_evidence() {
        let report = run_finite_h3_spike().expect("finite H3 spike");
        assert_eq!(report.declared_definitions.len(), 7);
        assert_eq!(
            report.bijection_cardinality.proof().statement_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            report.bijection_cardinality.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            report.bijection_cardinality.proof().transitive_features(),
            &std::collections::BTreeSet::from([
                ProofFeature::Induction,
                ProofFeature::StructuralRecursion,
            ])
        );
        assert!(report
            .bijection_cardinality
            .proof()
            .axiom_dependencies()
            .is_empty());
        assert!(report
            .bijection_cardinality
            .proof()
            .incomplete_dependencies()
            .is_empty());
        assert!(ReceiptPolicy::new(TeachingProfile::FirstOrderInductive)
            .check(&report.bijection_cardinality)
            .is_empty());
        assert_eq!(
            report
                .generic_transport_instance
                .proof()
                .statement_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            report
                .generic_transport_instance
                .proof()
                .required_fragment(),
            StatementFragment::HigherOrder
        );
        assert!(report
            .generic_transport_instance
            .proof()
            .axiom_dependencies()
            .is_empty());
        assert!(report
            .generic_transport_instance
            .proof()
            .incomplete_dependencies()
            .is_empty());
        assert!(!ReceiptPolicy::new(TeachingProfile::FirstOrderInductive)
            .check(&report.generic_transport_instance)
            .is_empty());
        assert!(ReceiptPolicy::new(TeachingProfile::HigherOrder)
            .check(&report.generic_transport_instance)
            .is_empty());
        assert!(report.type_error.contains("application argument has type"));
        assert!(report.termination_error.contains("calls itself directly"));
        assert!(report.positivity_error.contains("occurs negatively"));
    }
}
