//! Checked relation and explicit-path infrastructure over the generic List package.

use super::fragments::DeclarationReceipt;
use super::library::ListLibrary;
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{ConstantId, CoreTerm};
use super::theorems::TheoremId;
use super::types::CoreType;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphLibraryNames {
    pub valid_path: String,
}

impl GraphLibraryNames {
    pub fn canonical() -> Self {
        Self {
            valid_path: "ValidPath".to_string(),
        }
    }

    pub fn under_namespace(namespace: &str) -> Self {
        Self {
            valid_path: if namespace.is_empty() {
                "ValidPath".to_string()
            } else {
                format!("{namespace}.ValidPath")
            },
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GraphLibrary {
    pub edge: ConstantId,
    pub valid_path: ConstantId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathConcatenationTheorem {
    pub theorem: TheoremId,
    pub receipt: DeclarationReceipt,
}

impl GraphLibrary {
    /// Install an endpoint-aware path predicate specialized to a checked
    /// polymorphic edge-symbol family. Specializing at package installation,
    /// instead of passing a predicate as an object-language value, keeps
    /// concrete first-order instances first-order.
    pub fn install(
        elaborator: &mut SpikeElaborator,
        lists: &ListLibrary,
        edge: ConstantId,
    ) -> Result<Self, SpikeError> {
        Self::install_named(elaborator, lists, edge, &GraphLibraryNames::canonical())
    }

    pub fn install_named(
        elaborator: &mut SpikeElaborator,
        lists: &ListLibrary,
        edge: ConstantId,
        names: &GraphLibraryNames,
    ) -> Result<Self, SpikeError> {
        let mut staged = elaborator.clone();
        let parameter = lists.element_parameter;
        let element_type = CoreType::Parameter(parameter);
        let cons_layout = StructuralArmLayout::new(2, 1, 0);
        let valid_path = staged.declare_structural_definition(StructuralDefinitionSpec {
            name: names.valid_path.clone(),
            type_parameters: vec![parameter],
            datatype: lists.datatype,
            datatype_arguments: vec![element_type.clone()],
            fixed_parameter_types: Vec::new(),
            recursive_argument_index: 0,
            result_type: CoreType::arrow(
                element_type.clone(),
                CoreType::arrow(element_type.clone(), CoreType::Prop),
            ),
            arms: vec![
                StructuralArmSpec::new(
                    lists.nil,
                    CoreTerm::lambda(
                        element_type.clone(),
                        CoreTerm::lambda(
                            element_type.clone(),
                            CoreTerm::equality(
                                element_type.clone(),
                                CoreTerm::Bound(0),
                                CoreTerm::Bound(1),
                            ),
                        ),
                    ),
                ),
                StructuralArmSpec::new(
                    lists.cons,
                    CoreTerm::lambda(
                        element_type.clone(),
                        CoreTerm::lambda(
                            element_type,
                            CoreTerm::and(
                                // Under start and finish: finish 0, start 1,
                                // head 2, tail 3, recursive result 4.
                                CoreTerm::apply(
                                    CoreTerm::apply(
                                        CoreTerm::instantiate_constant(
                                            edge,
                                            vec![CoreType::Parameter(parameter)],
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
        debug_assert_eq!(cons_layout.recursive_result(0), Some(CoreTerm::Bound(2)));
        *elaborator = staged;
        Ok(Self { edge, valid_path })
    }

    pub fn edge_type(element_type: CoreType) -> CoreType {
        CoreType::arrow(
            element_type.clone(),
            CoreType::arrow(element_type, CoreType::Prop),
        )
    }

    pub fn valid_path_term(
        &self,
        element_type: CoreType,
        path: CoreTerm,
        start: CoreTerm,
        finish: CoreTerm,
    ) -> CoreTerm {
        apply_many(
            CoreTerm::instantiate_constant(self.valid_path, vec![element_type]),
            [path, start, finish],
        )
    }

    /// Check and store path concatenation for a concrete element type. The
    /// theorem statement remains first-order whenever that instance is
    /// first-order; the relation is not hidden behind a HOL axiom or an
    /// untracked metatheoretic shortcut.
    pub fn declare_path_concatenation(
        &self,
        elaborator: &mut SpikeElaborator,
        lists: &ListLibrary,
        name: impl Into<String>,
        element_type: CoreType,
    ) -> Result<PathConcatenationTheorem, SpikeError> {
        let list_type = lists.list_type(element_type.clone());
        let append =
            |left: CoreTerm, right: CoreTerm| lists.append_term(element_type.clone(), left, right);
        let valid_path = |path: CoreTerm, start: CoreTerm, finish: CoreTerm| {
            self.valid_path_term(element_type.clone(), path, start, finish)
        };

        // Inside the five quantifiers: finish 0, middle 1, start 2,
        // right path 3, left path 4.
        let theorem_body = CoreTerm::implies(
            valid_path(CoreTerm::Bound(4), CoreTerm::Bound(2), CoreTerm::Bound(1)),
            CoreTerm::implies(
                valid_path(CoreTerm::Bound(3), CoreTerm::Bound(1), CoreTerm::Bound(0)),
                valid_path(
                    append(CoreTerm::Bound(4), CoreTerm::Bound(3)),
                    CoreTerm::Bound(2),
                    CoreTerm::Bound(0),
                ),
            ),
        );
        let statement = CoreTerm::forall(
            list_type.clone(),
            CoreTerm::forall(
                list_type.clone(),
                CoreTerm::forall(
                    element_type.clone(),
                    CoreTerm::forall(
                        element_type.clone(),
                        CoreTerm::forall(element_type.clone(), theorem_body),
                    ),
                ),
            ),
        );

        // Motive for induction on the left path. Under the motive lambda and
        // four quantifiers: finish 0, middle 1, start 2, right 3, left 4.
        let motive_body = CoreTerm::implies(
            valid_path(CoreTerm::Bound(4), CoreTerm::Bound(2), CoreTerm::Bound(1)),
            CoreTerm::implies(
                valid_path(CoreTerm::Bound(3), CoreTerm::Bound(1), CoreTerm::Bound(0)),
                valid_path(
                    append(CoreTerm::Bound(4), CoreTerm::Bound(3)),
                    CoreTerm::Bound(2),
                    CoreTerm::Bound(0),
                ),
            ),
        );
        let motive = CoreTerm::lambda(
            list_type.clone(),
            CoreTerm::forall(
                list_type.clone(),
                CoreTerm::forall(
                    element_type.clone(),
                    CoreTerm::forall(
                        element_type.clone(),
                        CoreTerm::forall(element_type.clone(), motive_body),
                    ),
                ),
            ),
        );

        // Nil case after right/start/middle/finish binders: finish 0,
        // middle 1, start 2, right 3. The first premise is middle = start.
        let nil_equality =
            CoreTerm::equality(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(2));
        let nil_right_path = valid_path(CoreTerm::Bound(3), CoreTerm::Bound(1), CoreTerm::Bound(0));
        let equality_motive = CoreTerm::lambda(
            element_type.clone(),
            // replacement start 0, finish 1, old middle 2, old start 3,
            // right path 4.
            valid_path(CoreTerm::Bound(4), CoreTerm::Bound(0), CoreTerm::Bound(1)),
        );
        let nil_case = HolDraftProof::ForallIntro {
            domain: list_type.clone(),
            body: Box::new(HolDraftProof::ForallIntro {
                domain: element_type.clone(),
                body: Box::new(HolDraftProof::ForallIntro {
                    domain: element_type.clone(),
                    body: Box::new(HolDraftProof::ForallIntro {
                        domain: element_type.clone(),
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

        // Cons case after the four forall binders: finish 0, middle 1,
        // start 2, right 3, head 4, tail 5. Proof hypotheses after the two
        // implications are right-path 0, left-path decomposition 1, IH 2.
        let cons_left_premise = CoreTerm::and(
            CoreTerm::apply(
                CoreTerm::apply(
                    CoreTerm::instantiate_constant(self.edge, vec![element_type.clone()]),
                    CoreTerm::Bound(2),
                ),
                CoreTerm::Bound(4),
            ),
            valid_path(CoreTerm::Bound(5), CoreTerm::Bound(4), CoreTerm::Bound(1)),
        );
        let cons_right_premise =
            valid_path(CoreTerm::Bound(3), CoreTerm::Bound(1), CoreTerm::Bound(0));
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
            domain: list_type.clone(),
            body: Box::new(HolDraftProof::ForallIntro {
                domain: element_type.clone(),
                body: Box::new(HolDraftProof::ForallIntro {
                    domain: element_type.clone(),
                    body: Box::new(HolDraftProof::ForallIntro {
                        domain: element_type.clone(),
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
            domain: list_type.clone(),
            body: Box::new(HolDraftProof::Induction {
                datatype: lists.datatype,
                type_arguments: vec![element_type],
                motive,
                scrutinee: CoreTerm::Bound(0),
                cases: vec![nil_case, cons_case],
            }),
        };
        let (theorem, receipt) = elaborator.declare_theorem(name, Vec::new(), statement, proof)?;
        Ok(PathConcatenationTheorem { theorem, receipt })
    }
}

fn apply_many(function: CoreTerm, arguments: impl IntoIterator<Item = CoreTerm>) -> CoreTerm {
    arguments.into_iter().fold(function, CoreTerm::apply)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{ProofFeature, StatementFragment};
    use crate::hol::library::ListLibrary;
    use crate::hol::terms::{infer_type, TermContext};

    #[test]
    fn valid_path_is_generic_but_concrete_graphs_remain_first_order_inductive() {
        let mut elaborator = SpikeElaborator::new();
        let lists = ListLibrary::install(&mut elaborator).expect("install List");
        let parameter_type = CoreType::Parameter(lists.element_parameter);
        let edge = elaborator
            .declare_polymorphic_constant(
                "Edge",
                vec![lists.element_parameter],
                GraphLibrary::edge_type(parameter_type),
            )
            .expect("declare Edge family");
        let graphs =
            GraphLibrary::install(&mut elaborator, &lists, edge).expect("install graph paths");
        let vertex_id = elaborator
            .declare_base_type("Vertex", true)
            .expect("declare Vertex");
        let vertex = CoreType::constructor(vertex_id, Vec::new());
        let start = elaborator
            .declare_constant("start", vertex.clone())
            .expect("declare start");
        let finish = elaborator
            .declare_constant("finish", vertex.clone())
            .expect("declare finish");
        let open_path = graphs.valid_path_term(
            vertex.clone(),
            CoreTerm::Bound(0),
            CoreTerm::Constant(start),
            CoreTerm::Constant(finish),
        );
        assert_eq!(
            infer_type(
                elaborator.types(),
                elaborator.constants(),
                &TermContext::new().with_bound(lists.list_type(vertex.clone())),
                &open_path,
            )
            .expect("ValidPath type"),
            CoreType::Prop
        );
        assert_eq!(
            elaborator
                .classify_with_parameters(&[lists.list_type(vertex)], &open_path)
                .expect("concrete ValidPath fragment"),
            StatementFragment::FirstOrderInductive
        );

        let generic_path_parameter = lists.element_parameter;
        let generic_path_element = CoreType::Parameter(generic_path_parameter);
        let generic_path = elaborator
            .declare_polymorphic_constant(
                "PredicateValuedPath",
                vec![generic_path_parameter],
                CoreType::arrow(
                    GraphLibrary::edge_type(generic_path_element.clone()),
                    CoreType::arrow(
                        lists.list_type(generic_path_element.clone()),
                        CoreType::arrow(
                            generic_path_element.clone(),
                            CoreType::arrow(generic_path_element, CoreType::Prop),
                        ),
                    ),
                ),
            )
            .expect("declare predicate-valued comparison symbol");
        let predicate_valued_path = apply_many(
            CoreTerm::instantiate_constant(
                generic_path,
                vec![CoreType::constructor(vertex_id, Vec::new())],
            ),
            [
                CoreTerm::instantiate_constant(
                    edge,
                    vec![CoreType::constructor(vertex_id, Vec::new())],
                ),
                CoreTerm::Bound(0),
                CoreTerm::Constant(start),
                CoreTerm::Constant(finish),
            ],
        );
        assert_eq!(
            elaborator
                .classify_with_parameters(
                    &[lists.list_type(CoreType::constructor(vertex_id, Vec::new()))],
                    &predicate_valued_path,
                )
                .expect("predicate-valued path fragment"),
            StatementFragment::HigherOrder,
            "passing the relation as data must not be mislabeled FOL"
        );

        let higher_order_path = graphs.valid_path_term(
            CoreType::Prop,
            CoreTerm::Bound(0),
            CoreTerm::Truth,
            CoreTerm::Falsity,
        );
        assert_eq!(
            elaborator
                .classify_with_parameters(&[lists.list_type(CoreType::Prop)], &higher_order_path,)
                .expect("higher-order ValidPath fragment"),
            StatementFragment::HigherOrder
        );

        let concatenation = graphs
            .declare_path_concatenation(
                &mut elaborator,
                &lists,
                "path_concatenation",
                CoreType::constructor(vertex_id, Vec::new()),
            )
            .expect("checked path concatenation");
        assert_eq!(
            concatenation.receipt.proof().statement_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            concatenation.receipt.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            concatenation.receipt.proof().transitive_features(),
            &std::collections::BTreeSet::from([
                ProofFeature::Induction,
                ProofFeature::StructuralRecursion,
            ])
        );

        let higher_order_concatenation = graphs
            .declare_path_concatenation(
                &mut elaborator,
                &lists,
                "proposition_path_concatenation",
                CoreType::Prop,
            )
            .expect("checked higher-order path instance");
        assert_eq!(
            higher_order_concatenation
                .receipt
                .proof()
                .statement_fragment(),
            StatementFragment::HigherOrder
        );
        assert_eq!(
            higher_order_concatenation
                .receipt
                .proof()
                .required_fragment(),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn graph_package_rejects_an_ill_typed_edge_family_transactionally() {
        let mut elaborator = SpikeElaborator::new();
        let lists = ListLibrary::install(&mut elaborator).expect("install List");
        let parameter = lists.element_parameter;
        let element = CoreType::Parameter(parameter);
        let bad_edge = elaborator
            .declare_polymorphic_constant(
                "BadEdge",
                vec![parameter],
                CoreType::arrow(element.clone(), element),
            )
            .expect("declare ill-shaped edge family");
        let before = elaborator.clone();
        let error = GraphLibrary::install(&mut elaborator, &lists, bad_edge)
            .expect_err("edge family must return a binary proposition");
        assert!(error.message.contains("ill-typed"));
        assert_eq!(elaborator, before);
    }
}
