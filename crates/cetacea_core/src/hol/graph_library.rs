//! Checked relation and explicit-path infrastructure over the generic List package.

use super::fragments::DeclarationReceipt;
use super::library::ListLibrary;
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{shift_under_new_binder, ConstantId, CoreTerm};
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

/// Explicit paths for a relation supplied by the caller. Unlike `GraphLibrary`,
/// this definition accepts a predicate value and therefore requires HOL.
/// A path lists the vertices visited after the start, including the finish.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelationPathLibrary {
    pub valid_path: ConstantId,
}

impl RelationPathLibrary {
    pub fn install_named(
        elaborator: &mut SpikeElaborator,
        lists: &ListLibrary,
        names: &GraphLibraryNames,
    ) -> Result<Self, SpikeError> {
        let mut staged = elaborator.clone();
        let parameter = lists.element_parameter;
        let element = CoreType::Parameter(parameter);
        let layout = StructuralArmLayout::new(2, 1, 1);
        // The branch expression introduces start and finish inside the fold's
        // field/result/fixed-parameter context. Shift all layout references.
        let under_endpoints =
            |term: CoreTerm| shift_under_new_binder(&shift_under_new_binder(&term)?);
        let head = under_endpoints(layout.field(0).expect("cons head"))?;
        let recursive = under_endpoints(layout.recursive_result(0).expect("tail result"))?;
        let edge = under_endpoints(layout.fixed_parameter(0).expect("edge relation"))?;
        let valid_path = staged.declare_structural_definition(StructuralDefinitionSpec {
            name: names.valid_path.clone(),
            type_parameters: vec![parameter],
            datatype: lists.datatype,
            datatype_arguments: vec![element.clone()],
            fixed_parameter_types: vec![GraphLibrary::edge_type(element.clone())],
            recursive_argument_index: 1,
            result_type: CoreType::arrow(
                element.clone(),
                CoreType::arrow(element.clone(), CoreType::Prop),
            ),
            arms: vec![
                StructuralArmSpec::new(
                    lists.nil,
                    CoreTerm::lambda(
                        element.clone(),
                        CoreTerm::lambda(
                            element.clone(),
                            CoreTerm::equality(
                                element.clone(),
                                CoreTerm::Bound(0),
                                CoreTerm::Bound(1),
                            ),
                        ),
                    ),
                ),
                StructuralArmSpec::new(
                    lists.cons,
                    CoreTerm::lambda(
                        element.clone(),
                        CoreTerm::lambda(
                            element,
                            CoreTerm::and(
                                apply_many(edge, [CoreTerm::Bound(1), head.clone()]),
                                apply_many(recursive, [head, CoreTerm::Bound(0)]),
                            ),
                        ),
                    ),
                ),
            ],
        })?;
        *elaborator = staged;
        Ok(Self { valid_path })
    }

    pub fn valid_path_term(
        &self,
        element_type: CoreType,
        edge: CoreTerm,
        path: CoreTerm,
        start: CoreTerm,
        finish: CoreTerm,
    ) -> CoreTerm {
        apply_many(
            CoreTerm::instantiate_constant(self.valid_path, vec![element_type]),
            [edge, path, start, finish],
        )
    }
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

    fn iff_proof(left: CoreTerm, right: CoreTerm) -> HolDraftProof {
        HolDraftProof::AndIntro(
            Box::new(HolDraftProof::ImpIntro {
                premise: left,
                body: Box::new(HolDraftProof::Hypothesis(0)),
            }),
            Box::new(HolDraftProof::ImpIntro {
                premise: right,
                body: Box::new(HolDraftProof::Hypothesis(0)),
            }),
        )
    }

    #[test]
    fn relation_paths_have_checked_polymorphic_endpoint_equations() {
        let mut elaborator = SpikeElaborator::new();
        let lists = ListLibrary::install(&mut elaborator).unwrap();
        let paths = RelationPathLibrary::install_named(
            &mut elaborator,
            &lists,
            &GraphLibraryNames::under_namespace("Graph"),
        )
        .unwrap();
        let element = CoreType::Parameter(lists.element_parameter);
        let edge_type = GraphLibrary::edge_type(element.clone());
        // Parameters E, start, finish; the nearest binder is finish.
        let nil_left = paths.valid_path_term(
            element.clone(),
            CoreTerm::Bound(2),
            lists.nil_term(element.clone()),
            CoreTerm::Bound(1),
            CoreTerm::Bound(0),
        );
        let nil_right = CoreTerm::equality(element.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1));
        // Parameters E, head, tail, start, finish.
        let cons_left = paths.valid_path_term(
            element.clone(),
            CoreTerm::Bound(4),
            lists.cons_term(element.clone(), CoreTerm::Bound(3), CoreTerm::Bound(2)),
            CoreTerm::Bound(1),
            CoreTerm::Bound(0),
        );
        let cons_right = CoreTerm::and(
            apply_many(CoreTerm::Bound(4), [CoreTerm::Bound(1), CoreTerm::Bound(3)]),
            paths.valid_path_term(
                element.clone(),
                CoreTerm::Bound(4),
                CoreTerm::Bound(2),
                CoreTerm::Bound(3),
                CoreTerm::Bound(0),
            ),
        );
        for (name, params, left, right) in [
            (
                "path_nil",
                vec![edge_type.clone(), element.clone(), element.clone()],
                nil_left,
                nil_right,
            ),
            (
                "path_cons",
                vec![
                    edge_type,
                    element.clone(),
                    lists.list_type(element.clone()),
                    element.clone(),
                    element.clone(),
                ],
                cons_left,
                cons_right,
            ),
        ] {
            let statement = CoreTerm::and(
                CoreTerm::implies(left.clone(), right.clone()),
                CoreTerm::implies(right.clone(), left.clone()),
            );
            let (_, receipt) = elaborator
                .declare_theorem_with_parameters(
                    name,
                    vec![lists.element_parameter],
                    params,
                    statement,
                    iff_proof(left, right),
                )
                .expect("path equation must be kernel checked");
            assert_eq!(
                receipt.proof().required_fragment(),
                StatementFragment::HigherOrder
            );
            assert!(receipt.proof().axiom_dependencies().is_empty());
            assert!(receipt.proof().incomplete_dependencies().is_empty());
            assert!(receipt
                .proof()
                .transitive_features()
                .contains(&ProofFeature::StructuralRecursion));
        }
    }

    #[test]
    fn relation_paths_preserve_direction_and_finish_and_reject_wrong_edges() {
        use crate::hol::terms::normalize;
        let mut elaborator = SpikeElaborator::new();
        let lists = ListLibrary::install(&mut elaborator).unwrap();
        let paths = RelationPathLibrary::install_named(
            &mut elaborator,
            &lists,
            &GraphLibraryNames::under_namespace("Graph"),
        )
        .unwrap();
        let vertex_id = elaborator.declare_base_type("Vertex", true).unwrap();
        let vertex = CoreType::constructor(vertex_id, vec![]);
        let mut constant =
            |name| CoreTerm::Constant(elaborator.declare_constant(name, vertex.clone()).unwrap());
        let start = constant("start");
        let middle = constant("middle");
        let finish = constant("finish");
        let other = constant("other");
        let edge = CoreTerm::Constant(
            elaborator
                .declare_constant("Road", GraphLibrary::edge_type(vertex.clone()))
                .unwrap(),
        );
        let path = lists.cons_term(
            vertex.clone(),
            middle.clone(),
            lists.cons_term(
                vertex.clone(),
                finish.clone(),
                lists.nil_term(vertex.clone()),
            ),
        );
        let valid = paths.valid_path_term(
            vertex.clone(),
            edge.clone(),
            path.clone(),
            start.clone(),
            finish.clone(),
        );
        let expected = CoreTerm::and(
            apply_many(edge.clone(), [start.clone(), middle.clone()]),
            CoreTerm::and(
                apply_many(edge.clone(), [middle, finish.clone()]),
                CoreTerm::equality(vertex.clone(), finish.clone(), finish.clone()),
            ),
        );
        assert_eq!(
            normalize(
                elaborator.types(),
                elaborator.constants(),
                &TermContext::new(),
                &valid
            )
            .unwrap(),
            expected
        );
        assert_eq!(
            elaborator.classify_with_parameters(&[], &valid).unwrap(),
            StatementFragment::FirstOrder,
            "a closed path unfolds to ordinary edge predicates and equality"
        );
        let open_path = paths.valid_path_term(
            vertex.clone(),
            edge.clone(),
            CoreTerm::Bound(0),
            start.clone(),
            finish.clone(),
        );
        assert_eq!(
            elaborator
                .classify_with_parameters(&[lists.list_type(vertex.clone())], &open_path)
                .unwrap(),
            StatementFragment::HigherOrder,
            "an open path retains the predicate-valued operator"
        );
        for (name, wrong) in [
            (
                "wrong_direction",
                paths.valid_path_term(
                    vertex.clone(),
                    edge.clone(),
                    path.clone(),
                    finish.clone(),
                    start.clone(),
                ),
            ),
            (
                "wrong_finish",
                paths.valid_path_term(vertex.clone(), edge.clone(), path, start.clone(), other),
            ),
            (
                "empty_changes_vertex",
                paths.valid_path_term(
                    vertex.clone(),
                    edge.clone(),
                    lists.nil_term(vertex.clone()),
                    start,
                    finish,
                ),
            ),
        ] {
            let before = elaborator.clone();
            assert!(elaborator
                .declare_theorem(
                    name,
                    vec![],
                    CoreTerm::implies(valid.clone(), wrong),
                    HolDraftProof::ImpIntro {
                        premise: valid.clone(),
                        body: Box::new(HolDraftProof::Hypothesis(0)),
                    }
                )
                .is_err());
            assert_eq!(elaborator, before);
        }
        let ill_typed = paths.valid_path_term(
            vertex.clone(),
            CoreTerm::Truth,
            lists.nil_term(vertex.clone()),
            CoreTerm::Truth,
            CoreTerm::Truth,
        );
        assert!(infer_type(
            elaborator.types(),
            elaborator.constants(),
            &TermContext::new(),
            &ill_typed
        )
        .is_err());
        let before = elaborator.clone();
        assert!(RelationPathLibrary::install_named(
            &mut elaborator,
            &lists,
            &GraphLibraryNames::under_namespace("Graph")
        )
        .is_err());
        assert_eq!(
            elaborator, before,
            "a name collision must not partially install a library"
        );
    }

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
