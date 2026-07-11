//! Checked finite-enumeration evidence over the reusable List package.
//!
//! `HasCard A xs n` means that `xs` has no duplicates, has length `n`, and
//! contains every `A`. The package can synthesize this evidence for a
//! parameterless inductive whose constructors are all nullary. That covers the
//! ordinary finite colors, labels, states, and small sample spaces used in a
//! discrete-mathematics sequence without adding a kernel primitive for
//! finiteness.

use super::fragments::DeclarationReceipt;
use super::library::{ListLength, ListLibrary};
use super::proofs::HolDraftProof;
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{ConstantId, CoreTerm};
use super::theorems::TheoremId;
use super::types::{CoreType, TypeConstructorId, TypeParameter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteEnumerationNames {
    pub has_card: String,
}

impl FiniteEnumerationNames {
    pub fn canonical() -> Self {
        Self::under_namespace("")
    }

    pub fn under_namespace(namespace: &str) -> Self {
        Self {
            has_card: if namespace.is_empty() {
                "HasCard".to_string()
            } else {
                format!("{namespace}.HasCard")
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteEnumerationLibrary {
    pub has_card: ConstantId,
    pub lists: ListLibrary,
    pub length: ListLength,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteEnumerationEvidence {
    pub datatype: TypeConstructorId,
    pub element_type: CoreType,
    pub constructors: Vec<ConstantId>,
    pub enumeration: CoreTerm,
    pub cardinal: CoreTerm,
    pub theorem: TheoremId,
    pub receipt: DeclarationReceipt,
}

impl FiniteEnumerationLibrary {
    pub fn install(
        elaborator: &mut SpikeElaborator,
        lists: &ListLibrary,
        length: &ListLength,
    ) -> Result<Self, SpikeError> {
        Self::install_named(
            elaborator,
            lists,
            length,
            &FiniteEnumerationNames::canonical(),
        )
    }

    pub fn install_named(
        elaborator: &mut SpikeElaborator,
        lists: &ListLibrary,
        length: &ListLength,
        names: &FiniteEnumerationNames,
    ) -> Result<Self, SpikeError> {
        let mut staged = elaborator.clone();
        let library = Self::install_into(&mut staged, lists, length, names)?;
        *elaborator = staged;
        Ok(library)
    }

    fn install_into(
        elaborator: &mut SpikeElaborator,
        lists: &ListLibrary,
        length: &ListLength,
        names: &FiniteEnumerationNames,
    ) -> Result<Self, SpikeError> {
        let element_parameter = TypeParameter::any(200);
        let element_type = CoreType::Parameter(element_parameter);
        let list_type = lists.list_type(element_type.clone());
        let natural_type = length.natural_type.clone();
        let body = CoreTerm::lambda(
            list_type.clone(),
            CoreTerm::lambda(
                natural_type.clone(),
                CoreTerm::and(
                    lists.nodup_term(element_type.clone(), CoreTerm::Bound(1)),
                    CoreTerm::and(
                        CoreTerm::equality(
                            natural_type.clone(),
                            length.apply(element_type.clone(), CoreTerm::Bound(1)),
                            CoreTerm::Bound(0),
                        ),
                        CoreTerm::forall(
                            element_type.clone(),
                            lists.member_term(
                                element_type.clone(),
                                CoreTerm::Bound(0),
                                CoreTerm::Bound(2),
                            ),
                        ),
                    ),
                ),
            ),
        );
        let has_card = elaborator.declare_polymorphic_transparent_definition(
            names.has_card.clone(),
            vec![element_parameter],
            CoreType::arrow(list_type, CoreType::arrow(natural_type, CoreType::Prop)),
            body,
        )?;
        Ok(Self {
            has_card,
            lists: *lists,
            length: length.clone(),
        })
    }

    pub fn has_card_term(
        &self,
        element_type: CoreType,
        enumeration: CoreTerm,
        cardinal: CoreTerm,
    ) -> CoreTerm {
        CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(self.has_card, vec![element_type]),
                enumeration,
            ),
            cardinal,
        )
    }

    /// Enumerate every constructor of a parameterless nullary inductive and
    /// store a checked `HasCard` theorem for it.
    pub fn declare_nullary_inductive(
        &self,
        elaborator: &mut SpikeElaborator,
        theorem_name: impl Into<String>,
        datatype: TypeConstructorId,
    ) -> Result<FiniteEnumerationEvidence, SpikeError> {
        let declaration = elaborator
            .inductives()
            .declaration(datatype)
            .cloned()
            .ok_or_else(|| SpikeError {
                message: format!("unknown inductive datatype id `{}`", datatype.0),
            })?;
        if !declaration.type_parameters.is_empty() {
            return Err(SpikeError {
                message: format!(
                    "finite enumeration of `{}` currently requires a parameterless datatype",
                    declaration.name
                ),
            });
        }
        if let Some(constructor) = declaration
            .constructors
            .iter()
            .find(|constructor| !constructor.field_types.is_empty())
        {
            return Err(SpikeError {
                message: format!(
                    "finite enumeration of `{}` requires nullary constructors, but `{}` has {} field(s)",
                    declaration.name,
                    constructor.name,
                    constructor.field_types.len()
                ),
            });
        }

        let element_type = CoreType::constructor(datatype, Vec::new());
        let constructors = declaration
            .constructors
            .iter()
            .map(|constructor| constructor.constant)
            .collect::<Vec<_>>();
        let enumeration = self.enumeration_term(element_type.clone(), &constructors);
        let cardinal = self.cardinal_numeral(constructors.len());
        let statement =
            self.has_card_term(element_type.clone(), enumeration.clone(), cardinal.clone());
        let proof = HolDraftProof::AndIntro(
            Box::new(self.nodup_proof(element_type.clone(), &constructors)),
            Box::new(HolDraftProof::AndIntro(
                Box::new(HolDraftProof::EqualityRefl(cardinal.clone())),
                Box::new(self.coverage_proof(
                    datatype,
                    element_type.clone(),
                    &constructors,
                    enumeration.clone(),
                )),
            )),
        );
        let (theorem, receipt) =
            elaborator.declare_theorem(theorem_name, Vec::new(), statement, proof)?;
        Ok(FiniteEnumerationEvidence {
            datatype,
            element_type,
            constructors,
            enumeration,
            cardinal,
            theorem,
            receipt,
        })
    }

    fn enumeration_term(&self, element_type: CoreType, constructors: &[ConstantId]) -> CoreTerm {
        constructors.iter().rev().fold(
            self.lists.nil_term(element_type.clone()),
            |tail, constructor| {
                self.lists
                    .cons_term(element_type.clone(), CoreTerm::Constant(*constructor), tail)
            },
        )
    }

    fn cardinal_numeral(&self, cardinality: usize) -> CoreTerm {
        (0..cardinality).fold(CoreTerm::Constant(self.length.zero), |number, _| {
            CoreTerm::apply(CoreTerm::Constant(self.length.successor), number)
        })
    }

    fn nodup_proof(&self, element_type: CoreType, constructors: &[ConstantId]) -> HolDraftProof {
        let Some((head, tail)) = constructors.split_first() else {
            return HolDraftProof::TruthIntro;
        };
        let premise = self.lists.member_term(
            element_type.clone(),
            CoreTerm::Constant(*head),
            self.enumeration_term(element_type.clone(), tail),
        );
        HolDraftProof::AndIntro(
            Box::new(HolDraftProof::ImpIntro {
                premise,
                body: Box::new(self.not_member_case(element_type.clone(), *head, tail)),
            }),
            Box::new(self.nodup_proof(element_type, tail)),
        )
    }

    fn not_member_case(
        &self,
        element_type: CoreType,
        head: ConstantId,
        tail: &[ConstantId],
    ) -> HolDraftProof {
        let Some((_, rest)) = tail.split_first() else {
            return HolDraftProof::Hypothesis(0);
        };
        HolDraftProof::OrElim {
            proof_or: Box::new(HolDraftProof::Hypothesis(0)),
            left_case: Box::new(HolDraftProof::ConstructorDisjoint {
                proof_equality: Box::new(HolDraftProof::Hypothesis(0)),
            }),
            right_case: Box::new(self.not_member_case(element_type, head, rest)),
            target: CoreTerm::Falsity,
        }
    }

    fn coverage_proof(
        &self,
        datatype: TypeConstructorId,
        element_type: CoreType,
        constructors: &[ConstantId],
        enumeration: CoreTerm,
    ) -> HolDraftProof {
        HolDraftProof::ForallIntro {
            domain: element_type.clone(),
            body: Box::new(HolDraftProof::Induction {
                datatype,
                type_arguments: Vec::new(),
                motive: CoreTerm::lambda(
                    element_type.clone(),
                    self.lists
                        .member_term(element_type.clone(), CoreTerm::Bound(0), enumeration),
                ),
                scrutinee: CoreTerm::Bound(0),
                cases: constructors
                    .iter()
                    .enumerate()
                    .map(|(index, constructor)| {
                        self.membership_proof(
                            element_type.clone(),
                            *constructor,
                            constructors,
                            index,
                        )
                    })
                    .collect(),
            }),
        }
    }

    fn membership_proof(
        &self,
        element_type: CoreType,
        value: ConstantId,
        constructors: &[ConstantId],
        index: usize,
    ) -> HolDraftProof {
        let head = constructors[0];
        if index == 0 {
            HolDraftProof::OrIntroLeft {
                proof_left: Box::new(HolDraftProof::EqualityRefl(CoreTerm::Constant(value))),
                right: self.lists.member_term(
                    element_type.clone(),
                    CoreTerm::Constant(value),
                    self.enumeration_term(element_type, &constructors[1..]),
                ),
            }
        } else {
            HolDraftProof::OrIntroRight {
                left: CoreTerm::equality(
                    element_type.clone(),
                    CoreTerm::Constant(value),
                    CoreTerm::Constant(head),
                ),
                proof_right: Box::new(self.membership_proof(
                    element_type,
                    value,
                    &constructors[1..],
                    index - 1,
                )),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{ProofFeature, StatementFragment};
    use crate::hol::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
    use crate::hol::terms::{infer_type, TermContext};

    fn elaborator_with_library() -> (SpikeElaborator, FiniteEnumerationLibrary) {
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
        let finite = FiniteEnumerationLibrary::install(&mut elaborator, &lists, &length)
            .expect("install finite package");
        (elaborator, finite)
    }

    #[test]
    fn nullary_inductive_enumeration_is_exhaustive_distinct_and_fragment_precise() {
        let (mut elaborator, finite) = elaborator_with_library();
        let has_card_receipt = elaborator
            .definition_receipt(finite.has_card)
            .expect("HasCard definition receipt");
        assert_eq!(
            has_card_receipt.proof().direct_dependencies(),
            &std::collections::BTreeSet::from([
                elaborator
                    .definition_receipt(finite.lists.member)
                    .expect("Member receipt")
                    .id(),
                elaborator
                    .definition_receipt(finite.lists.nodup)
                    .expect("Nodup receipt")
                    .id(),
                elaborator
                    .definition_receipt(finite.length.constant)
                    .expect("length receipt")
                    .id(),
            ])
        );
        let traffic = elaborator
            .declare_inductive(InductiveSpec::new(
                "Traffic",
                Vec::new(),
                vec![
                    InductiveConstructorSpec::new("stop", Vec::new()),
                    InductiveConstructorSpec::new("wait", Vec::new()),
                    InductiveConstructorSpec::new("go", Vec::new()),
                ],
            ))
            .expect("declare Traffic");
        let evidence = finite
            .declare_nullary_inductive(&mut elaborator, "traffic_has_card", traffic)
            .expect("enumerate Traffic");

        assert_eq!(evidence.constructors.len(), 3);
        assert_eq!(
            elaborator.theorems().resolve("traffic_has_card"),
            Some(evidence.theorem)
        );
        assert_eq!(
            infer_type(
                elaborator.types(),
                elaborator.constants(),
                &TermContext::new(),
                &evidence.enumeration,
            )
            .expect("enumeration type"),
            finite.lists.list_type(evidence.element_type.clone())
        );
        assert_eq!(
            evidence.receipt.proof().statement_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            evidence.receipt.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert!(evidence
            .receipt
            .proof()
            .direct_features()
            .contains(&ProofFeature::Induction));
        assert!(evidence
            .receipt
            .proof()
            .transitive_features()
            .contains(&ProofFeature::StructuralRecursion));
        assert!(evidence.receipt.proof().axiom_dependencies().is_empty());
        assert!(evidence
            .receipt
            .proof()
            .incomplete_dependencies()
            .is_empty());

        let open_prop_instance = finite.has_card_term(
            CoreType::Prop,
            CoreTerm::Bound(0),
            CoreTerm::Constant(finite.length.zero),
        );
        assert_eq!(
            elaborator
                .classify_with_parameters(
                    &[finite.lists.list_type(CoreType::Prop)],
                    &open_prop_instance,
                )
                .expect("classify List Prop cardinality"),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn non_nullary_datatypes_and_name_collisions_leave_evidence_unchanged() {
        let (mut elaborator, finite) = elaborator_with_library();
        let names = FiniteEnumerationNames::under_namespace("@test.finite");
        let namespaced = FiniteEnumerationLibrary::install_named(
            &mut elaborator,
            &finite.lists,
            &finite.length,
            &names,
        )
        .expect("install namespaced finite package");
        assert_eq!(
            elaborator.constants().resolve(&names.has_card),
            Some(namespaced.has_card)
        );
        let before_package_collision = elaborator.clone();
        let package_collision = FiniteEnumerationLibrary::install_named(
            &mut elaborator,
            &finite.lists,
            &finite.length,
            &names,
        )
        .expect_err("duplicate package name rejects installation");
        assert!(package_collision.message.contains(&names.has_card));
        assert_eq!(elaborator, before_package_collision);

        let wrapper = elaborator
            .declare_inductive(InductiveSpec::new(
                "Wrapper",
                Vec::new(),
                vec![InductiveConstructorSpec::new(
                    "wrap",
                    vec![InductiveFieldType::existing(
                        finite.length.natural_type.clone(),
                    )],
                )],
            ))
            .expect("declare Wrapper");
        let before_field_error = elaborator.clone();
        let field_error = finite
            .declare_nullary_inductive(&mut elaborator, "wrapper_has_card", wrapper)
            .expect_err("constructor fields require explicit enumeration evidence");
        assert!(field_error
            .message
            .contains("requires nullary constructors"));
        assert_eq!(elaborator, before_field_error);

        let bit = elaborator
            .declare_inductive(InductiveSpec::new(
                "Bit",
                Vec::new(),
                vec![
                    InductiveConstructorSpec::new("off", Vec::new()),
                    InductiveConstructorSpec::new("on", Vec::new()),
                ],
            ))
            .expect("declare Bit");
        elaborator
            .declare_theorem(
                "bit_has_card",
                Vec::new(),
                CoreTerm::Truth,
                HolDraftProof::TruthIntro,
            )
            .expect("reserve theorem name");
        let before_collision = elaborator.clone();
        let collision = finite
            .declare_nullary_inductive(&mut elaborator, "bit_has_card", bit)
            .expect_err("theorem collision rejects evidence");
        assert!(collision.message.contains("bit_has_card"));
        assert_eq!(elaborator, before_collision);
    }
}
