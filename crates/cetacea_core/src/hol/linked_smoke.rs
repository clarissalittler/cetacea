//! Small executable path used to measure a linked HOL engine.
//!
//! Unlike the H3 curriculum examples, this deliberately avoids embedding a
//! large fixture in release artifacts. It still crosses the real declaration,
//! recursion, induction, theorem-reference, polymorphic-instantiation, receipt,
//! and policy paths.

use super::fragments::StatementFragment;
use super::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::CoreTerm;
use super::types::{CoreType, TypeParameter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkedHolSmokeReport {
    pub structural_required: StatementFragment,
    pub transparent_required: StatementFragment,
    pub facade_required: StatementFragment,
    pub polymorphic_required: StatementFragment,
    pub product_required: StatementFragment,
    pub set_required: StatementFragment,
    pub axiom_dependencies: usize,
    pub incomplete_dependencies: usize,
    pub trusted_user_axiom_dependencies: usize,
    pub incomplete_user_dependencies: usize,
    pub classical_user_features: usize,
}

pub fn run_linked_hol_smoke() -> Result<LinkedHolSmokeReport, SpikeError> {
    let mut elaborator = SpikeElaborator::new();
    let nat_id = elaborator.declare_base_type("Nat", true)?;
    elaborator.declare_legacy_set_type("Set")?;
    let nat = CoreType::constructor(nat_id, Vec::new());
    let zero = elaborator.declare_constant("zero", nat.clone())?;

    let list_parameter = TypeParameter::any(500);
    let list = elaborator.declare_inductive(InductiveSpec::new(
        "List",
        vec![list_parameter],
        vec![
            InductiveConstructorSpec::new("nil", Vec::new()),
            InductiveConstructorSpec::new(
                "cons",
                vec![
                    InductiveFieldType::existing(CoreType::Parameter(list_parameter)),
                    InductiveFieldType::Recursive,
                ],
            ),
        ],
    ))?;
    let nil = elaborator.resolve_constant("nil")?;
    let cons = elaborator.resolve_constant("cons")?;
    let list_nat = CoreType::constructor(list, vec![nat.clone()]);
    let nil_nat = CoreTerm::instantiate_constant(nil, vec![nat.clone()]);
    let singleton_nat = CoreTerm::apply(
        CoreTerm::apply(
            CoreTerm::instantiate_constant(cons, vec![nat.clone()]),
            CoreTerm::Constant(zero),
        ),
        nil_nat.clone(),
    );

    let always = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "AlwaysNat".to_string(),
        type_parameters: Vec::new(),
        datatype: list,
        datatype_arguments: vec![nat.clone()],
        fixed_parameter_types: vec![nat.clone()],
        recursive_argument_index: 0,
        result_type: CoreType::Prop,
        arms: vec![
            StructuralArmSpec::new(
                nil,
                CoreTerm::equality(
                    nat.clone(),
                    StructuralArmLayout::new(0, 0, 1)
                        .fixed_parameter(0)
                        .expect("fallback value"),
                    StructuralArmLayout::new(0, 0, 1)
                        .fixed_parameter(0)
                        .expect("fallback value"),
                ),
            ),
            StructuralArmSpec::new(
                cons,
                StructuralArmLayout::new(2, 1, 1)
                    .recursive_result(0)
                    .expect("recursive proposition"),
            ),
        ],
    })?;
    let (_, structural) = elaborator.declare_theorem(
        "always_singleton",
        Vec::new(),
        CoreTerm::apply(
            CoreTerm::apply(CoreTerm::Constant(always), singleton_nat),
            CoreTerm::Constant(zero),
        ),
        HolDraftProof::EqualityRefl(CoreTerm::Constant(zero)),
    )?;
    let always_alias = elaborator.declare_transparent_definition(
        "AlwaysAlias",
        CoreType::arrow(list_nat.clone(), CoreType::Prop),
        CoreTerm::lambda(
            list_nat.clone(),
            CoreTerm::apply(
                CoreTerm::apply(CoreTerm::Constant(always), CoreTerm::Bound(0)),
                CoreTerm::Constant(zero),
            ),
        ),
    )?;
    let (_, transparent) = elaborator.declare_theorem(
        "always_alias_nil",
        Vec::new(),
        CoreTerm::apply(CoreTerm::Constant(always_alias), nil_nat.clone()),
        HolDraftProof::EqualityRefl(CoreTerm::Constant(zero)),
    )?;

    let (induction_source, _) = elaborator.declare_theorem(
        "induction_source",
        Vec::new(),
        CoreTerm::Truth,
        HolDraftProof::Induction {
            datatype: list,
            type_arguments: vec![nat.clone()],
            motive: CoreTerm::lambda(list_nat, CoreTerm::Truth),
            scrutinee: nil_nat,
            cases: vec![HolDraftProof::TruthIntro, HolDraftProof::TruthIntro],
        },
    )?;
    let (_, facade) = elaborator.declare_theorem(
        "induction_facade",
        Vec::new(),
        CoreTerm::Truth,
        HolDraftProof::TheoremRef {
            theorem: induction_source,
            type_arguments: Vec::new(),
            term_arguments: Vec::new(),
        },
    )?;

    let theorem_parameter = TypeParameter::any(501);
    let identity = elaborator
        .declare_theorem_with_parameters(
            "identity",
            vec![theorem_parameter],
            vec![CoreType::Parameter(theorem_parameter)],
            CoreTerm::equality(
                CoreType::Parameter(theorem_parameter),
                CoreTerm::Bound(0),
                CoreTerm::Bound(0),
            ),
            HolDraftProof::EqualityRefl(CoreTerm::Bound(0)),
        )?
        .0;
    let (_, polymorphic) = elaborator.declare_theorem(
        "zero_identity",
        Vec::new(),
        CoreTerm::equality(
            nat.clone(),
            CoreTerm::Constant(zero),
            CoreTerm::Constant(zero),
        ),
        HolDraftProof::TheoremRef {
            theorem: identity,
            type_arguments: vec![nat.clone()],
            term_arguments: vec![CoreTerm::Constant(zero)],
        },
    )?;
    let pair = CoreTerm::pair(CoreTerm::Constant(zero), CoreTerm::Constant(zero));
    let (_, product) = elaborator.declare_theorem(
        "first_pair_zero",
        Vec::new(),
        CoreTerm::equality(nat.clone(), CoreTerm::first(pair), CoreTerm::Constant(zero)),
        HolDraftProof::EqualityRefl(CoreTerm::Constant(zero)),
    )?;

    let set_nat = elaborator.types().legacy_set_type(nat.clone())?;
    let in_left = CoreTerm::membership(nat.clone(), CoreTerm::Bound(0), CoreTerm::Bound(2));
    let in_right = CoreTerm::membership(nat.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1));
    let set_ext_statement = CoreTerm::implies(
        CoreTerm::forall(
            nat.clone(),
            CoreTerm::and(
                CoreTerm::implies(in_left.clone(), in_right.clone()),
                CoreTerm::implies(in_right, in_left),
            ),
        ),
        CoreTerm::equality(set_nat.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
    );
    let (set_ext, _) = elaborator.declare_trusted_axiom_with_parameters(
        "set_ext_nat",
        Vec::new(),
        vec![set_nat.clone(), set_nat.clone()],
        set_ext_statement,
    )?;
    let empty_nat = CoreTerm::empty_set(nat.clone());
    let (_, trusted_user) = elaborator.declare_theorem(
        "empty_extensional",
        Vec::new(),
        CoreTerm::equality(set_nat, empty_nat.clone(), empty_nat.clone()),
        HolDraftProof::ImpElim {
            proof_implication: Box::new(HolDraftProof::TheoremRef {
                theorem: set_ext,
                type_arguments: Vec::new(),
                term_arguments: vec![empty_nat.clone(), empty_nat],
            }),
            proof_argument: Box::new(HolDraftProof::ForallIntro {
                domain: nat.clone(),
                body: Box::new(HolDraftProof::AndIntro(
                    Box::new(HolDraftProof::ImpIntro {
                        premise: CoreTerm::Falsity,
                        body: Box::new(HolDraftProof::Hypothesis(0)),
                    }),
                    Box::new(HolDraftProof::ImpIntro {
                        premise: CoreTerm::Falsity,
                        body: Box::new(HolDraftProof::Hypothesis(0)),
                    }),
                )),
            }),
        },
    )?;

    let (unfinished, _) = elaborator.declare_incomplete_theorem(
        "unfinished_truth",
        Vec::new(),
        CoreTerm::Truth,
        HolDraftProof::Sorry {
            target: CoreTerm::Truth,
        },
    )?;
    let (_, incomplete_user) = elaborator.declare_incomplete_theorem(
        "unfinished_facade",
        Vec::new(),
        CoreTerm::Truth,
        HolDraftProof::TheoremRef {
            theorem: unfinished,
            type_arguments: Vec::new(),
            term_arguments: Vec::new(),
        },
    )?;

    let atom = elaborator.declare_constant("P", CoreType::Prop)?;
    let proposition = CoreTerm::Constant(atom);
    let classical_statement = CoreTerm::or(
        proposition.clone(),
        CoreTerm::implies(proposition.clone(), CoreTerm::Falsity),
    );
    let (classical, _) = elaborator.declare_theorem(
        "excluded_middle",
        Vec::new(),
        classical_statement.clone(),
        HolDraftProof::ExcludedMiddle { proposition },
    )?;
    let (_, classical_user) = elaborator.declare_theorem(
        "uses_excluded_middle",
        Vec::new(),
        classical_statement,
        HolDraftProof::TheoremRef {
            theorem: classical,
            type_arguments: Vec::new(),
            term_arguments: Vec::new(),
        },
    )?;

    let receipts = [&structural, &transparent, &facade, &polymorphic, &product];
    Ok(LinkedHolSmokeReport {
        structural_required: structural.proof().required_fragment(),
        transparent_required: transparent.proof().required_fragment(),
        facade_required: facade.proof().required_fragment(),
        polymorphic_required: polymorphic.proof().required_fragment(),
        product_required: product.proof().required_fragment(),
        set_required: trusted_user.proof().required_fragment(),
        axiom_dependencies: receipts
            .iter()
            .map(|receipt| receipt.proof().axiom_dependencies().len())
            .sum(),
        incomplete_dependencies: receipts
            .iter()
            .map(|receipt| receipt.proof().incomplete_dependencies().len())
            .sum(),
        trusted_user_axiom_dependencies: trusted_user.proof().axiom_dependencies().len(),
        incomplete_user_dependencies: incomplete_user.proof().incomplete_dependencies().len(),
        classical_user_features: classical_user.proof().transitive_features().len(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linked_smoke_reaches_fragments_and_reports_trust_transitively() {
        let report = run_linked_hol_smoke().expect("linked HOL smoke");
        assert_eq!(
            report.structural_required,
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            report.transparent_required,
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            report.facade_required,
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(report.polymorphic_required, StatementFragment::FirstOrder);
        assert_eq!(report.product_required, StatementFragment::FirstOrder);
        assert_eq!(report.set_required, StatementFragment::FirstOrder);
        assert_eq!(report.axiom_dependencies, 0);
        assert_eq!(report.incomplete_dependencies, 0);
        assert_eq!(report.trusted_user_axiom_dependencies, 1);
        assert_eq!(report.incomplete_user_dependencies, 1);
        assert_eq!(report.classical_user_features, 1);
    }
}
