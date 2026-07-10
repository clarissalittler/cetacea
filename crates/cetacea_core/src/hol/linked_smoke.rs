//! Small executable path used to measure a linked HOL engine.
//!
//! Unlike the H3 curriculum examples, this deliberately avoids embedding a
//! large fixture in release artifacts. It still crosses the real declaration,
//! recursion, induction, theorem-reference, polymorphic-instantiation, receipt,
//! and policy paths.

use super::fragments::StatementFragment;
use super::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::CoreTerm;
use super::types::{CoreType, TypeParameter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkedHolSmokeReport {
    pub structural_required: StatementFragment,
    pub facade_required: StatementFragment,
    pub polymorphic_required: StatementFragment,
    pub axiom_dependencies: usize,
    pub incomplete_dependencies: usize,
}

pub fn run_linked_hol_smoke() -> Result<LinkedHolSmokeReport, SpikeError> {
    let mut elaborator = SpikeElaborator::new();
    let nat_id = elaborator.declare_base_type("Nat", true)?;
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

    let always = elaborator.declare_structural_definition(StructuralDefinitionSpec {
        name: "AlwaysNat".to_string(),
        type_parameters: Vec::new(),
        datatype: list,
        datatype_arguments: vec![nat.clone()],
        fixed_parameter_types: Vec::new(),
        result_type: CoreType::Prop,
        arms: vec![
            StructuralArmSpec::new(nil, CoreTerm::Truth),
            StructuralArmSpec::new(cons, CoreTerm::Truth),
        ],
    })?;
    let (_, structural) = elaborator.declare_theorem(
        "always_nil",
        Vec::new(),
        CoreTerm::apply(CoreTerm::Constant(always), nil_nat.clone()),
        HolDraftProof::TruthIntro,
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
            type_arguments: vec![nat],
            term_arguments: vec![CoreTerm::Constant(zero)],
        },
    )?;

    let receipts = [&structural, &facade, &polymorphic];
    Ok(LinkedHolSmokeReport {
        structural_required: structural.proof().required_fragment(),
        facade_required: facade.proof().required_fragment(),
        polymorphic_required: polymorphic.proof().required_fragment(),
        axiom_dependencies: receipts
            .iter()
            .map(|receipt| receipt.proof().axiom_dependencies().len())
            .sum(),
        incomplete_dependencies: receipts
            .iter()
            .map(|receipt| receipt.proof().incomplete_dependencies().len())
            .sum(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linked_smoke_reaches_restricted_and_higher_order_receipts_without_trust() {
        let report = run_linked_hol_smoke().expect("linked HOL smoke");
        assert_eq!(
            report.structural_required,
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(
            report.facade_required,
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(report.polymorphic_required, StatementFragment::HigherOrder);
        assert_eq!(report.axiom_dependencies, 0);
        assert_eq!(report.incomplete_dependencies, 0);
    }
}
