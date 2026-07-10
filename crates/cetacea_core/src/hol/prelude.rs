//! Checked core declarations behind the legacy `Nat` and `Set` syntax.
//!
//! The compatibility parser is deliberately not involved here. Installing the
//! prelude into an empty [`SpikeElaborator`] creates the stable IDs that later
//! AST lowering uses for builtin syntax. Every recursive operation is admitted
//! by the ordinary structural-recursion checker; this module does not install
//! an extra evaluator or a trusted arithmetic oracle.

use super::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{ConstantId, CoreTerm};
use super::types::{CoreType, TypeConstructorId};

/// Stable core declarations used when lowering the legacy builtin syntax.
///
/// `predecessor` and `less_equal_tail` are implementation helpers rather than
/// surface declarations. In particular, installing this prelude does not take
/// the user-visible name `pred`, which remains an ordinary definition in
/// `std/nat.ctea`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompatibilityPrelude {
    nat: TypeConstructorId,
    set: TypeConstructorId,
    zero: ConstantId,
    successor: ConstantId,
    addition: ConstantId,
    multiplication: ConstantId,
    subtraction: ConstantId,
    less_equal: ConstantId,
    predecessor: ConstantId,
    less_equal_tail: ConstantId,
}

impl CompatibilityPrelude {
    /// Transactionally install the compatibility primitives.
    ///
    /// A failed name, type, positivity, or recursion check leaves the supplied
    /// elaborator exactly as it was before the call.
    pub fn install(elaborator: &mut SpikeElaborator) -> Result<Self, SpikeError> {
        let mut staged = elaborator.clone();

        let nat = staged.declare_inductive(InductiveSpec::new(
            "Nat",
            Vec::new(),
            vec![
                InductiveConstructorSpec::new("zero", Vec::new()),
                InductiveConstructorSpec::new("succ", vec![InductiveFieldType::Recursive]),
            ],
        ))?;
        let set = staged.declare_legacy_set_type("Set")?;
        let nat_type = CoreType::constructor(nat, Vec::new());
        let zero = staged.resolve_constant("zero")?;
        let successor = staged.resolve_constant("succ")?;

        let unary_successor = StructuralArmLayout::new(1, 1, 0);
        let predecessor = staged.declare_structural_definition(StructuralDefinitionSpec {
            name: "@compat.pred".to_string(),
            type_parameters: Vec::new(),
            datatype: nat,
            datatype_arguments: Vec::new(),
            recursive_argument_index: 0,
            fixed_parameter_types: Vec::new(),
            result_type: nat_type.clone(),
            arms: vec![
                StructuralArmSpec::new(zero, CoreTerm::Constant(zero)),
                StructuralArmSpec::new(
                    successor,
                    unary_successor
                        .field(0)
                        .expect("successor has one checked field"),
                ),
            ],
        })?;
        let binary_zero = StructuralArmLayout::new(0, 0, 1);
        let binary_successor = StructuralArmLayout::new(1, 1, 1);
        let addition = staged.declare_structural_definition(StructuralDefinitionSpec {
            name: "add".to_string(),
            type_parameters: Vec::new(),
            datatype: nat,
            datatype_arguments: Vec::new(),
            recursive_argument_index: 0,
            fixed_parameter_types: vec![nat_type.clone()],
            result_type: nat_type.clone(),
            arms: vec![
                StructuralArmSpec::new(
                    zero,
                    binary_zero
                        .fixed_parameter(0)
                        .expect("addition has one fixed argument"),
                ),
                StructuralArmSpec::new(
                    successor,
                    CoreTerm::apply(
                        CoreTerm::Constant(successor),
                        binary_successor
                            .recursive_result(0)
                            .expect("successor has one recursive result"),
                    ),
                ),
            ],
        })?;

        let multiplication = staged.declare_structural_definition(StructuralDefinitionSpec {
            name: "mul".to_string(),
            type_parameters: Vec::new(),
            datatype: nat,
            datatype_arguments: Vec::new(),
            recursive_argument_index: 0,
            fixed_parameter_types: vec![nat_type.clone()],
            result_type: nat_type.clone(),
            arms: vec![
                StructuralArmSpec::new(zero, CoreTerm::Constant(zero)),
                StructuralArmSpec::new(
                    successor,
                    apply2(
                        addition,
                        binary_successor
                            .fixed_parameter(0)
                            .expect("multiplication has one fixed argument"),
                        binary_successor
                            .recursive_result(0)
                            .expect("successor has one recursive result"),
                    ),
                ),
            ],
        })?;

        // Truncated subtraction recurses on the second source argument:
        //   sub n 0       = n
        //   sub n (S m)   = pred (sub n m)
        // This is terminating and computes every closed numeral. The legacy
        // normalizer's additional open-term shortcuts are supplied later as
        // checked simp lemmas rather than unsound conversion rules.
        let subtraction = staged.declare_structural_definition(StructuralDefinitionSpec {
            name: "sub".to_string(),
            type_parameters: Vec::new(),
            datatype: nat,
            datatype_arguments: Vec::new(),
            recursive_argument_index: 1,
            fixed_parameter_types: vec![nat_type.clone()],
            result_type: nat_type.clone(),
            arms: vec![
                StructuralArmSpec::new(
                    zero,
                    binary_zero
                        .fixed_parameter(0)
                        .expect("subtraction has one fixed argument"),
                ),
                StructuralArmSpec::new(
                    successor,
                    CoreTerm::apply(
                        CoreTerm::Constant(predecessor),
                        binary_successor
                            .recursive_result(0)
                            .expect("successor has one recursive result"),
                    ),
                ),
            ],
        })?;

        // `le` is nested structural recursion without a primitive proposition
        // evaluator. The helper maps a predecessor predicate `p` to the Nat
        // predicate that is false at zero and `p k` at `succ k`.
        let predicate_type = CoreType::arrow(nat_type.clone(), CoreType::Prop);
        let tail_successor = StructuralArmLayout::new(1, 1, 1);
        let less_equal_tail = staged.declare_structural_definition(StructuralDefinitionSpec {
            name: "@compat.le_tail".to_string(),
            type_parameters: Vec::new(),
            datatype: nat,
            datatype_arguments: Vec::new(),
            recursive_argument_index: 1,
            fixed_parameter_types: vec![predicate_type.clone()],
            result_type: CoreType::Prop,
            arms: vec![
                StructuralArmSpec::new(zero, CoreTerm::Falsity),
                StructuralArmSpec::new(
                    successor,
                    CoreTerm::apply(
                        tail_successor
                            .fixed_parameter(0)
                            .expect("less-equal tail has one predicate argument"),
                        tail_successor
                            .field(0)
                            .expect("successor has one checked field"),
                    ),
                ),
            ],
        })?;
        let less_equal = staged.declare_structural_definition(StructuralDefinitionSpec {
            name: "le".to_string(),
            type_parameters: Vec::new(),
            datatype: nat,
            datatype_arguments: Vec::new(),
            recursive_argument_index: 0,
            fixed_parameter_types: Vec::new(),
            result_type: predicate_type,
            arms: vec![
                StructuralArmSpec::new(zero, CoreTerm::lambda(nat_type.clone(), CoreTerm::Truth)),
                StructuralArmSpec::new(
                    successor,
                    CoreTerm::apply(
                        CoreTerm::Constant(less_equal_tail),
                        unary_successor
                            .recursive_result(0)
                            .expect("successor has one recursive predicate"),
                    ),
                ),
            ],
        })?;

        *elaborator = staged;
        Ok(Self {
            nat,
            set,
            zero,
            successor,
            addition,
            multiplication,
            subtraction,
            less_equal,
            predecessor,
            less_equal_tail,
        })
    }

    pub fn nat_constructor(&self) -> TypeConstructorId {
        self.nat
    }

    pub fn set_constructor(&self) -> TypeConstructorId {
        self.set
    }

    pub fn nat_type(&self) -> CoreType {
        CoreType::constructor(self.nat, Vec::new())
    }

    pub fn zero(&self) -> ConstantId {
        self.zero
    }

    pub fn successor(&self) -> ConstantId {
        self.successor
    }

    pub fn addition(&self) -> ConstantId {
        self.addition
    }

    pub fn multiplication(&self) -> ConstantId {
        self.multiplication
    }

    pub fn subtraction(&self) -> ConstantId {
        self.subtraction
    }

    pub fn less_equal(&self) -> ConstantId {
        self.less_equal
    }
}

fn apply2(function: ConstantId, left: CoreTerm, right: CoreTerm) -> CoreTerm {
    CoreTerm::apply(CoreTerm::apply(CoreTerm::Constant(function), left), right)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{StatementFragment, TeachingProfile};
    use crate::hol::proofs::HolDraftProof;
    use crate::hol::terms::{definitionally_equal, infer_type, normalize, TermContext};
    use crate::hol::{ReceiptPolicy, TypeSignature};

    fn fixture() -> (SpikeElaborator, CompatibilityPrelude) {
        let mut elaborator = SpikeElaborator::new();
        let prelude = CompatibilityPrelude::install(&mut elaborator).expect("checked prelude");
        (elaborator, prelude)
    }

    fn successor(prelude: &CompatibilityPrelude, value: CoreTerm) -> CoreTerm {
        CoreTerm::apply(CoreTerm::Constant(prelude.successor()), value)
    }

    fn binary(function: ConstantId, left: CoreTerm, right: CoreTerm) -> CoreTerm {
        apply2(function, left, right)
    }

    fn numeral(prelude: &CompatibilityPrelude, value: usize) -> CoreTerm {
        (0..value).fold(CoreTerm::Constant(prelude.zero()), |term, _| {
            successor(prelude, term)
        })
    }

    fn assert_def_eq(
        elaborator: &SpikeElaborator,
        context: &TermContext,
        left: CoreTerm,
        right: CoreTerm,
    ) {
        assert!(
            definitionally_equal(
                elaborator.types(),
                elaborator.constants(),
                context,
                &left,
                &right,
            )
            .expect("well-typed definitional equality"),
            "left normalized to {:?}, right normalized to {:?}",
            normalize(elaborator.types(), elaborator.constants(), context, &left,)
                .expect("normalize left"),
            normalize(elaborator.types(), elaborator.constants(), context, &right,)
                .expect("normalize right"),
        );
    }

    #[test]
    fn installation_is_checked_typed_and_transactional() {
        let (elaborator, prelude) = fixture();
        assert_eq!(
            elaborator.types().resolve("Nat"),
            Some(prelude.nat_constructor())
        );
        assert_eq!(
            elaborator.types().legacy_set_constructor(),
            Some(prelude.set_constructor())
        );

        let nat = prelude.nat_type();
        let binary_nat = CoreType::arrow(nat.clone(), CoreType::arrow(nat.clone(), nat.clone()));
        for operation in [
            prelude.addition(),
            prelude.multiplication(),
            prelude.subtraction(),
        ] {
            assert_eq!(
                infer_type(
                    elaborator.types(),
                    elaborator.constants(),
                    &TermContext::new(),
                    &CoreTerm::Constant(operation),
                ),
                Ok(binary_nat.clone())
            );
        }
        assert_eq!(
            infer_type(
                elaborator.types(),
                elaborator.constants(),
                &TermContext::new(),
                &CoreTerm::Constant(prelude.less_equal()),
            ),
            Ok(CoreType::arrow(
                nat.clone(),
                CoreType::arrow(nat, CoreType::Prop),
            ))
        );

        let mut occupied = SpikeElaborator::new();
        occupied
            .declare_base_type("Nat", true)
            .expect("occupy builtin name");
        let before = occupied.clone();
        let error = CompatibilityPrelude::install(&mut occupied)
            .expect_err("duplicate Nat must reject the entire prelude");
        assert!(error.message.contains("already declared"));
        assert_eq!(occupied, before);
    }

    #[test]
    fn primary_open_nat_equations_reduce_definitionally() {
        let (elaborator, prelude) = fixture();
        let nat = prelude.nat_type();
        let context = TermContext::new().with_bound(nat.clone()).with_bound(nat);
        let x = CoreTerm::Bound(1);
        let y = CoreTerm::Bound(0);
        let zero = CoreTerm::Constant(prelude.zero());

        assert_def_eq(
            &elaborator,
            &context,
            CoreTerm::apply(CoreTerm::Constant(prelude.predecessor), zero.clone()),
            zero.clone(),
        );
        assert_def_eq(
            &elaborator,
            &context,
            CoreTerm::apply(
                CoreTerm::Constant(prelude.predecessor),
                successor(&prelude, x.clone()),
            ),
            x.clone(),
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(prelude.addition(), zero.clone(), y.clone()),
            y.clone(),
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(
                prelude.addition(),
                successor(&prelude, x.clone()),
                y.clone(),
            ),
            successor(&prelude, binary(prelude.addition(), x.clone(), y.clone())),
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(prelude.multiplication(), zero.clone(), y.clone()),
            zero.clone(),
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(
                prelude.multiplication(),
                successor(&prelude, x.clone()),
                y.clone(),
            ),
            binary(
                prelude.addition(),
                y.clone(),
                binary(prelude.multiplication(), x.clone(), y.clone()),
            ),
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(prelude.subtraction(), x.clone(), zero.clone()),
            x.clone(),
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(prelude.less_equal(), zero.clone(), y.clone()),
            CoreTerm::Truth,
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(
                prelude.less_equal(),
                successor(&prelude, x.clone()),
                zero.clone(),
            ),
            CoreTerm::Falsity,
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(
                prelude.less_equal(),
                successor(&prelude, x.clone()),
                successor(&prelude, y.clone()),
            ),
            binary(prelude.less_equal(), x, y),
        );
    }

    #[test]
    fn closed_arithmetic_matches_legacy_numerals() {
        let (elaborator, prelude) = fixture();
        let context = TermContext::new();
        let two = numeral(&prelude, 2);
        let three = numeral(&prelude, 3);
        let five = numeral(&prelude, 5);
        let six = numeral(&prelude, 6);
        let zero = numeral(&prelude, 0);

        assert_def_eq(
            &elaborator,
            &context,
            binary(prelude.addition(), two.clone(), three.clone()),
            five.clone(),
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(prelude.multiplication(), two.clone(), three.clone()),
            six,
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(prelude.subtraction(), two, three.clone()),
            zero,
        );
        assert_def_eq(
            &elaborator,
            &context,
            binary(prelude.subtraction(), five, three),
            numeral(&prelude, 2),
        );
    }

    #[test]
    fn non_structural_legacy_shortcuts_are_not_kernel_conversion() {
        let (elaborator, prelude) = fixture();
        let nat = prelude.nat_type();
        let context = TermContext::new().with_bound(nat);
        let neutral = CoreTerm::Bound(0);
        let zero = CoreTerm::Constant(prelude.zero());

        // The legacy evaluator also rewrites these open terms. Those shortcuts
        // overlap the structural rules and are not substitution-stable, so the
        // HOL compatibility layer must discharge them with checked lemmas.
        for operation in [prelude.addition(), prelude.multiplication()] {
            assert!(!definitionally_equal(
                elaborator.types(),
                elaborator.constants(),
                &context,
                &binary(operation, neutral.clone(), zero.clone()),
                &if operation == prelude.addition() {
                    neutral.clone()
                } else {
                    zero.clone()
                },
            )
            .expect("well-typed non-conversion"));
        }
    }

    #[test]
    fn saturated_first_order_use_is_not_tainted_by_higher_order_helper() {
        let (mut elaborator, prelude) = fixture();
        let nat = prelude.nat_type();
        let zero = CoreTerm::Constant(prelude.zero());
        let statement = binary(prelude.less_equal(), zero.clone(), CoreTerm::Bound(0));
        let (_, receipt) = elaborator
            .declare_theorem_with_parameters(
                "compat.zero_le",
                Vec::new(),
                vec![nat.clone()],
                statement,
                HolDraftProof::TruthIntro,
            )
            .expect("zero <= n computes to truth");
        assert_eq!(
            receipt.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert!(ReceiptPolicy::new(TeachingProfile::FirstOrderInductive)
            .check(&receipt)
            .is_empty());

        let predicate = CoreTerm::apply(CoreTerm::Constant(prelude.less_equal()), zero);
        let higher_order_statement = CoreTerm::equality(
            CoreType::arrow(nat, CoreType::Prop),
            predicate.clone(),
            predicate.clone(),
        );
        let (_, higher_order) = elaborator
            .declare_theorem(
                "compat.le_predicate_refl",
                Vec::new(),
                higher_order_statement,
                HolDraftProof::EqualityRefl(predicate),
            )
            .expect("higher-order use is still valid HOL");
        assert_eq!(
            higher_order.proof().required_fragment(),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn set_is_the_distinguished_first_order_wrapper() {
        let (elaborator, prelude) = fixture();
        let set_nat = elaborator
            .types()
            .legacy_set_type(prelude.nat_type())
            .expect("Set Nat");
        assert_eq!(
            set_nat,
            CoreType::constructor(prelude.set_constructor(), vec![prelude.nat_type()])
        );
        assert_eq!(
            elaborator.types().first_order_status(&set_nat),
            Ok(crate::hol::FirstOrderStatus::FirstOrder)
        );

        let mut raw_types = TypeSignature::new();
        raw_types
            .declare_legacy_set("Set")
            .expect("independent Set signature");
        assert!(raw_types.legacy_set_type(CoreType::Prop).is_err());
    }
}
