//! Checked core declarations behind the legacy `Nat` and `Set` syntax.
//!
//! The compatibility parser is deliberately not involved here. Installing the
//! prelude into an empty [`SpikeElaborator`] creates the stable IDs that later
//! AST lowering uses for builtin syntax. Every recursive operation is admitted
//! by the ordinary structural-recursion checker; this module does not install
//! an extra evaluator or a trusted arithmetic oracle.

use super::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{shift_under_new_binder, ConstantId, CoreTerm};
use super::theorems::TheoremId;
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
    addition_zero_right: TheoremId,
    addition_successor_right: TheoremId,
    addition_left_commute: TheoremId,
    multiplication_zero_right: TheoremId,
    multiplication_successor_right: TheoremId,
    subtraction_zero_left: TheoremId,
    subtraction_successor_successor: TheoremId,
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
        staged.mark_first_order_implementation_constant(less_equal_tail);
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

        // The legacy evaluator also simplifies on the non-structural side of
        // arithmetic operations. Those equations cannot be kernel conversion:
        // overlapping open reductions are not substitution-stable. Install
        // ordinary checked induction theorems instead so compatibility
        // conversion can elaborate each shortcut to explicit equality
        // elimination.
        let addition_zero_right = declare_addition_zero_right(
            &mut staged,
            nat,
            nat_type.clone(),
            zero,
            successor,
            addition,
        )?;
        let addition_successor_right = declare_addition_successor_right(
            &mut staged,
            nat,
            nat_type.clone(),
            zero,
            successor,
            addition,
        )?;
        let addition_left_commute = declare_addition_left_commute(
            &mut staged,
            nat,
            nat_type.clone(),
            zero,
            successor,
            addition,
            addition_successor_right,
        )?;
        let multiplication_zero_right = declare_multiplication_zero_right(
            &mut staged,
            nat,
            nat_type.clone(),
            zero,
            multiplication,
        )?;
        let multiplication_successor_right = declare_multiplication_successor_right(
            &mut staged,
            nat,
            nat_type.clone(),
            zero,
            successor,
            addition,
            multiplication,
            addition_left_commute,
        )?;
        let subtraction_zero_left = declare_subtraction_zero_left(
            &mut staged,
            nat,
            nat_type.clone(),
            zero,
            subtraction,
            predecessor,
        )?;
        let subtraction_successor_successor = declare_subtraction_successor_successor(
            &mut staged,
            nat,
            nat_type.clone(),
            successor,
            subtraction,
            predecessor,
        )?;

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
            addition_zero_right,
            addition_successor_right,
            addition_left_commute,
            multiplication_zero_right,
            multiplication_successor_right,
            subtraction_zero_left,
            subtraction_successor_successor,
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

    pub fn addition_zero_right(&self) -> TheoremId {
        self.addition_zero_right
    }

    pub fn addition_successor_right(&self) -> TheoremId {
        self.addition_successor_right
    }

    pub fn multiplication_zero_right(&self) -> TheoremId {
        self.multiplication_zero_right
    }

    pub fn multiplication_successor_right(&self) -> TheoremId {
        self.multiplication_successor_right
    }

    pub fn subtraction_zero_left(&self) -> TheoremId {
        self.subtraction_zero_left
    }

    pub fn subtraction_successor_successor(&self) -> TheoremId {
        self.subtraction_successor_successor
    }
}

fn apply2(function: ConstantId, left: CoreTerm, right: CoreTerm) -> CoreTerm {
    CoreTerm::apply(CoreTerm::apply(CoreTerm::Constant(function), left), right)
}

fn successor(successor: ConstantId, term: CoreTerm) -> CoreTerm {
    CoreTerm::apply(CoreTerm::Constant(successor), term)
}

fn equality(nat: &CoreType, left: CoreTerm, right: CoreTerm) -> CoreTerm {
    CoreTerm::equality(nat.clone(), left, right)
}

fn theorem_reference(theorem: TheoremId, term_arguments: Vec<CoreTerm>) -> HolDraftProof {
    HolDraftProof::TheoremRef {
        theorem,
        type_arguments: Vec::new(),
        term_arguments,
    }
}

fn unary_congruence(
    function: ConstantId,
    nat: &CoreType,
    left: CoreTerm,
    proof_equality: HolDraftProof,
) -> Result<HolDraftProof, SpikeError> {
    let shifted_left = shift_under_new_binder(&left)?;
    let applied_left = CoreTerm::apply(CoreTerm::Constant(function), left);
    Ok(HolDraftProof::EqualityElim {
        proof_equality: Box::new(proof_equality),
        motive: CoreTerm::lambda(
            nat.clone(),
            equality(
                nat,
                CoreTerm::apply(CoreTerm::Constant(function), shifted_left),
                CoreTerm::apply(CoreTerm::Constant(function), CoreTerm::Bound(0)),
            ),
        ),
        proof_left: Box::new(HolDraftProof::EqualityRefl(applied_left)),
    })
}

fn binary_right_congruence(
    function: ConstantId,
    nat: &CoreType,
    fixed: CoreTerm,
    left: CoreTerm,
    proof_equality: HolDraftProof,
) -> Result<HolDraftProof, SpikeError> {
    let shifted_fixed = shift_under_new_binder(&fixed)?;
    let shifted_left = shift_under_new_binder(&left)?;
    let applied_left = apply2(function, fixed, left);
    Ok(HolDraftProof::EqualityElim {
        proof_equality: Box::new(proof_equality),
        motive: CoreTerm::lambda(
            nat.clone(),
            equality(
                nat,
                apply2(function, shifted_fixed.clone(), shifted_left),
                apply2(function, shifted_fixed, CoreTerm::Bound(0)),
            ),
        ),
        proof_left: Box::new(HolDraftProof::EqualityRefl(applied_left)),
    })
}

fn symmetry(
    nat: &CoreType,
    left: CoreTerm,
    proof_equality: HolDraftProof,
) -> Result<HolDraftProof, SpikeError> {
    let shifted_left = shift_under_new_binder(&left)?;
    Ok(HolDraftProof::EqualityElim {
        proof_equality: Box::new(proof_equality),
        motive: CoreTerm::lambda(nat.clone(), equality(nat, CoreTerm::Bound(0), shifted_left)),
        proof_left: Box::new(HolDraftProof::EqualityRefl(left)),
    })
}

fn transitivity(
    nat: &CoreType,
    left: CoreTerm,
    proof_left: HolDraftProof,
    proof_right: HolDraftProof,
) -> Result<HolDraftProof, SpikeError> {
    let shifted_left = shift_under_new_binder(&left)?;
    Ok(HolDraftProof::EqualityElim {
        proof_equality: Box::new(proof_right),
        motive: CoreTerm::lambda(nat.clone(), equality(nat, shifted_left, CoreTerm::Bound(0))),
        proof_left: Box::new(proof_left),
    })
}

fn declare_addition_zero_right(
    elaborator: &mut SpikeElaborator,
    datatype: TypeConstructorId,
    nat: CoreType,
    zero: ConstantId,
    successor_id: ConstantId,
    addition: ConstantId,
) -> Result<TheoremId, SpikeError> {
    let zero_term = CoreTerm::Constant(zero);
    let statement = equality(
        &nat,
        apply2(addition, CoreTerm::Bound(0), zero_term.clone()),
        CoreTerm::Bound(0),
    );
    let motive = CoreTerm::lambda(
        nat.clone(),
        equality(
            &nat,
            apply2(addition, CoreTerm::Bound(0), zero_term.clone()),
            CoreTerm::Bound(0),
        ),
    );
    let step_left = apply2(addition, CoreTerm::Bound(0), zero_term.clone());
    let proof = HolDraftProof::Induction {
        datatype,
        type_arguments: Vec::new(),
        motive,
        scrutinee: CoreTerm::Bound(0),
        cases: vec![
            HolDraftProof::EqualityRefl(zero_term),
            unary_congruence(successor_id, &nat, step_left, HolDraftProof::Hypothesis(0))?,
        ],
    };
    elaborator
        .declare_theorem_with_parameters(
            "@compat.add_zero_right",
            Vec::new(),
            vec![nat],
            statement,
            proof,
        )
        .map(|(theorem, _)| theorem)
}

fn declare_addition_successor_right(
    elaborator: &mut SpikeElaborator,
    datatype: TypeConstructorId,
    nat: CoreType,
    _zero: ConstantId,
    successor_id: ConstantId,
    addition: ConstantId,
) -> Result<TheoremId, SpikeError> {
    let n = CoreTerm::Bound(1);
    let m = CoreTerm::Bound(0);
    let statement = equality(
        &nat,
        apply2(addition, n.clone(), successor(successor_id, m.clone())),
        successor(successor_id, apply2(addition, n.clone(), m.clone())),
    );
    // Under the motive binder: k = 0, m = 1; the original n is ignored.
    let k = CoreTerm::Bound(0);
    let shifted_m = CoreTerm::Bound(1);
    let motive = CoreTerm::lambda(
        nat.clone(),
        equality(
            &nat,
            apply2(
                addition,
                k.clone(),
                successor(successor_id, shifted_m.clone()),
            ),
            successor(successor_id, apply2(addition, k.clone(), shifted_m.clone())),
        ),
    );
    // In the successor case: k = 0, m = 1.
    let step_left = apply2(
        addition,
        CoreTerm::Bound(0),
        successor(successor_id, CoreTerm::Bound(1)),
    );
    let proof = HolDraftProof::Induction {
        datatype,
        type_arguments: Vec::new(),
        motive,
        scrutinee: n,
        cases: vec![
            HolDraftProof::EqualityRefl(successor(successor_id, m)),
            unary_congruence(successor_id, &nat, step_left, HolDraftProof::Hypothesis(0))?,
        ],
    };
    elaborator
        .declare_theorem_with_parameters(
            "@compat.add_succ_right",
            Vec::new(),
            vec![nat.clone(), nat],
            statement,
            proof,
        )
        .map(|(theorem, _)| theorem)
}

#[allow(clippy::too_many_arguments)]
fn declare_addition_left_commute(
    elaborator: &mut SpikeElaborator,
    datatype: TypeConstructorId,
    nat: CoreType,
    _zero: ConstantId,
    successor_id: ConstantId,
    addition: ConstantId,
    addition_successor_right: TheoremId,
) -> Result<TheoremId, SpikeError> {
    let a = CoreTerm::Bound(2);
    let b = CoreTerm::Bound(1);
    let c = CoreTerm::Bound(0);
    let statement = equality(
        &nat,
        apply2(addition, a.clone(), apply2(addition, b.clone(), c.clone())),
        apply2(addition, b.clone(), apply2(addition, a.clone(), c.clone())),
    );
    // Under the motive binder: k = 0, c = 1, b = 2.
    let k = CoreTerm::Bound(0);
    let shifted_c = CoreTerm::Bound(1);
    let shifted_b = CoreTerm::Bound(2);
    let motive = CoreTerm::lambda(
        nat.clone(),
        equality(
            &nat,
            apply2(
                addition,
                k.clone(),
                apply2(addition, shifted_b.clone(), shifted_c.clone()),
            ),
            apply2(
                addition,
                shifted_b.clone(),
                apply2(addition, k.clone(), shifted_c.clone()),
            ),
        ),
    );
    // In the successor case: k = 0, c = 1, b = 2.
    let k = CoreTerm::Bound(0);
    let c = CoreTerm::Bound(1);
    let b = CoreTerm::Bound(2);
    let ih_left = apply2(addition, k.clone(), apply2(addition, b.clone(), c.clone()));
    let lifted_ih = unary_congruence(
        successor_id,
        &nat,
        ih_left.clone(),
        HolDraftProof::Hypothesis(0),
    )?;
    let inner = apply2(addition, k, c);
    let right_equation =
        theorem_reference(addition_successor_right, vec![b.clone(), inner.clone()]);
    let reversed_right = symmetry(
        &nat,
        apply2(addition, b.clone(), successor(successor_id, inner.clone())),
        right_equation,
    )?;
    let step = transitivity(
        &nat,
        successor(successor_id, ih_left),
        lifted_ih,
        reversed_right,
    )?;
    let proof = HolDraftProof::Induction {
        datatype,
        type_arguments: Vec::new(),
        motive,
        scrutinee: a,
        cases: vec![
            HolDraftProof::EqualityRefl(apply2(addition, CoreTerm::Bound(1), CoreTerm::Bound(0))),
            step,
        ],
    };
    elaborator
        .declare_theorem_with_parameters(
            "@compat.add_left_comm",
            Vec::new(),
            vec![nat.clone(), nat.clone(), nat],
            statement,
            proof,
        )
        .map(|(theorem, _)| theorem)
}

fn declare_multiplication_zero_right(
    elaborator: &mut SpikeElaborator,
    datatype: TypeConstructorId,
    nat: CoreType,
    zero: ConstantId,
    multiplication: ConstantId,
) -> Result<TheoremId, SpikeError> {
    let zero_term = CoreTerm::Constant(zero);
    let statement = equality(
        &nat,
        apply2(multiplication, CoreTerm::Bound(0), zero_term.clone()),
        zero_term.clone(),
    );
    let motive = CoreTerm::lambda(
        nat.clone(),
        equality(
            &nat,
            apply2(multiplication, CoreTerm::Bound(0), zero_term.clone()),
            zero_term.clone(),
        ),
    );
    let proof = HolDraftProof::Induction {
        datatype,
        type_arguments: Vec::new(),
        motive,
        scrutinee: CoreTerm::Bound(0),
        cases: vec![
            HolDraftProof::EqualityRefl(zero_term),
            HolDraftProof::Hypothesis(0),
        ],
    };
    elaborator
        .declare_theorem_with_parameters(
            "@compat.mul_zero_right",
            Vec::new(),
            vec![nat],
            statement,
            proof,
        )
        .map(|(theorem, _)| theorem)
}

#[allow(clippy::too_many_arguments)]
fn declare_multiplication_successor_right(
    elaborator: &mut SpikeElaborator,
    datatype: TypeConstructorId,
    nat: CoreType,
    zero: ConstantId,
    successor_id: ConstantId,
    addition: ConstantId,
    multiplication: ConstantId,
    addition_left_commute: TheoremId,
) -> Result<TheoremId, SpikeError> {
    let n = CoreTerm::Bound(1);
    let m = CoreTerm::Bound(0);
    let statement = equality(
        &nat,
        apply2(
            multiplication,
            n.clone(),
            successor(successor_id, m.clone()),
        ),
        apply2(
            addition,
            n.clone(),
            apply2(multiplication, n.clone(), m.clone()),
        ),
    );
    // Under the motive binder: k = 0, m = 1.
    let k = CoreTerm::Bound(0);
    let shifted_m = CoreTerm::Bound(1);
    let motive = CoreTerm::lambda(
        nat.clone(),
        equality(
            &nat,
            apply2(
                multiplication,
                k.clone(),
                successor(successor_id, shifted_m.clone()),
            ),
            apply2(
                addition,
                k.clone(),
                apply2(multiplication, k.clone(), shifted_m.clone()),
            ),
        ),
    );

    // In the successor case: k = 0, m = 1.
    let k = CoreTerm::Bound(0);
    let m = CoreTerm::Bound(1);
    let successor_m = successor(successor_id, m.clone());
    let ih_left = apply2(multiplication, k.clone(), successor_m);
    let lifted_add = binary_right_congruence(
        addition,
        &nat,
        m.clone(),
        ih_left.clone(),
        HolDraftProof::Hypothesis(0),
    )?;
    let lifted_ih = unary_congruence(
        successor_id,
        &nat,
        apply2(addition, m.clone(), ih_left.clone()),
        lifted_add,
    )?;
    let product_k_m = apply2(multiplication, k.clone(), m.clone());
    let commute = theorem_reference(
        addition_left_commute,
        vec![m.clone(), k.clone(), product_k_m.clone()],
    );
    let lifted_commute = unary_congruence(
        successor_id,
        &nat,
        apply2(
            addition,
            m.clone(),
            apply2(addition, k.clone(), product_k_m),
        ),
        commute,
    )?;
    let step = transitivity(
        &nat,
        successor(successor_id, apply2(addition, m, ih_left)),
        lifted_ih,
        lifted_commute,
    )?;
    let zero_term = CoreTerm::Constant(zero);
    let proof = HolDraftProof::Induction {
        datatype,
        type_arguments: Vec::new(),
        motive,
        scrutinee: n,
        cases: vec![HolDraftProof::EqualityRefl(zero_term), step],
    };
    elaborator
        .declare_theorem_with_parameters(
            "@compat.mul_succ_right",
            Vec::new(),
            vec![nat.clone(), nat],
            statement,
            proof,
        )
        .map(|(theorem, _)| theorem)
}

fn declare_subtraction_zero_left(
    elaborator: &mut SpikeElaborator,
    datatype: TypeConstructorId,
    nat: CoreType,
    zero: ConstantId,
    subtraction: ConstantId,
    predecessor: ConstantId,
) -> Result<TheoremId, SpikeError> {
    let zero_term = CoreTerm::Constant(zero);
    let statement = equality(
        &nat,
        apply2(subtraction, zero_term.clone(), CoreTerm::Bound(0)),
        zero_term.clone(),
    );
    let motive = CoreTerm::lambda(
        nat.clone(),
        equality(
            &nat,
            apply2(subtraction, zero_term.clone(), CoreTerm::Bound(0)),
            zero_term.clone(),
        ),
    );
    let step_left = apply2(subtraction, zero_term.clone(), CoreTerm::Bound(0));
    let proof = HolDraftProof::Induction {
        datatype,
        type_arguments: Vec::new(),
        motive,
        scrutinee: CoreTerm::Bound(0),
        cases: vec![
            HolDraftProof::EqualityRefl(zero_term),
            unary_congruence(predecessor, &nat, step_left, HolDraftProof::Hypothesis(0))?,
        ],
    };
    elaborator
        .declare_theorem_with_parameters(
            "@compat.sub_zero_left",
            Vec::new(),
            vec![nat],
            statement,
            proof,
        )
        .map(|(theorem, _)| theorem)
}

fn declare_subtraction_successor_successor(
    elaborator: &mut SpikeElaborator,
    datatype: TypeConstructorId,
    nat: CoreType,
    successor_id: ConstantId,
    subtraction: ConstantId,
    predecessor: ConstantId,
) -> Result<TheoremId, SpikeError> {
    let n = CoreTerm::Bound(1);
    let m = CoreTerm::Bound(0);
    let statement = equality(
        &nat,
        apply2(
            subtraction,
            successor(successor_id, n.clone()),
            successor(successor_id, m.clone()),
        ),
        apply2(subtraction, n.clone(), m.clone()),
    );
    // Under the motive binder: k = 0, n = 2; original m = 1 is ignored.
    let k = CoreTerm::Bound(0);
    let shifted_n = CoreTerm::Bound(2);
    let motive = CoreTerm::lambda(
        nat.clone(),
        equality(
            &nat,
            apply2(
                subtraction,
                successor(successor_id, shifted_n.clone()),
                successor(successor_id, k.clone()),
            ),
            apply2(subtraction, shifted_n, k),
        ),
    );
    // In the successor case: k = 0, n = 2.
    let k = CoreTerm::Bound(0);
    let n_in_case = CoreTerm::Bound(2);
    let ih_left = CoreTerm::apply(
        CoreTerm::Constant(predecessor),
        apply2(subtraction, successor(successor_id, n_in_case), k),
    );
    let proof = HolDraftProof::Induction {
        datatype,
        type_arguments: Vec::new(),
        motive,
        scrutinee: m,
        cases: vec![
            HolDraftProof::EqualityRefl(n),
            unary_congruence(predecessor, &nat, ih_left, HolDraftProof::Hypothesis(0))?,
        ],
    };
    elaborator
        .declare_theorem_with_parameters(
            "@compat.sub_succ_succ",
            Vec::new(),
            vec![nat.clone(), nat],
            statement,
            proof,
        )
        .map(|(theorem, _)| theorem)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{
        classify_statement, EvidenceStatus, ProofFeature, StatementFragment, TeachingProfile,
    };
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
    fn secondary_arithmetic_equations_are_checked_induction_theorems() {
        let (elaborator, prelude) = fixture();
        for theorem in [
            prelude.addition_zero_right(),
            prelude.addition_successor_right(),
            prelude.multiplication_zero_right(),
            prelude.multiplication_successor_right(),
            prelude.subtraction_zero_left(),
            prelude.subtraction_successor_successor(),
        ] {
            let receipt = elaborator
                .theorem_receipt(theorem)
                .expect("compatibility theorem receipt");
            assert_eq!(receipt.status(), EvidenceStatus::Checked);
            assert!(receipt.proof().axiom_dependencies().is_empty());
            assert!(receipt
                .proof()
                .transitive_features()
                .contains(&ProofFeature::Induction));
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

        let open_context = TermContext::new().with_bound(nat.clone());
        let open_successor_order = CoreTerm::implies(
            binary(
                prelude.less_equal(),
                successor(&prelude, CoreTerm::Bound(0)),
                CoreTerm::Bound(0),
            ),
            CoreTerm::Falsity,
        );
        assert_eq!(
            classify_statement(
                elaborator.types(),
                elaborator.constants(),
                &open_context,
                elaborator.fragment_metadata(),
                &open_successor_order,
            )
            .expect("classify open saturated order relation"),
            StatementFragment::FirstOrderInductive
        );

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
