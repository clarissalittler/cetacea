//! Structurally checked finite row, column, and matrix sums.
//!
//! For `w : A -> B -> Nat`, the argument order is `row_sum(w, a, ys)`,
//! `column_sum(w, xs, b)`, and `rows_total(w, xs, ys)` or
//! `columns_total(w, xs, ys)`. Lists retain multiplicity. The eight equations
//! are checked computation laws; equality of the two totals for arbitrary
//! lists is proved in `std/hol/double_counting.ctea` through the source package
//! `std/hol/matrix@1`.
use super::fragments::DeclarationReceipt;
use super::library::ListLibrary;
use super::proofs::HolDraftProof;
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{ConstantId, CoreTerm};
use super::theorems::TheoremId;
use super::types::{CoreType, TypeParameter};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixLibrary {
    pub equations: Vec<MatrixEquation>,
    pub row_parameter: TypeParameter,
    pub column_parameter: TypeParameter,
    pub natural_type: CoreType,
    pub row_sum: ConstantId,
    pub column_sum: ConstantId,
    pub rows_total: ConstantId,
    pub columns_total: ConstantId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatrixEquation {
    pub name: String,
    pub theorem: TheoremId,
    pub receipt: DeclarationReceipt,
}

fn apply(function: CoreTerm, args: impl IntoIterator<Item = CoreTerm>) -> CoreTerm {
    args.into_iter().fold(function, CoreTerm::apply)
}

impl MatrixLibrary {
    pub const EXPORTS: [&'static str; 4] = ["row_sum", "column_sum", "rows_total", "columns_total"];

    pub fn constants(&self) -> [ConstantId; 4] {
        [
            self.row_sum,
            self.column_sum,
            self.rows_total,
            self.columns_total,
        ]
    }

    pub fn install_named(
        core: &mut SpikeElaborator,
        lists: &ListLibrary,
        natural_type: CoreType,
        zero: ConstantId,
        addition: ConstantId,
        namespace: &str,
    ) -> Result<Self, SpikeError> {
        let mut staged = core.clone();
        let row_parameter = TypeParameter::any(200);
        let column_parameter = TypeParameter::any(201);
        let row = CoreType::Parameter(row_parameter);
        let column = CoreType::Parameter(column_parameter);
        let weight = CoreType::arrow(
            row.clone(),
            CoreType::arrow(column.clone(), natural_type.clone()),
        );
        let layout = StructuralArmLayout::new(2, 1, 2);
        let fixed = |index| {
            layout
                .fixed_parameter(index)
                .expect("fixed matrix argument")
        };
        let head = || layout.field(0).expect("list head");
        let tail = || layout.recursive_result(0).expect("sum of tail");
        let add = |left, right| apply(CoreTerm::Constant(addition), [left, right]);
        let mut installed = Vec::new();
        for (index, name) in Self::EXPORTS.iter().enumerate() {
            let (element, fixed_type, recursive_argument_index, contribution) = match index {
                0 => (
                    column.clone(),
                    row.clone(),
                    2,
                    apply(fixed(0), [fixed(1), head()]),
                ),
                1 => (
                    row.clone(),
                    column.clone(),
                    1,
                    apply(fixed(0), [head(), fixed(1)]),
                ),
                2 => (
                    row.clone(),
                    lists.list_type(column.clone()),
                    1,
                    apply(
                        CoreTerm::instantiate_constant(
                            installed[0],
                            vec![row.clone(), column.clone()],
                        ),
                        [fixed(0), head(), fixed(1)],
                    ),
                ),
                3 => (
                    column.clone(),
                    lists.list_type(row.clone()),
                    2,
                    apply(
                        CoreTerm::instantiate_constant(
                            installed[1],
                            vec![row.clone(), column.clone()],
                        ),
                        [fixed(0), fixed(1), head()],
                    ),
                ),
                _ => unreachable!(),
            };
            let constant = staged.declare_structural_definition(StructuralDefinitionSpec {
                name: if namespace.is_empty() {
                    name.to_string()
                } else {
                    format!("{namespace}.{name}")
                },
                type_parameters: vec![row_parameter, column_parameter],
                datatype: lists.datatype,
                datatype_arguments: vec![element],
                fixed_parameter_types: vec![weight.clone(), fixed_type],
                recursive_argument_index,
                result_type: natural_type.clone(),
                arms: vec![
                    StructuralArmSpec::new(lists.nil, CoreTerm::Constant(zero)),
                    StructuralArmSpec::new(lists.cons, add(contribution, tail())),
                ],
            })?;
            installed.push(constant);
        }
        let mut library = Self {
            equations: Vec::new(),
            row_parameter,
            column_parameter,
            natural_type,
            row_sum: installed[0],
            column_sum: installed[1],
            rows_total: installed[2],
            columns_total: installed[3],
        };
        library.equations =
            library.declare_equations(&mut staged, lists, zero, addition, namespace)?;
        *core = staged;
        Ok(library)
    }

    fn declare_equations(
        &self,
        core: &mut SpikeElaborator,
        lists: &ListLibrary,
        zero: ConstantId,
        addition: ConstantId,
        namespace: &str,
    ) -> Result<Vec<MatrixEquation>, SpikeError> {
        let a = CoreType::Parameter(self.row_parameter);
        let b = CoreType::Parameter(self.column_parameter);
        let la = lists.list_type(a.clone());
        let lb = lists.list_type(b.clone());
        let w = CoreType::arrow(
            a.clone(),
            CoreType::arrow(b.clone(), self.natural_type.clone()),
        );
        let bound = CoreTerm::Bound;
        let call = |index, weight, first, second| {
            self.sum_term(index, a.clone(), b.clone(), weight, first, second)
        };
        let add = |x, y| apply(CoreTerm::Constant(addition), [x, y]);
        let rows = [
            (
                "row_sum_nil",
                vec![w.clone(), a.clone()],
                call(0, bound(1), bound(0), lists.nil_term(b.clone())),
                CoreTerm::Constant(zero),
            ),
            (
                "row_sum_cons",
                vec![w.clone(), a.clone(), b.clone(), lb.clone()],
                call(
                    0,
                    bound(3),
                    bound(2),
                    lists.cons_term(b.clone(), bound(1), bound(0)),
                ),
                add(
                    apply(bound(3), [bound(2), bound(1)]),
                    call(0, bound(3), bound(2), bound(0)),
                ),
            ),
            (
                "column_sum_nil",
                vec![w.clone(), b.clone()],
                call(1, bound(1), lists.nil_term(a.clone()), bound(0)),
                CoreTerm::Constant(zero),
            ),
            (
                "column_sum_cons",
                vec![w.clone(), a.clone(), la.clone(), b.clone()],
                call(
                    1,
                    bound(3),
                    lists.cons_term(a.clone(), bound(2), bound(1)),
                    bound(0),
                ),
                add(
                    apply(bound(3), [bound(2), bound(0)]),
                    call(1, bound(3), bound(1), bound(0)),
                ),
            ),
            (
                "rows_total_nil",
                vec![w.clone(), lb.clone()],
                call(2, bound(1), lists.nil_term(a.clone()), bound(0)),
                CoreTerm::Constant(zero),
            ),
            (
                "rows_total_cons",
                vec![w.clone(), a.clone(), la.clone(), lb.clone()],
                call(
                    2,
                    bound(3),
                    lists.cons_term(a.clone(), bound(2), bound(1)),
                    bound(0),
                ),
                add(
                    call(0, bound(3), bound(2), bound(0)),
                    call(2, bound(3), bound(1), bound(0)),
                ),
            ),
            (
                "columns_total_nil",
                vec![w.clone(), la.clone()],
                call(3, bound(1), bound(0), lists.nil_term(b.clone())),
                CoreTerm::Constant(zero),
            ),
            (
                "columns_total_cons",
                vec![w, la, b.clone(), lb],
                call(
                    3,
                    bound(3),
                    bound(2),
                    lists.cons_term(b.clone(), bound(1), bound(0)),
                ),
                add(
                    call(1, bound(3), bound(2), bound(1)),
                    call(3, bound(3), bound(2), bound(0)),
                ),
            ),
        ];
        rows.into_iter()
            .map(|(name, parameters, left, right)| {
                let qualified = if namespace.is_empty() {
                    name.to_string()
                } else {
                    format!("{namespace}.{name}")
                };
                let (theorem, receipt) = core.declare_theorem_with_parameters(
                    qualified,
                    vec![self.row_parameter, self.column_parameter],
                    parameters,
                    CoreTerm::equality(self.natural_type.clone(), left.clone(), right),
                    HolDraftProof::EqualityRefl(left),
                )?;
                Ok(MatrixEquation {
                    name: name.to_string(),
                    theorem,
                    receipt,
                })
            })
            .collect()
    }

    fn sum_term(
        &self,
        index: usize,
        row: CoreType,
        column: CoreType,
        weight: CoreTerm,
        first: CoreTerm,
        second: CoreTerm,
    ) -> CoreTerm {
        apply(
            CoreTerm::instantiate_constant(self.constants()[index], vec![row, column]),
            [weight, first, second],
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::terms::{normalize, TermContext};
    use crate::hol::{CompatibilityPrelude, ListLibraryNames, StatementFragment};

    fn setup() -> (SpikeElaborator, CompatibilityPrelude, ListLibrary) {
        let mut core = SpikeElaborator::new();
        let prelude = CompatibilityPrelude::install(&mut core).unwrap();
        let lists =
            ListLibrary::install_named(&mut core, &ListLibraryNames::under_namespace("L")).unwrap();
        (core, prelude, lists)
    }

    fn numeral(prelude: &CompatibilityPrelude, n: usize) -> CoreTerm {
        (0..n).fold(CoreTerm::Constant(prelude.zero()), |term, _| {
            CoreTerm::apply(CoreTerm::Constant(prelude.successor()), term)
        })
    }

    #[test]
    fn asymmetric_rectangular_matrix_checks_both_orders_and_empty_dimensions() {
        let (mut core, prelude, lists) = setup();
        let nat = prelude.nat_type();
        let matrix = MatrixLibrary::install_named(
            &mut core,
            &lists,
            nat.clone(),
            prelude.zero(),
            prelude.addition(),
            "M",
        )
        .unwrap();
        let list = |values: &[usize]| {
            values
                .iter()
                .rev()
                .fold(lists.nil_term(nat.clone()), |tail, n| {
                    lists.cons_term(nat.clone(), numeral(&prelude, *n), tail)
                })
        };
        // w(a,b)=10*a+b; rows [1,2], columns [3,4,5].
        let weight = CoreTerm::lambda(
            nat.clone(),
            CoreTerm::lambda(
                nat.clone(),
                apply(
                    CoreTerm::Constant(prelude.addition()),
                    [
                        apply(
                            CoreTerm::Constant(prelude.multiplication()),
                            [CoreTerm::Bound(1), numeral(&prelude, 10)],
                        ),
                        CoreTerm::Bound(0),
                    ],
                ),
            ),
        );
        let rows = list(&[1, 2]);
        let columns = list(&[3, 4, 5]);
        for (index, first, second, expected) in [
            (0, numeral(&prelude, 1), columns.clone(), 42),
            (1, rows.clone(), numeral(&prelude, 3), 36),
            (2, rows.clone(), columns.clone(), 114),
            (3, rows.clone(), columns.clone(), 114),
            (0, numeral(&prelude, 1), list(&[]), 0),
            (1, list(&[]), numeral(&prelude, 3), 0),
            (2, rows.clone(), list(&[]), 0),
            (3, list(&[]), columns.clone(), 0),
            (2, list(&[1, 1]), list(&[3]), 26),
        ] {
            let term = matrix.sum_term(
                index,
                nat.clone(),
                nat.clone(),
                weight.clone(),
                first,
                second,
            );
            assert_eq!(
                normalize(core.types(), core.constants(), &TermContext::new(), &term).unwrap(),
                numeral(&prelude, expected),
                "operator {index}"
            );
        }
        assert_eq!(matrix.equations.len(), 8);
        for equation in &matrix.equations {
            assert_eq!(
                equation.receipt.proof().required_fragment(),
                if equation.name.ends_with("_nil") {
                    StatementFragment::FirstOrderInductive
                } else {
                    StatementFragment::HigherOrder
                },
                "{}",
                equation.name
            );
            assert!(equation.receipt.proof().axiom_dependencies().is_empty());
            assert!(equation
                .receipt
                .proof()
                .incomplete_dependencies()
                .is_empty());
        }
    }

    #[test]
    fn distinct_index_types_reject_swapped_lists_and_false_totals() {
        let (mut core, prelude, lists) = setup();
        let matrix = MatrixLibrary::install_named(
            &mut core,
            &lists,
            prelude.nat_type(),
            prelude.zero(),
            prelude.addition(),
            "M",
        )
        .unwrap();
        let row = CoreType::constructor(core.declare_base_type("Row", true).unwrap(), vec![]);
        let column = CoreType::constructor(core.declare_base_type("Column", true).unwrap(), vec![]);
        let a = CoreTerm::Constant(core.declare_constant("a", row.clone()).unwrap());
        let b = CoreTerm::Constant(core.declare_constant("b", column.clone()).unwrap());
        let weight = CoreTerm::lambda(
            row.clone(),
            CoreTerm::lambda(column.clone(), numeral(&prelude, 2)),
        );
        let rows = lists.cons_term(row.clone(), a, lists.nil_term(row.clone()));
        let columns = lists.cons_term(column.clone(), b, lists.nil_term(column.clone()));
        for index in [2, 3] {
            let total = matrix.sum_term(
                index,
                row.clone(),
                column.clone(),
                weight.clone(),
                rows.clone(),
                columns.clone(),
            );
            let (_, receipt) = core
                .declare_theorem(
                    format!("total_{index}"),
                    vec![],
                    CoreTerm::equality(prelude.nat_type(), total.clone(), numeral(&prelude, 2)),
                    HolDraftProof::EqualityRefl(total.clone()),
                )
                .unwrap();
            assert!(receipt.proof().axiom_dependencies().is_empty());
            let before = core.clone();
            assert!(core
                .declare_theorem(
                    format!("wrong_{index}"),
                    vec![],
                    CoreTerm::equality(prelude.nat_type(), total.clone(), numeral(&prelude, 1)),
                    HolDraftProof::EqualityRefl(total),
                )
                .is_err());
            assert_eq!(core, before);
            let swapped = matrix.sum_term(
                index,
                row.clone(),
                column.clone(),
                weight.clone(),
                columns.clone(),
                rows.clone(),
            );
            assert!(crate::hol::terms::infer_type(
                core.types(),
                core.constants(),
                &TermContext::new(),
                &swapped
            )
            .is_err());
        }
    }

    #[test]
    fn matrix_install_rolls_back_late_equation_collisions_and_bad_arithmetic() {
        let (mut core, prelude, lists) = setup();
        core.declare_theorem(
            "M.columns_total_cons",
            vec![],
            CoreTerm::equality(
                prelude.nat_type(),
                numeral(&prelude, 0),
                numeral(&prelude, 0),
            ),
            HolDraftProof::EqualityRefl(numeral(&prelude, 0)),
        )
        .unwrap();
        let before = core.clone();
        assert!(MatrixLibrary::install_named(
            &mut core,
            &lists,
            prelude.nat_type(),
            prelude.zero(),
            prelude.addition(),
            "M"
        )
        .is_err());
        assert_eq!(core, before);
        assert!(MatrixLibrary::install_named(
            &mut core,
            &lists,
            prelude.nat_type(),
            prelude.zero(),
            prelude.successor(),
            "Other"
        )
        .is_err());
        assert_eq!(core, before);
    }
}
