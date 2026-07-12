//! Reusable checked HOL library packages.
//!
//! Unlike the historical spike builders, installers in this module are
//! transactional: a failed package installation leaves the elaborator exactly
//! as it was. The package handles also centralize canonical construction of
//! common library terms; the existing type checker still validates every use.

use super::inductive::{InductiveConstructorSpec, InductiveFieldType, InductiveSpec};
use super::recursion::{StructuralArmLayout, StructuralArmSpec, StructuralDefinitionSpec};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{ConstantId, CoreTerm};
use super::types::{CoreType, TypeConstructorId, TypeParameter};

/// Checked handles for the generic `List A` substrate.
///
/// The element parameter deliberately accepts any simple HOL type. A concrete
/// use at a first-order type is still classified at that least fragment, while
/// a use at `Prop` or an arrow remains honestly higher-order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ListLibrary {
    pub element_parameter: TypeParameter,
    pub datatype: TypeConstructorId,
    pub nil: ConstantId,
    pub cons: ConstantId,
    pub all: ConstantId,
    pub member: ConstantId,
    pub nodup: ConstantId,
    pub append: ConstantId,
}

/// Core names used by one installation of the list package.
///
/// Spike examples retain the historical unqualified names. Production-facing
/// registries use a reserved versioned namespace so an installed generic
/// package can coexist with legacy monomorphic declarations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListLibraryNames {
    pub datatype: String,
    pub nil: String,
    pub cons: String,
    pub all: String,
    pub member: String,
    pub nodup: String,
    pub append: String,
    pub length: String,
    pub append_nil_left: String,
    pub append_cons: String,
    pub length_nil: String,
    pub length_cons: String,
    pub member_nil: String,
    pub member_cons: String,
    pub nodup_nil: String,
    pub nodup_cons: String,
    pub all_nil: String,
    pub all_cons: String,
    pub append_nil_right: String,
    pub append_assoc: String,
    pub length_append: String,
    pub list_induction: String,
}

impl ListLibraryNames {
    pub fn canonical() -> Self {
        Self::under_namespace("")
    }

    pub fn under_namespace(namespace: &str) -> Self {
        let qualify = |leaf: &str| {
            if namespace.is_empty() {
                leaf.to_string()
            } else {
                format!("{namespace}.{leaf}")
            }
        };
        Self {
            datatype: qualify("List"),
            nil: qualify("nil"),
            cons: qualify("cons"),
            all: qualify("All"),
            member: qualify("Member"),
            nodup: qualify("Nodup"),
            append: qualify("append"),
            length: qualify("length"),
            append_nil_left: qualify("append_nil_left"),
            append_cons: qualify("append_cons"),
            length_nil: qualify("length_nil"),
            length_cons: qualify("length_cons"),
            member_nil: qualify("member_nil"),
            member_cons: qualify("member_cons"),
            nodup_nil: qualify("nodup_nil"),
            nodup_cons: qualify("nodup_cons"),
            all_nil: qualify("all_nil"),
            all_cons: qualify("all_cons"),
            append_nil_right: qualify("append_nil_right"),
            append_assoc: qualify("append_assoc"),
            length_append: qualify("length_append"),
            list_induction: qualify("list_induction"),
        }
    }
}

/// The Nat-specific extension of the generic list package.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListLength {
    pub constant: ConstantId,
    pub natural_type: CoreType,
    pub zero: ConstantId,
    pub successor: ConstantId,
}

impl ListLibrary {
    /// Install `List`, its constructors, and the `All`, `Member`, `Nodup`, and
    /// `append` structural definitions as one atomic package.
    pub fn install(elaborator: &mut SpikeElaborator) -> Result<Self, SpikeError> {
        Self::install_named(elaborator, &ListLibraryNames::canonical())
    }

    pub fn install_named(
        elaborator: &mut SpikeElaborator,
        names: &ListLibraryNames,
    ) -> Result<Self, SpikeError> {
        let mut staged = elaborator.clone();
        let library = Self::install_into(&mut staged, names)?;
        *elaborator = staged;
        Ok(library)
    }

    fn install_into(
        elaborator: &mut SpikeElaborator,
        names: &ListLibraryNames,
    ) -> Result<Self, SpikeError> {
        let element_parameter = TypeParameter::any(0);
        let element_type = CoreType::Parameter(element_parameter);
        let datatype = elaborator.declare_inductive(InductiveSpec::new(
            names.datatype.clone(),
            vec![element_parameter],
            vec![
                InductiveConstructorSpec::new(names.nil.clone(), Vec::new()),
                InductiveConstructorSpec::new(
                    names.cons.clone(),
                    vec![
                        InductiveFieldType::existing(element_type.clone()),
                        InductiveFieldType::Recursive,
                    ],
                ),
            ],
        ))?;
        let nil = elaborator.resolve_constant(&names.nil)?;
        let cons = elaborator.resolve_constant(&names.cons)?;
        let list_type = CoreType::constructor(datatype, vec![element_type.clone()]);

        let nil_with_fixed = StructuralArmLayout::new(0, 0, 1);
        let cons_with_fixed = StructuralArmLayout::new(2, 1, 1);
        let all = elaborator.declare_structural_definition(StructuralDefinitionSpec {
            name: names.all.clone(),
            type_parameters: vec![element_parameter],
            datatype,
            datatype_arguments: vec![element_type.clone()],
            fixed_parameter_types: vec![CoreType::arrow(element_type.clone(), CoreType::Prop)],
            recursive_argument_index: 1,
            result_type: CoreType::Prop,
            arms: vec![
                StructuralArmSpec::new(nil, CoreTerm::Truth),
                StructuralArmSpec::new(
                    cons,
                    CoreTerm::and(
                        CoreTerm::apply(
                            cons_with_fixed
                                .fixed_parameter(0)
                                .expect("All predicate binder"),
                            cons_with_fixed.field(0).expect("All head binder"),
                        ),
                        cons_with_fixed
                            .recursive_result(0)
                            .expect("All recursive result"),
                    ),
                ),
            ],
        })?;

        let member = elaborator.declare_structural_definition(StructuralDefinitionSpec {
            name: names.member.clone(),
            type_parameters: vec![element_parameter],
            datatype,
            datatype_arguments: vec![element_type.clone()],
            fixed_parameter_types: vec![element_type.clone()],
            recursive_argument_index: 1,
            result_type: CoreType::Prop,
            arms: vec![
                StructuralArmSpec::new(nil, CoreTerm::Falsity),
                StructuralArmSpec::new(
                    cons,
                    CoreTerm::or(
                        CoreTerm::equality(
                            element_type.clone(),
                            cons_with_fixed
                                .fixed_parameter(0)
                                .expect("Member needle binder"),
                            cons_with_fixed.field(0).expect("Member head binder"),
                        ),
                        cons_with_fixed
                            .recursive_result(0)
                            .expect("Member recursive result"),
                    ),
                ),
            ],
        })?;

        let cons_without_fixed = StructuralArmLayout::new(2, 1, 0);
        let member_of_tail = CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(member, vec![element_type.clone()]),
                cons_without_fixed.field(0).expect("Nodup head binder"),
            ),
            cons_without_fixed.field(1).expect("Nodup tail binder"),
        );
        let nodup = elaborator.declare_structural_definition(StructuralDefinitionSpec {
            name: names.nodup.clone(),
            type_parameters: vec![element_parameter],
            datatype,
            datatype_arguments: vec![element_type.clone()],
            fixed_parameter_types: Vec::new(),
            recursive_argument_index: 0,
            result_type: CoreType::Prop,
            arms: vec![
                StructuralArmSpec::new(nil, CoreTerm::Truth),
                StructuralArmSpec::new(
                    cons,
                    CoreTerm::and(
                        CoreTerm::implies(member_of_tail, CoreTerm::Falsity),
                        cons_without_fixed
                            .recursive_result(0)
                            .expect("Nodup recursive result"),
                    ),
                ),
            ],
        })?;

        let append = elaborator.declare_structural_definition(StructuralDefinitionSpec {
            name: names.append.clone(),
            type_parameters: vec![element_parameter],
            datatype,
            datatype_arguments: vec![element_type],
            fixed_parameter_types: vec![list_type.clone()],
            recursive_argument_index: 0,
            result_type: list_type,
            arms: vec![
                StructuralArmSpec::new(
                    nil,
                    nil_with_fixed
                        .fixed_parameter(0)
                        .expect("append right-list binder"),
                ),
                StructuralArmSpec::new(
                    cons,
                    CoreTerm::apply(
                        CoreTerm::apply(
                            CoreTerm::instantiate_constant(
                                cons,
                                vec![CoreType::Parameter(element_parameter)],
                            ),
                            cons_with_fixed.field(0).expect("append head binder"),
                        ),
                        cons_with_fixed
                            .recursive_result(0)
                            .expect("append recursive result"),
                    ),
                ),
            ],
        })?;

        Ok(Self {
            element_parameter,
            datatype,
            nil,
            cons,
            all,
            member,
            nodup,
            append,
        })
    }

    /// Add generic list length over a caller-supplied Nat interface.
    /// Installation is atomic and the supplied constants are type-checked by
    /// the structural-definition checker.
    pub fn install_length(
        &self,
        elaborator: &mut SpikeElaborator,
        natural_type: CoreType,
        zero: ConstantId,
        successor: ConstantId,
    ) -> Result<ListLength, SpikeError> {
        self.install_length_named(elaborator, "length", natural_type, zero, successor)
    }

    pub fn install_length_named(
        &self,
        elaborator: &mut SpikeElaborator,
        name: impl Into<String>,
        natural_type: CoreType,
        zero: ConstantId,
        successor: ConstantId,
    ) -> Result<ListLength, SpikeError> {
        let mut staged = elaborator.clone();
        let layout = StructuralArmLayout::new(2, 1, 0);
        let constant = staged.declare_structural_definition(StructuralDefinitionSpec {
            name: name.into(),
            type_parameters: vec![self.element_parameter],
            datatype: self.datatype,
            datatype_arguments: vec![CoreType::Parameter(self.element_parameter)],
            fixed_parameter_types: Vec::new(),
            recursive_argument_index: 0,
            result_type: natural_type.clone(),
            arms: vec![
                StructuralArmSpec::new(self.nil, CoreTerm::Constant(zero)),
                StructuralArmSpec::new(
                    self.cons,
                    CoreTerm::apply(
                        CoreTerm::Constant(successor),
                        layout.recursive_result(0).expect("length recursive result"),
                    ),
                ),
            ],
        })?;
        *elaborator = staged;
        Ok(ListLength {
            constant,
            natural_type,
            zero,
            successor,
        })
    }

    pub fn list_type(&self, element_type: CoreType) -> CoreType {
        CoreType::constructor(self.datatype, vec![element_type])
    }

    pub fn nil_term(&self, element_type: CoreType) -> CoreTerm {
        CoreTerm::instantiate_constant(self.nil, vec![element_type])
    }

    pub fn cons_term(&self, element_type: CoreType, head: CoreTerm, tail: CoreTerm) -> CoreTerm {
        CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(self.cons, vec![element_type]),
                head,
            ),
            tail,
        )
    }

    pub fn all_term(
        &self,
        element_type: CoreType,
        predicate: CoreTerm,
        list: CoreTerm,
    ) -> CoreTerm {
        apply2(
            CoreTerm::instantiate_constant(self.all, vec![element_type]),
            predicate,
            list,
        )
    }

    pub fn member_term(
        &self,
        element_type: CoreType,
        element: CoreTerm,
        list: CoreTerm,
    ) -> CoreTerm {
        apply2(
            CoreTerm::instantiate_constant(self.member, vec![element_type]),
            element,
            list,
        )
    }

    pub fn nodup_term(&self, element_type: CoreType, list: CoreTerm) -> CoreTerm {
        CoreTerm::apply(
            CoreTerm::instantiate_constant(self.nodup, vec![element_type]),
            list,
        )
    }

    pub fn append_term(&self, element_type: CoreType, left: CoreTerm, right: CoreTerm) -> CoreTerm {
        apply2(
            CoreTerm::instantiate_constant(self.append, vec![element_type]),
            left,
            right,
        )
    }
}

impl ListLength {
    pub fn apply(&self, element_type: CoreType, list: CoreTerm) -> CoreTerm {
        CoreTerm::apply(
            CoreTerm::instantiate_constant(self.constant, vec![element_type]),
            list,
        )
    }
}

fn apply2(function: CoreTerm, first: CoreTerm, second: CoreTerm) -> CoreTerm {
    CoreTerm::apply(CoreTerm::apply(function, first), second)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::StatementFragment;
    use crate::hol::terms::{infer_type, TermContext};

    #[test]
    fn generic_list_package_is_typed_reusable_and_fragment_precise() {
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
            .install_length(&mut elaborator, nat.clone(), zero, successor)
            .expect("install list length");

        let nil = lists.nil_term(nat.clone());
        let singleton = lists.cons_term(nat.clone(), CoreTerm::Constant(zero), nil);
        assert_eq!(
            infer_type(
                elaborator.types(),
                elaborator.constants(),
                &TermContext::new(),
                &singleton,
            )
            .expect("singleton type"),
            lists.list_type(nat.clone())
        );
        assert_eq!(
            infer_type(
                elaborator.types(),
                elaborator.constants(),
                &TermContext::new(),
                &length.apply(nat.clone(), singleton.clone()),
            )
            .expect("length type"),
            nat.clone()
        );
        let predicate = elaborator
            .declare_constant("P", CoreType::arrow(nat.clone(), CoreType::Prop))
            .expect("declare Nat predicate");
        for proposition in [
            lists.all_term(
                nat.clone(),
                CoreTerm::Constant(predicate),
                singleton.clone(),
            ),
            lists.nodup_term(nat.clone(), singleton.clone()),
        ] {
            assert_eq!(
                infer_type(
                    elaborator.types(),
                    elaborator.constants(),
                    &TermContext::new(),
                    &proposition,
                )
                .expect("list predicate type"),
                CoreType::Prop
            );
        }
        assert_eq!(
            infer_type(
                elaborator.types(),
                elaborator.constants(),
                &TermContext::new(),
                &lists.append_term(nat.clone(), singleton.clone(), lists.nil_term(nat.clone()),),
            )
            .expect("append type"),
            lists.list_type(nat.clone())
        );

        let membership = lists.member_term(nat.clone(), CoreTerm::Constant(zero), singleton);
        assert_eq!(
            elaborator
                .classify(&membership)
                .expect("classify concrete membership"),
            StatementFragment::FirstOrder
        );
        let open_membership =
            lists.member_term(nat.clone(), CoreTerm::Constant(zero), CoreTerm::Bound(0));
        assert_eq!(
            elaborator
                .classify_with_parameters(&[lists.list_type(nat)], &open_membership)
                .expect("classify open list membership"),
            StatementFragment::FirstOrderInductive
        );

        let prop_nil = lists.nil_term(CoreType::Prop);
        assert_eq!(
            infer_type(
                elaborator.types(),
                elaborator.constants(),
                &TermContext::new(),
                &prop_nil,
            )
            .expect("List Prop remains available to HOL"),
            lists.list_type(CoreType::Prop)
        );
        let proposition_list = lists.list_type(CoreType::Prop);
        let proposition_predicate = CoreType::arrow(CoreType::Prop, CoreType::Prop);
        let higher_order_all =
            lists.all_term(CoreType::Prop, CoreTerm::Bound(0), CoreTerm::Bound(1));
        assert_eq!(
            elaborator
                .classify_with_parameters(
                    &[proposition_list, proposition_predicate],
                    &higher_order_all,
                )
                .expect("classify higher-order List instance"),
            StatementFragment::HigherOrder
        );
    }

    #[test]
    fn list_package_and_length_extension_are_transactional() {
        let mut blocked = SpikeElaborator::new();
        blocked
            .declare_constant("Nodup", CoreType::Prop)
            .expect("reserve a late package name");
        let before_blocked_install = blocked.clone();
        ListLibrary::install(&mut blocked)
            .expect_err("a collision after earlier staged declarations must fail");
        assert_eq!(blocked, before_blocked_install);

        let mut elaborator = SpikeElaborator::new();
        let lists = ListLibrary::install(&mut elaborator).expect("first install");
        let after_list = elaborator.clone();
        ListLibrary::install(&mut elaborator).expect_err("duplicate package must fail");
        assert_eq!(elaborator, after_list);

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
        lists
            .install_length(&mut elaborator, nat.clone(), zero, successor)
            .expect("first length install");
        let after_length = elaborator.clone();
        lists
            .install_length(&mut elaborator, nat, zero, successor)
            .expect_err("duplicate length must fail");
        assert_eq!(elaborator, after_length);
    }
}
