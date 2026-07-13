//! Versioned installation registry for checked HOL library packages.
//!
//! The registry is deliberately independent of surface syntax. It gives the
//! compatibility driver and a future native HOL frontend one atomic package
//! mechanism, with logical provenance and stable reserved core names. Surface
//! imports can later bind aliases to these records without reinstalling or
//! duplicating kernel declarations.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use super::finite_library::{FiniteEnumerationLibrary, FiniteEnumerationNames};
use super::fragments::DeclarationId;
use super::h35_cardinality::{
    install_cardinality_transport_named, CardinalityTransportLibrary, CardinalityTransportNames,
};
use super::library::{ListLength, ListLibrary, ListLibraryNames};
use super::proofs::HolDraftProof;
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::{shift_under_new_binder, ConstantId, CoreTerm};
use super::theorems::TheoremId;
use super::types::CoreType;

pub const BUILTIN_LIST_V1_MODULE: &str = "std/hol/list";
pub const BUILTIN_LIST_V1_NAMESPACE: &str = "@library.list.v1";
pub const BUILTIN_CARDINALITY_V1_MODULE: &str = "std/hol/cardinality";
pub const BUILTIN_CARDINALITY_V1_NAMESPACE: &str = "@library.cardinality.v1";
pub const BUILTIN_FINITE_V1_MODULE: &str = "std/hol/finite";
pub const BUILTIN_FINITE_V1_NAMESPACE: &str = "@library.finite.v1";

fn definitional_iff_proof(left: CoreTerm, right: CoreTerm) -> HolDraftProof {
    HolDraftProof::AndIntro(
        Box::new(HolDraftProof::ImpIntro {
            premise: left.clone(),
            body: Box::new(HolDraftProof::Hypothesis(0)),
        }),
        Box::new(HolDraftProof::ImpIntro {
            premise: right,
            body: Box::new(HolDraftProof::Hypothesis(0)),
        }),
    )
}

fn list_cons_tail_congruence(
    lists: &ListLibrary,
    element_type: &CoreType,
    head: CoreTerm,
    left_tail: CoreTerm,
    proof_equality: HolDraftProof,
) -> Result<HolDraftProof, SpikeError> {
    let shifted_head = shift_under_new_binder(&head)?;
    let shifted_left_tail = shift_under_new_binder(&left_tail)?;
    let list_type = lists.list_type(element_type.clone());
    let applied_left = lists.cons_term(element_type.clone(), head, left_tail);
    Ok(HolDraftProof::EqualityElim {
        proof_equality: Box::new(proof_equality),
        motive: CoreTerm::lambda(
            list_type.clone(),
            CoreTerm::equality(
                list_type,
                lists.cons_term(
                    element_type.clone(),
                    shifted_head.clone(),
                    shifted_left_tail,
                ),
                lists.cons_term(element_type.clone(), shifted_head, CoreTerm::Bound(0)),
            ),
        ),
        proof_left: Box::new(HolDraftProof::EqualityRefl(applied_left)),
    })
}

fn unary_constant_congruence(
    function: ConstantId,
    domain: &CoreType,
    left: CoreTerm,
    proof_equality: HolDraftProof,
) -> Result<HolDraftProof, SpikeError> {
    let shifted_left = shift_under_new_binder(&left)?;
    let applied_left = CoreTerm::apply(CoreTerm::Constant(function), left);
    Ok(HolDraftProof::EqualityElim {
        proof_equality: Box::new(proof_equality),
        motive: CoreTerm::lambda(
            domain.clone(),
            CoreTerm::equality(
                domain.clone(),
                CoreTerm::apply(CoreTerm::Constant(function), shifted_left),
                CoreTerm::apply(CoreTerm::Constant(function), CoreTerm::Bound(0)),
            ),
        ),
        proof_left: Box::new(HolDraftProof::EqualityRefl(applied_left)),
    })
}

fn apply_binary_constant(function: ConstantId, left: CoreTerm, right: CoreTerm) -> CoreTerm {
    CoreTerm::apply(CoreTerm::apply(CoreTerm::Constant(function), left), right)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LibraryPackageId {
    ListV1,
    CardinalityV1,
    FiniteV1,
}

impl LibraryPackageId {
    pub fn from_logical_id(logical_id: &str) -> Option<Self> {
        match logical_id {
            "std/hol/list@1" => Some(Self::ListV1),
            "std/hol/cardinality@1" => Some(Self::CardinalityV1),
            "std/hol/finite@1" => Some(Self::FiniteV1),
            _ => None,
        }
    }
}

impl fmt::Display for LibraryPackageId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ListV1 => write!(f, "{BUILTIN_LIST_V1_MODULE}@1"),
            Self::CardinalityV1 => write!(f, "{BUILTIN_CARDINALITY_V1_MODULE}@1"),
            Self::FiniteV1 => write!(f, "{BUILTIN_FINITE_V1_MODULE}@1"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LibraryPackageSource {
    Builtin,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryPackageProvenance {
    pub module: String,
    pub version: u32,
    pub source: LibraryPackageSource,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LibraryDeclarationKind {
    Datatype,
    Constructor,
    Definition,
    Theorem,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryDeclaration {
    pub logical_name: String,
    pub core_name: String,
    pub kind: LibraryDeclarationKind,
    pub receipt: Option<DeclarationId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryPackageRecord {
    pub id: LibraryPackageId,
    pub provenance: LibraryPackageProvenance,
    pub core_namespace: String,
    pub dependencies: Vec<LibraryPackageId>,
    pub declarations: Vec<LibraryDeclaration>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstalledListLibrary {
    pub record: LibraryPackageRecord,
    pub lists: ListLibrary,
    pub length: ListLength,
    pub natural_addition: ConstantId,
    pub append_nil_left: TheoremId,
    pub append_cons: TheoremId,
    pub length_nil: TheoremId,
    pub length_cons: TheoremId,
    pub member_nil: TheoremId,
    pub member_cons: TheoremId,
    pub nodup_nil: TheoremId,
    pub nodup_cons: TheoremId,
    pub all_nil: TheoremId,
    pub all_cons: TheoremId,
    pub append_nil_right: TheoremId,
    pub append_assoc: TheoremId,
    pub length_append: TheoremId,
    pub list_induction: TheoremId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstalledCardinalityLibrary {
    pub record: LibraryPackageRecord,
    pub cardinality: CardinalityTransportLibrary,
    pub map_nil_schema: TheoremId,
    pub map_cons_schema: TheoremId,
    pub map_length_schema: TheoremId,
    pub member_map_forward_schema: TheoremId,
    pub member_map_reverse_schema: TheoremId,
    pub nodup_map_injective_schema: TheoremId,
    pub map_coverage_surjective_schema: TheoremId,
    pub cardinality_transport_schema: TheoremId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstalledFiniteLibrary {
    pub record: LibraryPackageRecord,
    pub finite: FiniteEnumerationLibrary,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstalledLibraryPackage {
    ListV1(InstalledListLibrary),
    CardinalityV1(InstalledCardinalityLibrary),
    FiniteV1(InstalledFiniteLibrary),
}

impl InstalledLibraryPackage {
    pub fn record(&self) -> &LibraryPackageRecord {
        match self {
            Self::ListV1(installed) => &installed.record,
            Self::CardinalityV1(installed) => &installed.record,
            Self::FiniteV1(installed) => &installed.record,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct HolLibraryRegistry {
    packages: BTreeMap<LibraryPackageId, InstalledLibraryPackage>,
}

impl HolLibraryRegistry {
    pub fn packages(&self) -> &BTreeMap<LibraryPackageId, InstalledLibraryPackage> {
        &self.packages
    }

    pub fn get(&self, id: LibraryPackageId) -> Option<&InstalledLibraryPackage> {
        self.packages.get(&id)
    }

    pub fn list_v1(&self) -> Option<&InstalledListLibrary> {
        match self.get(LibraryPackageId::ListV1) {
            Some(InstalledLibraryPackage::ListV1(installed)) => Some(installed),
            _ => None,
        }
    }

    pub fn cardinality_v1(&self) -> Option<&InstalledCardinalityLibrary> {
        match self.get(LibraryPackageId::CardinalityV1) {
            Some(InstalledLibraryPackage::CardinalityV1(installed)) => Some(installed),
            _ => None,
        }
    }

    pub fn finite_v1(&self) -> Option<&InstalledFiniteLibrary> {
        match self.get(LibraryPackageId::FiniteV1) {
            Some(InstalledLibraryPackage::FiniteV1(installed)) => Some(installed),
            _ => None,
        }
    }

    pub fn declaration_by_receipt(
        &self,
        receipt: DeclarationId,
    ) -> Option<(&LibraryPackageRecord, &LibraryDeclaration)> {
        self.packages.values().find_map(|package| {
            let record = package.record();
            record
                .declarations
                .iter()
                .find(|declaration| declaration.receipt == Some(receipt))
                .map(|declaration| (record, declaration))
        })
    }

    /// Stable human/audit name for a package-owned declaration receipt.
    pub fn receipt_name(&self, receipt: DeclarationId) -> Option<String> {
        self.declaration_by_receipt(receipt)
            .map(|(record, declaration)| format!("{}::{}", record.id, declaration.logical_name))
    }

    /// Install the built-in generic list package and its Nat length extension.
    ///
    /// Repeated installation is idempotent. A name, type, positivity, or
    /// recursion failure commits neither core declarations nor registry
    /// metadata.
    pub fn install_builtin_list_v1(
        &mut self,
        core: &mut SpikeElaborator,
        natural_type: CoreType,
        zero: ConstantId,
        successor: ConstantId,
        addition: ConstantId,
    ) -> Result<InstalledListLibrary, SpikeError> {
        if let Some(installed) = self.list_v1() {
            validate_installed_list_v1(core, installed)?;
            if installed.length.natural_type != natural_type
                || installed.length.zero != zero
                || installed.length.successor != successor
                || installed.natural_addition != addition
            {
                return Err(SpikeError {
                    message: format!(
                        "library package `{}` is already installed against a different Nat interface",
                        LibraryPackageId::ListV1
                    ),
                });
            }
            return Ok(installed.clone());
        }

        let mut staged_core = core.clone();
        let names = ListLibraryNames::under_namespace(BUILTIN_LIST_V1_NAMESPACE);
        let lists = ListLibrary::install_named(&mut staged_core, &names)?;
        let length = lists.install_length_named(
            &mut staged_core,
            names.length.clone(),
            natural_type,
            zero,
            successor,
        )?;
        let element_type = CoreType::Parameter(lists.element_parameter);
        let list_type = lists.list_type(element_type.clone());
        let append_nil_left_statement = CoreTerm::equality(
            list_type.clone(),
            lists.append_term(
                element_type.clone(),
                lists.nil_term(element_type.clone()),
                CoreTerm::Bound(0),
            ),
            CoreTerm::Bound(0),
        );
        let (append_nil_left, append_nil_left_receipt) = staged_core
            .declare_theorem_with_parameters(
                names.append_nil_left.clone(),
                vec![lists.element_parameter],
                vec![list_type.clone()],
                append_nil_left_statement,
                HolDraftProof::EqualityRefl(CoreTerm::Bound(0)),
            )?;
        let append_cons_right = lists.cons_term(
            element_type.clone(),
            CoreTerm::Bound(2),
            lists.append_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
        );
        let append_cons_statement = CoreTerm::equality(
            list_type.clone(),
            lists.append_term(
                element_type.clone(),
                lists.cons_term(element_type.clone(), CoreTerm::Bound(2), CoreTerm::Bound(1)),
                CoreTerm::Bound(0),
            ),
            append_cons_right.clone(),
        );
        let (append_cons, append_cons_receipt) = staged_core.declare_theorem_with_parameters(
            names.append_cons.clone(),
            vec![lists.element_parameter],
            vec![element_type.clone(), list_type.clone(), list_type.clone()],
            append_cons_statement,
            HolDraftProof::EqualityRefl(append_cons_right),
        )?;
        let zero_term = CoreTerm::Constant(length.zero);
        let length_nil_statement = CoreTerm::equality(
            length.natural_type.clone(),
            length.apply(element_type.clone(), lists.nil_term(element_type.clone())),
            zero_term.clone(),
        );
        let (length_nil, length_nil_receipt) = staged_core.declare_theorem_with_parameters(
            names.length_nil.clone(),
            vec![lists.element_parameter],
            Vec::new(),
            length_nil_statement,
            HolDraftProof::EqualityRefl(zero_term),
        )?;
        let length_cons_right = CoreTerm::apply(
            CoreTerm::Constant(length.successor),
            length.apply(element_type.clone(), CoreTerm::Bound(0)),
        );
        let length_cons_statement = CoreTerm::equality(
            length.natural_type.clone(),
            length.apply(
                element_type.clone(),
                lists.cons_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
            ),
            length_cons_right.clone(),
        );
        let (length_cons, length_cons_receipt) = staged_core.declare_theorem_with_parameters(
            names.length_cons.clone(),
            vec![lists.element_parameter],
            vec![element_type.clone(), list_type.clone()],
            length_cons_statement,
            HolDraftProof::EqualityRefl(length_cons_right),
        )?;
        let member_nil_premise = lists.member_term(
            element_type.clone(),
            CoreTerm::Bound(0),
            lists.nil_term(element_type.clone()),
        );
        let member_nil_statement = CoreTerm::implies(member_nil_premise.clone(), CoreTerm::Falsity);
        let (member_nil, member_nil_receipt) = staged_core.declare_theorem_with_parameters(
            names.member_nil.clone(),
            vec![lists.element_parameter],
            vec![element_type.clone()],
            member_nil_statement,
            HolDraftProof::ImpIntro {
                premise: member_nil_premise,
                body: Box::new(HolDraftProof::Hypothesis(0)),
            },
        )?;
        let member_cons_left = lists.member_term(
            element_type.clone(),
            CoreTerm::Bound(2),
            lists.cons_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
        );
        let member_cons_right = CoreTerm::or(
            CoreTerm::equality(element_type.clone(), CoreTerm::Bound(2), CoreTerm::Bound(1)),
            lists.member_term(element_type.clone(), CoreTerm::Bound(2), CoreTerm::Bound(0)),
        );
        let member_cons_statement = CoreTerm::and(
            CoreTerm::implies(member_cons_left.clone(), member_cons_right.clone()),
            CoreTerm::implies(member_cons_right.clone(), member_cons_left.clone()),
        );
        let (member_cons, member_cons_receipt) = staged_core.declare_theorem_with_parameters(
            names.member_cons.clone(),
            vec![lists.element_parameter],
            vec![
                element_type.clone(),
                element_type.clone(),
                list_type.clone(),
            ],
            member_cons_statement,
            definitional_iff_proof(member_cons_left, member_cons_right),
        )?;
        let nodup_nil_statement =
            lists.nodup_term(element_type.clone(), lists.nil_term(element_type.clone()));
        let (nodup_nil, nodup_nil_receipt) = staged_core.declare_theorem_with_parameters(
            names.nodup_nil.clone(),
            vec![lists.element_parameter],
            Vec::new(),
            nodup_nil_statement,
            HolDraftProof::TruthIntro,
        )?;
        let nodup_cons_left = lists.nodup_term(
            element_type.clone(),
            lists.cons_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
        );
        let nodup_cons_right = CoreTerm::and(
            CoreTerm::implies(
                lists.member_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
                CoreTerm::Falsity,
            ),
            lists.nodup_term(element_type.clone(), CoreTerm::Bound(0)),
        );
        let nodup_cons_statement = CoreTerm::and(
            CoreTerm::implies(nodup_cons_left.clone(), nodup_cons_right.clone()),
            CoreTerm::implies(nodup_cons_right.clone(), nodup_cons_left.clone()),
        );
        let (nodup_cons, nodup_cons_receipt) = staged_core.declare_theorem_with_parameters(
            names.nodup_cons.clone(),
            vec![lists.element_parameter],
            vec![element_type.clone(), list_type.clone()],
            nodup_cons_statement,
            definitional_iff_proof(nodup_cons_left, nodup_cons_right),
        )?;
        let element_predicate_type = CoreType::arrow(element_type.clone(), CoreType::Prop);
        let all_nil_statement = lists.all_term(
            element_type.clone(),
            CoreTerm::Bound(0),
            lists.nil_term(element_type.clone()),
        );
        let (all_nil, all_nil_receipt) = staged_core.declare_theorem_with_parameters(
            names.all_nil.clone(),
            vec![lists.element_parameter],
            vec![element_predicate_type.clone()],
            all_nil_statement,
            HolDraftProof::TruthIntro,
        )?;
        let all_cons_left = lists.all_term(
            element_type.clone(),
            CoreTerm::Bound(2),
            lists.cons_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
        );
        let all_cons_right = CoreTerm::and(
            CoreTerm::apply(CoreTerm::Bound(2), CoreTerm::Bound(1)),
            lists.all_term(element_type.clone(), CoreTerm::Bound(2), CoreTerm::Bound(0)),
        );
        let all_cons_statement = CoreTerm::and(
            CoreTerm::implies(all_cons_left.clone(), all_cons_right.clone()),
            CoreTerm::implies(all_cons_right.clone(), all_cons_left.clone()),
        );
        let (all_cons, all_cons_receipt) = staged_core.declare_theorem_with_parameters(
            names.all_cons.clone(),
            vec![lists.element_parameter],
            vec![
                element_predicate_type,
                element_type.clone(),
                list_type.clone(),
            ],
            all_cons_statement,
            definitional_iff_proof(all_cons_left, all_cons_right),
        )?;
        let append_nil_right_nil = lists.nil_term(element_type.clone());
        let append_nil_right_statement = CoreTerm::equality(
            list_type.clone(),
            lists.append_term(
                element_type.clone(),
                CoreTerm::Bound(0),
                append_nil_right_nil.clone(),
            ),
            CoreTerm::Bound(0),
        );
        let append_nil_right_motive = CoreTerm::lambda(
            list_type.clone(),
            CoreTerm::equality(
                list_type.clone(),
                lists.append_term(
                    element_type.clone(),
                    CoreTerm::Bound(0),
                    append_nil_right_nil.clone(),
                ),
                CoreTerm::Bound(0),
            ),
        );
        let append_nil_right_step_left = lists.append_term(
            element_type.clone(),
            CoreTerm::Bound(1),
            append_nil_right_nil.clone(),
        );
        let append_nil_right_proof = HolDraftProof::Induction {
            datatype: lists.datatype,
            type_arguments: vec![element_type.clone()],
            motive: append_nil_right_motive,
            scrutinee: CoreTerm::Bound(0),
            cases: vec![
                HolDraftProof::EqualityRefl(append_nil_right_nil),
                list_cons_tail_congruence(
                    &lists,
                    &element_type,
                    CoreTerm::Bound(0),
                    append_nil_right_step_left,
                    HolDraftProof::Hypothesis(0),
                )?,
            ],
        };
        let (append_nil_right, append_nil_right_receipt) = staged_core
            .declare_theorem_with_parameters(
                names.append_nil_right.clone(),
                vec![lists.element_parameter],
                vec![list_type.clone()],
                append_nil_right_statement,
                append_nil_right_proof,
            )?;
        let append_assoc_left = lists.append_term(
            element_type.clone(),
            lists.append_term(element_type.clone(), CoreTerm::Bound(2), CoreTerm::Bound(1)),
            CoreTerm::Bound(0),
        );
        let append_assoc_right = lists.append_term(
            element_type.clone(),
            CoreTerm::Bound(2),
            lists.append_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
        );
        let append_assoc_statement =
            CoreTerm::equality(list_type.clone(), append_assoc_left, append_assoc_right);
        let append_assoc_motive = CoreTerm::lambda(
            list_type.clone(),
            CoreTerm::equality(
                list_type.clone(),
                lists.append_term(
                    element_type.clone(),
                    lists.append_term(element_type.clone(), CoreTerm::Bound(0), CoreTerm::Bound(2)),
                    CoreTerm::Bound(1),
                ),
                lists.append_term(
                    element_type.clone(),
                    CoreTerm::Bound(0),
                    lists.append_term(element_type.clone(), CoreTerm::Bound(2), CoreTerm::Bound(1)),
                ),
            ),
        );
        let append_assoc_base =
            lists.append_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0));
        let append_assoc_step_left = lists.append_term(
            element_type.clone(),
            lists.append_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(3)),
            CoreTerm::Bound(2),
        );
        let append_assoc_proof = HolDraftProof::Induction {
            datatype: lists.datatype,
            type_arguments: vec![element_type.clone()],
            motive: append_assoc_motive,
            scrutinee: CoreTerm::Bound(2),
            cases: vec![
                HolDraftProof::EqualityRefl(append_assoc_base),
                list_cons_tail_congruence(
                    &lists,
                    &element_type,
                    CoreTerm::Bound(0),
                    append_assoc_step_left,
                    HolDraftProof::Hypothesis(0),
                )?,
            ],
        };
        let (append_assoc, append_assoc_receipt) = staged_core.declare_theorem_with_parameters(
            names.append_assoc.clone(),
            vec![lists.element_parameter],
            vec![list_type.clone(), list_type.clone(), list_type.clone()],
            append_assoc_statement,
            append_assoc_proof,
        )?;
        let length_append_left = length.apply(
            element_type.clone(),
            lists.append_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0)),
        );
        let length_append_right = apply_binary_constant(
            addition,
            length.apply(element_type.clone(), CoreTerm::Bound(1)),
            length.apply(element_type.clone(), CoreTerm::Bound(0)),
        );
        let length_append_statement = CoreTerm::equality(
            length.natural_type.clone(),
            length_append_left,
            length_append_right,
        );
        let length_append_motive = CoreTerm::lambda(
            list_type.clone(),
            CoreTerm::equality(
                length.natural_type.clone(),
                length.apply(
                    element_type.clone(),
                    lists.append_term(element_type.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1)),
                ),
                apply_binary_constant(
                    addition,
                    length.apply(element_type.clone(), CoreTerm::Bound(0)),
                    length.apply(element_type.clone(), CoreTerm::Bound(1)),
                ),
            ),
        );
        let length_append_base = length.apply(element_type.clone(), CoreTerm::Bound(0));
        let length_append_step_left = length.apply(
            element_type.clone(),
            lists.append_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(2)),
        );
        let length_append_proof = HolDraftProof::Induction {
            datatype: lists.datatype,
            type_arguments: vec![element_type.clone()],
            motive: length_append_motive,
            scrutinee: CoreTerm::Bound(1),
            cases: vec![
                HolDraftProof::EqualityRefl(length_append_base),
                unary_constant_congruence(
                    length.successor,
                    &length.natural_type,
                    length_append_step_left,
                    HolDraftProof::Hypothesis(0),
                )?,
            ],
        };
        let (length_append, length_append_receipt) = staged_core.declare_theorem_with_parameters(
            names.length_append.clone(),
            vec![lists.element_parameter],
            vec![list_type.clone(), list_type.clone()],
            length_append_statement,
            length_append_proof,
        )?;
        let property_type = CoreType::arrow(list_type.clone(), CoreType::Prop);
        let induction_base =
            CoreTerm::apply(CoreTerm::Bound(1), lists.nil_term(element_type.clone()));
        let induction_cons =
            lists.cons_term(element_type.clone(), CoreTerm::Bound(1), CoreTerm::Bound(0));
        let induction_step = CoreTerm::forall(
            element_type.clone(),
            CoreTerm::forall(
                list_type.clone(),
                CoreTerm::implies(
                    CoreTerm::apply(CoreTerm::Bound(3), CoreTerm::Bound(0)),
                    CoreTerm::apply(CoreTerm::Bound(3), induction_cons),
                ),
            ),
        );
        let induction_conclusion = CoreTerm::apply(CoreTerm::Bound(1), CoreTerm::Bound(0));
        let list_induction_statement = CoreTerm::implies(
            induction_base.clone(),
            CoreTerm::implies(induction_step.clone(), induction_conclusion),
        );
        let induction_cons_case = HolDraftProof::ImpElim {
            proof_implication: Box::new(HolDraftProof::ForallElim {
                proof_forall: Box::new(HolDraftProof::ForallElim {
                    proof_forall: Box::new(HolDraftProof::Hypothesis(1)),
                    argument: CoreTerm::Bound(0),
                }),
                argument: CoreTerm::Bound(1),
            }),
            proof_argument: Box::new(HolDraftProof::Hypothesis(0)),
        };
        let list_induction_proof = HolDraftProof::ImpIntro {
            premise: induction_base,
            body: Box::new(HolDraftProof::ImpIntro {
                premise: induction_step,
                body: Box::new(HolDraftProof::Induction {
                    datatype: lists.datatype,
                    type_arguments: vec![element_type.clone()],
                    motive: CoreTerm::Bound(1),
                    scrutinee: CoreTerm::Bound(0),
                    cases: vec![HolDraftProof::Hypothesis(1), induction_cons_case],
                }),
            }),
        };
        let (list_induction, list_induction_receipt) = staged_core
            .declare_theorem_with_parameters(
                names.list_induction.clone(),
                vec![lists.element_parameter],
                vec![property_type, list_type.clone()],
                list_induction_statement,
                list_induction_proof,
            )?;
        let receipt = |constant| {
            staged_core
                .definition_receipt(constant)
                .map(|receipt| receipt.id())
        };
        let declaration =
            |logical_name: &str,
             core_name: &str,
             kind: LibraryDeclarationKind,
             receipt: Option<DeclarationId>| LibraryDeclaration {
                logical_name: logical_name.to_string(),
                core_name: core_name.to_string(),
                kind,
                receipt,
            };
        let installed = InstalledListLibrary {
            record: LibraryPackageRecord {
                id: LibraryPackageId::ListV1,
                provenance: LibraryPackageProvenance {
                    module: BUILTIN_LIST_V1_MODULE.to_string(),
                    version: 1,
                    source: LibraryPackageSource::Builtin,
                },
                core_namespace: BUILTIN_LIST_V1_NAMESPACE.to_string(),
                dependencies: Vec::new(),
                declarations: vec![
                    declaration(
                        "List",
                        &names.datatype,
                        LibraryDeclarationKind::Datatype,
                        None,
                    ),
                    declaration("nil", &names.nil, LibraryDeclarationKind::Constructor, None),
                    declaration(
                        "cons",
                        &names.cons,
                        LibraryDeclarationKind::Constructor,
                        None,
                    ),
                    declaration(
                        "All",
                        &names.all,
                        LibraryDeclarationKind::Definition,
                        receipt(lists.all),
                    ),
                    declaration(
                        "Member",
                        &names.member,
                        LibraryDeclarationKind::Definition,
                        receipt(lists.member),
                    ),
                    declaration(
                        "Nodup",
                        &names.nodup,
                        LibraryDeclarationKind::Definition,
                        receipt(lists.nodup),
                    ),
                    declaration(
                        "append",
                        &names.append,
                        LibraryDeclarationKind::Definition,
                        receipt(lists.append),
                    ),
                    declaration(
                        "length",
                        &names.length,
                        LibraryDeclarationKind::Definition,
                        receipt(length.constant),
                    ),
                    declaration(
                        "append_nil_left",
                        &names.append_nil_left,
                        LibraryDeclarationKind::Theorem,
                        Some(append_nil_left_receipt.id()),
                    ),
                    declaration(
                        "append_cons",
                        &names.append_cons,
                        LibraryDeclarationKind::Theorem,
                        Some(append_cons_receipt.id()),
                    ),
                    declaration(
                        "length_nil",
                        &names.length_nil,
                        LibraryDeclarationKind::Theorem,
                        Some(length_nil_receipt.id()),
                    ),
                    declaration(
                        "length_cons",
                        &names.length_cons,
                        LibraryDeclarationKind::Theorem,
                        Some(length_cons_receipt.id()),
                    ),
                    declaration(
                        "member_nil",
                        &names.member_nil,
                        LibraryDeclarationKind::Theorem,
                        Some(member_nil_receipt.id()),
                    ),
                    declaration(
                        "member_cons",
                        &names.member_cons,
                        LibraryDeclarationKind::Theorem,
                        Some(member_cons_receipt.id()),
                    ),
                    declaration(
                        "nodup_nil",
                        &names.nodup_nil,
                        LibraryDeclarationKind::Theorem,
                        Some(nodup_nil_receipt.id()),
                    ),
                    declaration(
                        "nodup_cons",
                        &names.nodup_cons,
                        LibraryDeclarationKind::Theorem,
                        Some(nodup_cons_receipt.id()),
                    ),
                    declaration(
                        "all_nil",
                        &names.all_nil,
                        LibraryDeclarationKind::Theorem,
                        Some(all_nil_receipt.id()),
                    ),
                    declaration(
                        "all_cons",
                        &names.all_cons,
                        LibraryDeclarationKind::Theorem,
                        Some(all_cons_receipt.id()),
                    ),
                    declaration(
                        "append_nil_right",
                        &names.append_nil_right,
                        LibraryDeclarationKind::Theorem,
                        Some(append_nil_right_receipt.id()),
                    ),
                    declaration(
                        "append_assoc",
                        &names.append_assoc,
                        LibraryDeclarationKind::Theorem,
                        Some(append_assoc_receipt.id()),
                    ),
                    declaration(
                        "length_append",
                        &names.length_append,
                        LibraryDeclarationKind::Theorem,
                        Some(length_append_receipt.id()),
                    ),
                    declaration(
                        "list_induction",
                        &names.list_induction,
                        LibraryDeclarationKind::Theorem,
                        Some(list_induction_receipt.id()),
                    ),
                ],
            },
            lists,
            length,
            natural_addition: addition,
            append_nil_left,
            append_cons,
            length_nil,
            length_cons,
            member_nil,
            member_cons,
            nodup_nil,
            nodup_cons,
            all_nil,
            all_cons,
            append_nil_right,
            append_assoc,
            length_append,
            list_induction,
        };

        let mut staged_registry = self.clone();
        staged_registry.packages.insert(
            LibraryPackageId::ListV1,
            InstalledLibraryPackage::ListV1(installed.clone()),
        );
        *core = staged_core;
        *self = staged_registry;
        Ok(installed)
    }

    /// Install cardinality transport and its versioned List dependency.
    ///
    /// The complete dependency closure is staged as one transaction: when List
    /// is not already installed, a failure in a later cardinality lemma commits
    /// neither package. Repeated installation validates both registry records
    /// against the supplied core and is otherwise idempotent.
    pub fn install_builtin_cardinality_v1(
        &mut self,
        core: &mut SpikeElaborator,
        natural_type: CoreType,
        zero: ConstantId,
        successor: ConstantId,
        addition: ConstantId,
    ) -> Result<InstalledCardinalityLibrary, SpikeError> {
        let mut staged_core = core.clone();
        let mut staged_registry = self.clone();
        let lists = staged_registry.install_builtin_list_v1(
            &mut staged_core,
            natural_type,
            zero,
            successor,
            addition,
        )?;

        if let Some(installed) = staged_registry.cardinality_v1().cloned() {
            validate_installed_cardinality_v1(&staged_core, &installed, &lists)?;
            *core = staged_core;
            *self = staged_registry;
            return Ok(installed);
        }

        let names = CardinalityTransportNames::under_namespace(BUILTIN_CARDINALITY_V1_NAMESPACE);
        let cardinality = install_cardinality_transport_named(
            &mut staged_core,
            &lists.lists,
            &lists.length,
            &names,
        )?;
        let domain_type = CoreType::Parameter(cardinality.domain_parameter);
        let codomain_type = CoreType::Parameter(cardinality.codomain_parameter);
        let function_type = CoreType::arrow(domain_type.clone(), codomain_type.clone());
        let source_list_type = lists.lists.list_type(domain_type.clone());
        let target_list_type = lists.lists.list_type(codomain_type.clone());
        let map_values = |function: CoreTerm, values: CoreTerm| {
            CoreTerm::apply(
                CoreTerm::apply(
                    CoreTerm::instantiate_constant(
                        cardinality.map,
                        vec![domain_type.clone(), codomain_type.clone()],
                    ),
                    function,
                ),
                values,
            )
        };
        let map_nil_schema_name = format!("{BUILTIN_CARDINALITY_V1_NAMESPACE}.map_nil_schema");
        let mapped_nil = map_values(
            CoreTerm::Bound(0),
            lists.lists.nil_term(domain_type.clone()),
        );
        let (map_nil_schema, _) = staged_core.declare_theorem_with_parameters(
            map_nil_schema_name.clone(),
            vec![cardinality.domain_parameter, cardinality.codomain_parameter],
            vec![function_type.clone()],
            CoreTerm::equality(
                target_list_type.clone(),
                mapped_nil.clone(),
                lists.lists.nil_term(codomain_type.clone()),
            ),
            HolDraftProof::EqualityRefl(mapped_nil),
        )?;
        let map_cons_schema_name = format!("{BUILTIN_CARDINALITY_V1_NAMESPACE}.map_cons_schema");
        let source_cons = CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(lists.lists.cons, vec![domain_type.clone()]),
                CoreTerm::Bound(1),
            ),
            CoreTerm::Bound(0),
        );
        let mapped_cons = map_values(CoreTerm::Bound(2), source_cons);
        let target_cons = CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(lists.lists.cons, vec![codomain_type.clone()]),
                CoreTerm::apply(CoreTerm::Bound(2), CoreTerm::Bound(1)),
            ),
            map_values(CoreTerm::Bound(2), CoreTerm::Bound(0)),
        );
        let (map_cons_schema, _) = staged_core.declare_theorem_with_parameters(
            map_cons_schema_name.clone(),
            vec![cardinality.domain_parameter, cardinality.codomain_parameter],
            vec![
                function_type.clone(),
                domain_type.clone(),
                source_list_type.clone(),
            ],
            CoreTerm::equality(target_list_type, mapped_cons.clone(), target_cons),
            HolDraftProof::EqualityRefl(mapped_cons),
        )?;
        let mapped_values = CoreTerm::apply(
            CoreTerm::apply(
                CoreTerm::instantiate_constant(
                    cardinality.map,
                    vec![domain_type.clone(), codomain_type.clone()],
                ),
                CoreTerm::Bound(1),
            ),
            CoreTerm::Bound(0),
        );
        let map_length_schema_name =
            format!("{BUILTIN_CARDINALITY_V1_NAMESPACE}.map_length_schema");
        let (map_length_schema, _) = staged_core.declare_theorem_with_parameters(
            map_length_schema_name.clone(),
            vec![cardinality.domain_parameter, cardinality.codomain_parameter],
            vec![function_type.clone(), source_list_type.clone()],
            CoreTerm::equality(
                lists.length.natural_type.clone(),
                lists.length.apply(codomain_type.clone(), mapped_values),
                lists.length.apply(domain_type.clone(), CoreTerm::Bound(0)),
            ),
            HolDraftProof::ForallElim {
                proof_forall: Box::new(HolDraftProof::ForallElim {
                    proof_forall: Box::new(HolDraftProof::TheoremRef {
                        theorem: cardinality.map_length,
                        type_arguments: vec![
                            CoreType::Parameter(cardinality.domain_parameter),
                            CoreType::Parameter(cardinality.codomain_parameter),
                        ],
                        term_arguments: Vec::new(),
                    }),
                    argument: CoreTerm::Bound(1),
                }),
                argument: CoreTerm::Bound(0),
            },
        )?;
        let inverse_function_type = CoreType::arrow(codomain_type.clone(), domain_type.clone());
        let member = |element_type: CoreType, value: CoreTerm, values: CoreTerm| {
            CoreTerm::apply(
                CoreTerm::apply(
                    CoreTerm::instantiate_constant(lists.lists.member, vec![element_type]),
                    value,
                ),
                values,
            )
        };
        let nodup = |element_type: CoreType, values: CoreTerm| {
            CoreTerm::apply(
                CoreTerm::instantiate_constant(lists.lists.nodup, vec![element_type]),
                values,
            )
        };
        let member_map_forward_schema_name =
            format!("{BUILTIN_CARDINALITY_V1_NAMESPACE}.member_map_forward_schema");
        let (member_map_forward_schema, _) = staged_core.declare_theorem_with_parameters(
            member_map_forward_schema_name.clone(),
            vec![cardinality.domain_parameter, cardinality.codomain_parameter],
            vec![
                function_type.clone(),
                source_list_type.clone(),
                domain_type.clone(),
            ],
            CoreTerm::implies(
                member(domain_type.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1)),
                member(
                    codomain_type.clone(),
                    CoreTerm::apply(CoreTerm::Bound(2), CoreTerm::Bound(0)),
                    map_values(CoreTerm::Bound(2), CoreTerm::Bound(1)),
                ),
            ),
            HolDraftProof::ForallElim {
                proof_forall: Box::new(HolDraftProof::ForallElim {
                    proof_forall: Box::new(HolDraftProof::ForallElim {
                        proof_forall: Box::new(HolDraftProof::TheoremRef {
                            theorem: cardinality.member_map_forward,
                            type_arguments: vec![
                                CoreType::Parameter(cardinality.domain_parameter),
                                CoreType::Parameter(cardinality.codomain_parameter),
                            ],
                            term_arguments: Vec::new(),
                        }),
                        argument: CoreTerm::Bound(2),
                    }),
                    argument: CoreTerm::Bound(1),
                }),
                argument: CoreTerm::Bound(0),
            },
        )?;
        let reverse_left_inverse = CoreTerm::forall(
            domain_type.clone(),
            CoreTerm::equality(
                domain_type.clone(),
                CoreTerm::apply(
                    CoreTerm::Bound(3),
                    CoreTerm::apply(CoreTerm::Bound(4), CoreTerm::Bound(0)),
                ),
                CoreTerm::Bound(0),
            ),
        );
        let member_map_reverse_schema_name =
            format!("{BUILTIN_CARDINALITY_V1_NAMESPACE}.member_map_reverse_schema");
        let (member_map_reverse_schema, _) = staged_core.declare_theorem_with_parameters(
            member_map_reverse_schema_name.clone(),
            vec![cardinality.domain_parameter, cardinality.codomain_parameter],
            vec![
                function_type.clone(),
                inverse_function_type.clone(),
                source_list_type.clone(),
                domain_type.clone(),
            ],
            CoreTerm::implies(
                reverse_left_inverse.clone(),
                CoreTerm::implies(
                    member(
                        codomain_type.clone(),
                        CoreTerm::apply(CoreTerm::Bound(3), CoreTerm::Bound(0)),
                        map_values(CoreTerm::Bound(3), CoreTerm::Bound(1)),
                    ),
                    member(domain_type.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1)),
                ),
            ),
            HolDraftProof::ImpIntro {
                premise: reverse_left_inverse,
                body: Box::new(HolDraftProof::ForallElim {
                    proof_forall: Box::new(HolDraftProof::ForallElim {
                        proof_forall: Box::new(HolDraftProof::ImpElim {
                            proof_implication: Box::new(HolDraftProof::ForallElim {
                                proof_forall: Box::new(HolDraftProof::ForallElim {
                                    proof_forall: Box::new(HolDraftProof::TheoremRef {
                                        theorem: cardinality.member_map_reverse,
                                        type_arguments: vec![
                                            CoreType::Parameter(cardinality.domain_parameter),
                                            CoreType::Parameter(cardinality.codomain_parameter),
                                        ],
                                        term_arguments: Vec::new(),
                                    }),
                                    argument: CoreTerm::Bound(3),
                                }),
                                argument: CoreTerm::Bound(2),
                            }),
                            proof_argument: Box::new(HolDraftProof::Hypothesis(0)),
                        }),
                        argument: CoreTerm::Bound(1),
                    }),
                    argument: CoreTerm::Bound(0),
                }),
            },
        )?;
        let left_inverse = CoreTerm::forall(
            domain_type.clone(),
            CoreTerm::equality(
                domain_type.clone(),
                CoreTerm::apply(
                    CoreTerm::Bound(2),
                    CoreTerm::apply(CoreTerm::Bound(3), CoreTerm::Bound(0)),
                ),
                CoreTerm::Bound(0),
            ),
        );
        let right_inverse = CoreTerm::forall(
            codomain_type.clone(),
            CoreTerm::equality(
                codomain_type.clone(),
                CoreTerm::apply(
                    CoreTerm::Bound(3),
                    CoreTerm::apply(CoreTerm::Bound(2), CoreTerm::Bound(0)),
                ),
                CoreTerm::Bound(0),
            ),
        );
        let nodup_map_injective_schema_name =
            format!("{BUILTIN_CARDINALITY_V1_NAMESPACE}.nodup_map_injective_schema");
        let (nodup_map_injective_schema, _) = staged_core.declare_theorem_with_parameters(
            nodup_map_injective_schema_name.clone(),
            vec![cardinality.domain_parameter, cardinality.codomain_parameter],
            vec![
                function_type.clone(),
                inverse_function_type.clone(),
                source_list_type.clone(),
            ],
            CoreTerm::implies(
                left_inverse.clone(),
                CoreTerm::implies(
                    nodup(domain_type.clone(), CoreTerm::Bound(0)),
                    nodup(
                        codomain_type.clone(),
                        map_values(CoreTerm::Bound(2), CoreTerm::Bound(0)),
                    ),
                ),
            ),
            HolDraftProof::ImpIntro {
                premise: left_inverse.clone(),
                body: Box::new(HolDraftProof::ForallElim {
                    proof_forall: Box::new(HolDraftProof::ImpElim {
                        proof_implication: Box::new(HolDraftProof::ForallElim {
                            proof_forall: Box::new(HolDraftProof::ForallElim {
                                proof_forall: Box::new(HolDraftProof::TheoremRef {
                                    theorem: cardinality.nodup_map_injective,
                                    type_arguments: vec![
                                        CoreType::Parameter(cardinality.domain_parameter),
                                        CoreType::Parameter(cardinality.codomain_parameter),
                                    ],
                                    term_arguments: Vec::new(),
                                }),
                                argument: CoreTerm::Bound(2),
                            }),
                            argument: CoreTerm::Bound(1),
                        }),
                        proof_argument: Box::new(HolDraftProof::Hypothesis(0)),
                    }),
                    argument: CoreTerm::Bound(0),
                }),
            },
        )?;
        let mapped_values = map_values(CoreTerm::Bound(2), CoreTerm::Bound(0));
        let source_coverage = CoreTerm::forall(
            domain_type.clone(),
            member(domain_type.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1)),
        );
        let mapped_coverage = CoreTerm::forall(
            codomain_type.clone(),
            member(
                codomain_type.clone(),
                CoreTerm::Bound(0),
                map_values(CoreTerm::Bound(3), CoreTerm::Bound(1)),
            ),
        );
        let map_coverage_surjective_schema_name =
            format!("{BUILTIN_CARDINALITY_V1_NAMESPACE}.map_coverage_surjective_schema");
        let (map_coverage_surjective_schema, _) = staged_core.declare_theorem_with_parameters(
            map_coverage_surjective_schema_name.clone(),
            vec![cardinality.domain_parameter, cardinality.codomain_parameter],
            vec![
                function_type.clone(),
                inverse_function_type.clone(),
                source_list_type.clone(),
            ],
            CoreTerm::implies(
                right_inverse.clone(),
                CoreTerm::implies(source_coverage.clone(), mapped_coverage.clone()),
            ),
            HolDraftProof::ImpIntro {
                premise: right_inverse.clone(),
                body: Box::new(HolDraftProof::ForallElim {
                    proof_forall: Box::new(HolDraftProof::ImpElim {
                        proof_implication: Box::new(HolDraftProof::ForallElim {
                            proof_forall: Box::new(HolDraftProof::ForallElim {
                                proof_forall: Box::new(HolDraftProof::TheoremRef {
                                    theorem: cardinality.map_coverage_surjective,
                                    type_arguments: vec![
                                        CoreType::Parameter(cardinality.domain_parameter),
                                        CoreType::Parameter(cardinality.codomain_parameter),
                                    ],
                                    term_arguments: Vec::new(),
                                }),
                                argument: CoreTerm::Bound(2),
                            }),
                            argument: CoreTerm::Bound(1),
                        }),
                        proof_argument: Box::new(HolDraftProof::Hypothesis(0)),
                    }),
                    argument: CoreTerm::Bound(0),
                }),
            },
        )?;
        let transport_conclusion = CoreTerm::and(
            nodup(codomain_type.clone(), mapped_values.clone()),
            CoreTerm::and(
                CoreTerm::equality(
                    lists.length.natural_type.clone(),
                    lists.length.apply(codomain_type.clone(), mapped_values),
                    lists.length.apply(domain_type.clone(), CoreTerm::Bound(0)),
                ),
                mapped_coverage,
            ),
        );
        let cardinality_transport_schema_name =
            format!("{BUILTIN_CARDINALITY_V1_NAMESPACE}.cardinality_transport_schema");
        let (cardinality_transport_schema, _) = staged_core.declare_theorem_with_parameters(
            cardinality_transport_schema_name.clone(),
            vec![cardinality.domain_parameter, cardinality.codomain_parameter],
            vec![function_type, inverse_function_type, source_list_type],
            CoreTerm::implies(
                left_inverse.clone(),
                CoreTerm::implies(
                    right_inverse.clone(),
                    CoreTerm::implies(
                        nodup(domain_type, CoreTerm::Bound(0)),
                        CoreTerm::implies(source_coverage, transport_conclusion),
                    ),
                ),
            ),
            HolDraftProof::ImpIntro {
                premise: left_inverse,
                body: Box::new(HolDraftProof::ImpIntro {
                    premise: right_inverse,
                    body: Box::new(HolDraftProof::ForallElim {
                        proof_forall: Box::new(HolDraftProof::ImpElim {
                            proof_implication: Box::new(HolDraftProof::ImpElim {
                                proof_implication: Box::new(HolDraftProof::ForallElim {
                                    proof_forall: Box::new(HolDraftProof::ForallElim {
                                        proof_forall: Box::new(HolDraftProof::TheoremRef {
                                            theorem: cardinality.theorem,
                                            type_arguments: vec![
                                                CoreType::Parameter(cardinality.domain_parameter),
                                                CoreType::Parameter(cardinality.codomain_parameter),
                                            ],
                                            term_arguments: Vec::new(),
                                        }),
                                        argument: CoreTerm::Bound(2),
                                    }),
                                    argument: CoreTerm::Bound(1),
                                }),
                                proof_argument: Box::new(HolDraftProof::Hypothesis(1)),
                            }),
                            proof_argument: Box::new(HolDraftProof::Hypothesis(0)),
                        }),
                        argument: CoreTerm::Bound(0),
                    }),
                }),
            },
        )?;
        let definition = |logical_name: &str,
                          core_name: &str,
                          constant: ConstantId|
         -> Result<LibraryDeclaration, SpikeError> {
            let receipt = staged_core
                .definition_receipt(constant)
                .ok_or_else(|| SpikeError {
                    message: format!("checked definition `{core_name}` has no declaration receipt"),
                })?
                .id();
            Ok(LibraryDeclaration {
                logical_name: logical_name.to_string(),
                core_name: core_name.to_string(),
                kind: LibraryDeclarationKind::Definition,
                receipt: Some(receipt),
            })
        };
        let theorem = |logical_name: &str,
                       core_name: &str,
                       theorem: super::theorems::TheoremId|
         -> Result<LibraryDeclaration, SpikeError> {
            let receipt = staged_core
                .theorem_receipt(theorem)
                .ok_or_else(|| SpikeError {
                    message: format!("checked theorem `{core_name}` has no declaration receipt"),
                })?
                .id();
            Ok(LibraryDeclaration {
                logical_name: logical_name.to_string(),
                core_name: core_name.to_string(),
                kind: LibraryDeclarationKind::Theorem,
                receipt: Some(receipt),
            })
        };
        let installed = InstalledCardinalityLibrary {
            record: LibraryPackageRecord {
                id: LibraryPackageId::CardinalityV1,
                provenance: LibraryPackageProvenance {
                    module: BUILTIN_CARDINALITY_V1_MODULE.to_string(),
                    version: 1,
                    source: LibraryPackageSource::Builtin,
                },
                core_namespace: BUILTIN_CARDINALITY_V1_NAMESPACE.to_string(),
                dependencies: vec![LibraryPackageId::ListV1],
                declarations: vec![
                    definition("map", &names.map, cardinality.map)?,
                    theorem("map_nil", &map_nil_schema_name, map_nil_schema)?,
                    theorem("map_cons", &map_cons_schema_name, map_cons_schema)?,
                    theorem("map_length", &names.map_length, cardinality.map_length)?,
                    theorem(
                        "map_length_schema",
                        &map_length_schema_name,
                        map_length_schema,
                    )?,
                    theorem(
                        "member_map_forward",
                        &names.member_map_forward,
                        cardinality.member_map_forward,
                    )?,
                    theorem(
                        "member_map_forward_schema",
                        &member_map_forward_schema_name,
                        member_map_forward_schema,
                    )?,
                    theorem(
                        "member_map_reverse",
                        &names.member_map_reverse,
                        cardinality.member_map_reverse,
                    )?,
                    theorem(
                        "member_map_reverse_schema",
                        &member_map_reverse_schema_name,
                        member_map_reverse_schema,
                    )?,
                    theorem(
                        "nodup_map_injective",
                        &names.nodup_map_injective,
                        cardinality.nodup_map_injective,
                    )?,
                    theorem(
                        "nodup_map_injective_schema",
                        &nodup_map_injective_schema_name,
                        nodup_map_injective_schema,
                    )?,
                    theorem(
                        "map_coverage_surjective",
                        &names.map_coverage_surjective,
                        cardinality.map_coverage_surjective,
                    )?,
                    theorem(
                        "map_coverage_surjective_schema",
                        &map_coverage_surjective_schema_name,
                        map_coverage_surjective_schema,
                    )?,
                    theorem(
                        "cardinality_transport",
                        &names.cardinality_transport,
                        cardinality.theorem,
                    )?,
                    theorem(
                        "cardinality_transport_schema",
                        &cardinality_transport_schema_name,
                        cardinality_transport_schema,
                    )?,
                ],
            },
            cardinality,
            map_nil_schema,
            map_cons_schema,
            map_length_schema,
            member_map_forward_schema,
            member_map_reverse_schema,
            nodup_map_injective_schema,
            map_coverage_surjective_schema,
            cardinality_transport_schema,
        };
        staged_registry.packages.insert(
            LibraryPackageId::CardinalityV1,
            InstalledLibraryPackage::CardinalityV1(installed.clone()),
        );
        *core = staged_core;
        *self = staged_registry;
        Ok(installed)
    }

    /// Install the generic finite-enumeration predicate and its List
    /// dependency as one atomic versioned package closure.
    pub fn install_builtin_finite_v1(
        &mut self,
        core: &mut SpikeElaborator,
        natural_type: CoreType,
        zero: ConstantId,
        successor: ConstantId,
        addition: ConstantId,
    ) -> Result<InstalledFiniteLibrary, SpikeError> {
        let mut staged_core = core.clone();
        let mut staged_registry = self.clone();
        let lists = staged_registry.install_builtin_list_v1(
            &mut staged_core,
            natural_type,
            zero,
            successor,
            addition,
        )?;

        if let Some(installed) = staged_registry.finite_v1().cloned() {
            validate_installed_finite_v1(&staged_core, &installed, &lists)?;
            *core = staged_core;
            *self = staged_registry;
            return Ok(installed);
        }

        let names = FiniteEnumerationNames::under_namespace(BUILTIN_FINITE_V1_NAMESPACE);
        let finite = FiniteEnumerationLibrary::install_named(
            &mut staged_core,
            &lists.lists,
            &lists.length,
            &names,
        )?;
        let has_card_receipt = staged_core
            .definition_receipt(finite.has_card)
            .ok_or_else(|| SpikeError {
                message: format!(
                    "checked definition `{}` has no declaration receipt",
                    names.has_card
                ),
            })?
            .id();
        let has_card_intro_receipt = staged_core
            .theorem_receipt(finite.has_card_intro)
            .ok_or_else(|| SpikeError {
                message: format!(
                    "checked theorem `{}` has no declaration receipt",
                    names.has_card_intro
                ),
            })?
            .id();
        let checked_theorem_receipt = |theorem, name: &str| {
            staged_core
                .theorem_receipt(theorem)
                .map(|receipt| receipt.id())
                .ok_or_else(|| SpikeError {
                    message: format!("checked theorem `{name}` has no declaration receipt"),
                })
        };
        let has_card_nodup_receipt =
            checked_theorem_receipt(finite.has_card_nodup, &names.has_card_nodup)?;
        let has_card_length_receipt =
            checked_theorem_receipt(finite.has_card_length, &names.has_card_length)?;
        let has_card_coverage_receipt =
            checked_theorem_receipt(finite.has_card_coverage, &names.has_card_coverage)?;
        let installed = InstalledFiniteLibrary {
            record: LibraryPackageRecord {
                id: LibraryPackageId::FiniteV1,
                provenance: LibraryPackageProvenance {
                    module: BUILTIN_FINITE_V1_MODULE.to_string(),
                    version: 1,
                    source: LibraryPackageSource::Builtin,
                },
                core_namespace: BUILTIN_FINITE_V1_NAMESPACE.to_string(),
                dependencies: vec![LibraryPackageId::ListV1],
                declarations: vec![
                    LibraryDeclaration {
                        logical_name: "HasCard".to_string(),
                        core_name: names.has_card,
                        kind: LibraryDeclarationKind::Definition,
                        receipt: Some(has_card_receipt),
                    },
                    LibraryDeclaration {
                        logical_name: "has_card_intro".to_string(),
                        core_name: names.has_card_intro,
                        kind: LibraryDeclarationKind::Theorem,
                        receipt: Some(has_card_intro_receipt),
                    },
                    LibraryDeclaration {
                        logical_name: "has_card_nodup".to_string(),
                        core_name: names.has_card_nodup,
                        kind: LibraryDeclarationKind::Theorem,
                        receipt: Some(has_card_nodup_receipt),
                    },
                    LibraryDeclaration {
                        logical_name: "has_card_length".to_string(),
                        core_name: names.has_card_length,
                        kind: LibraryDeclarationKind::Theorem,
                        receipt: Some(has_card_length_receipt),
                    },
                    LibraryDeclaration {
                        logical_name: "has_card_coverage".to_string(),
                        core_name: names.has_card_coverage,
                        kind: LibraryDeclarationKind::Theorem,
                        receipt: Some(has_card_coverage_receipt),
                    },
                ],
            },
            finite,
        };
        staged_registry.packages.insert(
            LibraryPackageId::FiniteV1,
            InstalledLibraryPackage::FiniteV1(installed.clone()),
        );
        *core = staged_core;
        *self = staged_registry;
        Ok(installed)
    }
}

fn validate_installed_list_v1(
    core: &SpikeElaborator,
    installed: &InstalledListLibrary,
) -> Result<(), SpikeError> {
    if installed.record.id != LibraryPackageId::ListV1 || !installed.record.dependencies.is_empty()
    {
        return Err(SpikeError {
            message: format!(
                "invalid package metadata for `{}`",
                LibraryPackageId::ListV1
            ),
        });
    }
    let names = ListLibraryNames::under_namespace(BUILTIN_LIST_V1_NAMESPACE);
    let expected_catalog = [
        (
            "List",
            names.datatype.as_str(),
            LibraryDeclarationKind::Datatype,
        ),
        (
            "nil",
            names.nil.as_str(),
            LibraryDeclarationKind::Constructor,
        ),
        (
            "cons",
            names.cons.as_str(),
            LibraryDeclarationKind::Constructor,
        ),
        (
            "All",
            names.all.as_str(),
            LibraryDeclarationKind::Definition,
        ),
        (
            "Member",
            names.member.as_str(),
            LibraryDeclarationKind::Definition,
        ),
        (
            "Nodup",
            names.nodup.as_str(),
            LibraryDeclarationKind::Definition,
        ),
        (
            "append",
            names.append.as_str(),
            LibraryDeclarationKind::Definition,
        ),
        (
            "length",
            names.length.as_str(),
            LibraryDeclarationKind::Definition,
        ),
        (
            "append_nil_left",
            names.append_nil_left.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "append_cons",
            names.append_cons.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "length_nil",
            names.length_nil.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "length_cons",
            names.length_cons.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "member_nil",
            names.member_nil.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "member_cons",
            names.member_cons.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "nodup_nil",
            names.nodup_nil.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "nodup_cons",
            names.nodup_cons.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "all_nil",
            names.all_nil.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "all_cons",
            names.all_cons.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "append_nil_right",
            names.append_nil_right.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "append_assoc",
            names.append_assoc.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "length_append",
            names.length_append.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "list_induction",
            names.list_induction.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
    ];
    if installed.record.declarations.len() != expected_catalog.len()
        || !installed
            .record
            .declarations
            .iter()
            .zip(expected_catalog)
            .all(|(declaration, (logical_name, core_name, kind))| {
                declaration.logical_name == logical_name
                    && declaration.core_name == core_name
                    && declaration.kind == kind
            })
    {
        return Err(SpikeError {
            message: format!(
                "invalid declaration catalog for package `{}`",
                LibraryPackageId::ListV1
            ),
        });
    }
    let matches = core.types().resolve(&names.datatype) == Some(installed.lists.datatype)
        && core.constants().resolve(&names.nil) == Some(installed.lists.nil)
        && core.constants().resolve(&names.cons) == Some(installed.lists.cons)
        && core.constants().resolve(&names.all) == Some(installed.lists.all)
        && core.constants().resolve(&names.member) == Some(installed.lists.member)
        && core.constants().resolve(&names.nodup) == Some(installed.lists.nodup)
        && core.constants().resolve(&names.append) == Some(installed.lists.append)
        && core.constants().resolve(&names.length) == Some(installed.length.constant)
        && core.theorems().resolve(&names.append_nil_left) == Some(installed.append_nil_left)
        && core.theorems().resolve(&names.append_cons) == Some(installed.append_cons)
        && core.theorems().resolve(&names.length_nil) == Some(installed.length_nil)
        && core.theorems().resolve(&names.length_cons) == Some(installed.length_cons)
        && core.theorems().resolve(&names.member_nil) == Some(installed.member_nil)
        && core.theorems().resolve(&names.member_cons) == Some(installed.member_cons)
        && core.theorems().resolve(&names.nodup_nil) == Some(installed.nodup_nil)
        && core.theorems().resolve(&names.nodup_cons) == Some(installed.nodup_cons)
        && core.theorems().resolve(&names.all_nil) == Some(installed.all_nil)
        && core.theorems().resolve(&names.all_cons) == Some(installed.all_cons)
        && core.theorems().resolve(&names.append_nil_right) == Some(installed.append_nil_right)
        && core.theorems().resolve(&names.append_assoc) == Some(installed.append_assoc)
        && core.theorems().resolve(&names.length_append) == Some(installed.length_append)
        && core.theorems().resolve(&names.list_induction) == Some(installed.list_induction);
    if !matches {
        return Err(SpikeError {
            message: format!(
                "library registry/core mismatch for package `{}`",
                LibraryPackageId::ListV1
            ),
        });
    }
    for declaration in &installed.record.declarations {
        let actual_receipt = match declaration.kind {
            LibraryDeclarationKind::Definition => core
                .constants()
                .resolve(&declaration.core_name)
                .and_then(|constant| core.definition_receipt(constant))
                .map(|receipt| receipt.id()),
            LibraryDeclarationKind::Theorem => core
                .theorems()
                .resolve(&declaration.core_name)
                .and_then(|theorem| core.theorem_receipt(theorem))
                .map(|receipt| receipt.id()),
            LibraryDeclarationKind::Datatype | LibraryDeclarationKind::Constructor => None,
        };
        if actual_receipt != declaration.receipt {
            return Err(SpikeError {
                message: format!(
                    "library receipt mismatch for `{}` in package `{}`",
                    declaration.logical_name,
                    LibraryPackageId::ListV1
                ),
            });
        }
    }
    Ok(())
}

fn validate_installed_cardinality_v1(
    core: &SpikeElaborator,
    installed: &InstalledCardinalityLibrary,
    lists: &InstalledListLibrary,
) -> Result<(), SpikeError> {
    let package = LibraryPackageId::CardinalityV1;
    if installed.record.id != package
        || installed.record.provenance.module != BUILTIN_CARDINALITY_V1_MODULE
        || installed.record.provenance.version != 1
        || installed.record.provenance.source != LibraryPackageSource::Builtin
        || installed.record.core_namespace != BUILTIN_CARDINALITY_V1_NAMESPACE
        || installed.record.dependencies != [LibraryPackageId::ListV1]
        || installed.record.declarations.len() != 15
    {
        return Err(SpikeError {
            message: format!("invalid package metadata for `{package}`"),
        });
    }

    let names = CardinalityTransportNames::under_namespace(BUILTIN_CARDINALITY_V1_NAMESPACE);
    let cardinality = &installed.cardinality;
    let expected_names = [
        (
            "map",
            names.map.as_str(),
            LibraryDeclarationKind::Definition,
        ),
        (
            "map_nil",
            "@library.cardinality.v1.map_nil_schema",
            LibraryDeclarationKind::Theorem,
        ),
        (
            "map_cons",
            "@library.cardinality.v1.map_cons_schema",
            LibraryDeclarationKind::Theorem,
        ),
        (
            "map_length",
            names.map_length.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "map_length_schema",
            "@library.cardinality.v1.map_length_schema",
            LibraryDeclarationKind::Theorem,
        ),
        (
            "member_map_forward",
            names.member_map_forward.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "member_map_forward_schema",
            "@library.cardinality.v1.member_map_forward_schema",
            LibraryDeclarationKind::Theorem,
        ),
        (
            "member_map_reverse",
            names.member_map_reverse.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "member_map_reverse_schema",
            "@library.cardinality.v1.member_map_reverse_schema",
            LibraryDeclarationKind::Theorem,
        ),
        (
            "nodup_map_injective",
            names.nodup_map_injective.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "nodup_map_injective_schema",
            "@library.cardinality.v1.nodup_map_injective_schema",
            LibraryDeclarationKind::Theorem,
        ),
        (
            "map_coverage_surjective",
            names.map_coverage_surjective.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "map_coverage_surjective_schema",
            "@library.cardinality.v1.map_coverage_surjective_schema",
            LibraryDeclarationKind::Theorem,
        ),
        (
            "cardinality_transport",
            names.cardinality_transport.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "cardinality_transport_schema",
            "@library.cardinality.v1.cardinality_transport_schema",
            LibraryDeclarationKind::Theorem,
        ),
    ];
    if !installed
        .record
        .declarations
        .iter()
        .zip(expected_names)
        .all(|(declaration, (logical_name, core_name, kind))| {
            declaration.logical_name == logical_name
                && declaration.core_name == core_name
                && declaration.kind == kind
                && declaration.receipt.is_some()
        })
    {
        return Err(SpikeError {
            message: format!("invalid declaration catalog for package `{package}`"),
        });
    }

    let handles_match = core.constants().resolve(&names.map) == Some(cardinality.map)
        && core
            .theorems()
            .resolve("@library.cardinality.v1.map_nil_schema")
            == Some(installed.map_nil_schema)
        && core
            .theorems()
            .resolve("@library.cardinality.v1.map_cons_schema")
            == Some(installed.map_cons_schema)
        && core.theorems().resolve(&names.map_length) == Some(cardinality.map_length)
        && core
            .theorems()
            .resolve("@library.cardinality.v1.map_length_schema")
            == Some(installed.map_length_schema)
        && core.theorems().resolve(&names.member_map_forward)
            == Some(cardinality.member_map_forward)
        && core
            .theorems()
            .resolve("@library.cardinality.v1.member_map_forward_schema")
            == Some(installed.member_map_forward_schema)
        && core.theorems().resolve(&names.member_map_reverse)
            == Some(cardinality.member_map_reverse)
        && core
            .theorems()
            .resolve("@library.cardinality.v1.member_map_reverse_schema")
            == Some(installed.member_map_reverse_schema)
        && core.theorems().resolve(&names.nodup_map_injective)
            == Some(cardinality.nodup_map_injective)
        && core
            .theorems()
            .resolve("@library.cardinality.v1.nodup_map_injective_schema")
            == Some(installed.nodup_map_injective_schema)
        && core.theorems().resolve(&names.map_coverage_surjective)
            == Some(cardinality.map_coverage_surjective)
        && core
            .theorems()
            .resolve("@library.cardinality.v1.map_coverage_surjective_schema")
            == Some(installed.map_coverage_surjective_schema)
        && core.theorems().resolve(&names.cardinality_transport) == Some(cardinality.theorem)
        && core
            .theorems()
            .resolve("@library.cardinality.v1.cardinality_transport_schema")
            == Some(installed.cardinality_transport_schema);
    if !handles_match {
        return Err(SpikeError {
            message: format!("library registry/core mismatch for package `{package}`"),
        });
    }

    for declaration in &installed.record.declarations {
        let actual_receipt = match declaration.kind {
            LibraryDeclarationKind::Definition => core
                .constants()
                .resolve(&declaration.core_name)
                .and_then(|constant| core.definition_receipt(constant))
                .map(|receipt| receipt.id()),
            LibraryDeclarationKind::Theorem => core
                .theorems()
                .resolve(&declaration.core_name)
                .and_then(|theorem| core.theorem_receipt(theorem))
                .map(|receipt| receipt.id()),
            LibraryDeclarationKind::Datatype | LibraryDeclarationKind::Constructor => None,
        };
        if actual_receipt != declaration.receipt {
            return Err(SpikeError {
                message: format!(
                    "library receipt mismatch for `{}` in package `{package}`",
                    declaration.logical_name
                ),
            });
        }
    }

    let definition_receipt = |constant: ConstantId| {
        core.definition_receipt(constant)
            .map(|receipt| receipt.id())
            .ok_or_else(|| SpikeError {
                message: format!("library dependency receipt missing for package `{package}`"),
            })
    };
    let theorem_receipt = |theorem| {
        core.theorem_receipt(theorem)
            .map(|receipt| receipt.id())
            .ok_or_else(|| SpikeError {
                message: format!("library dependency receipt missing for package `{package}`"),
            })
    };
    let expected_dependencies = BTreeSet::from([
        definition_receipt(lists.lists.member)?,
        definition_receipt(lists.lists.nodup)?,
        definition_receipt(lists.length.constant)?,
        definition_receipt(cardinality.map)?,
        theorem_receipt(cardinality.nodup_map_injective)?,
        theorem_receipt(cardinality.map_length)?,
        theorem_receipt(cardinality.map_coverage_surjective)?,
    ]);
    let final_receipt = core
        .theorem_receipt(cardinality.theorem)
        .ok_or_else(|| SpikeError {
            message: format!("final theorem receipt missing for package `{package}`"),
        })?;
    if final_receipt.proof().direct_dependencies() != &expected_dependencies {
        return Err(SpikeError {
            message: format!("library dependency mismatch for package `{package}`"),
        });
    }
    Ok(())
}

fn validate_installed_finite_v1(
    core: &SpikeElaborator,
    installed: &InstalledFiniteLibrary,
    lists: &InstalledListLibrary,
) -> Result<(), SpikeError> {
    let package = LibraryPackageId::FiniteV1;
    let names = FiniteEnumerationNames::under_namespace(BUILTIN_FINITE_V1_NAMESPACE);
    if installed.record.id != package
        || installed.record.provenance.module != BUILTIN_FINITE_V1_MODULE
        || installed.record.provenance.version != 1
        || installed.record.provenance.source != LibraryPackageSource::Builtin
        || installed.record.core_namespace != BUILTIN_FINITE_V1_NAMESPACE
        || installed.record.dependencies != [LibraryPackageId::ListV1]
        || installed.record.declarations.len() != 5
    {
        return Err(SpikeError {
            message: format!("invalid package metadata for `{package}`"),
        });
    }
    let expected_declarations = [
        (
            "HasCard",
            names.has_card.as_str(),
            LibraryDeclarationKind::Definition,
        ),
        (
            "has_card_intro",
            names.has_card_intro.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "has_card_nodup",
            names.has_card_nodup.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "has_card_length",
            names.has_card_length.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "has_card_coverage",
            names.has_card_coverage.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
    ];
    if !installed
        .record
        .declarations
        .iter()
        .zip(expected_declarations)
        .all(|(declaration, (logical_name, core_name, kind))| {
            declaration.logical_name == logical_name
                && declaration.core_name == core_name
                && declaration.kind == kind
                && declaration.receipt.is_some()
        })
    {
        return Err(SpikeError {
            message: format!("invalid declaration catalog for package `{package}`"),
        });
    }
    if core.constants().resolve(&names.has_card) != Some(installed.finite.has_card)
        || core.theorems().resolve(&names.has_card_intro) != Some(installed.finite.has_card_intro)
        || core.theorems().resolve(&names.has_card_nodup) != Some(installed.finite.has_card_nodup)
        || core.theorems().resolve(&names.has_card_length) != Some(installed.finite.has_card_length)
        || core.theorems().resolve(&names.has_card_coverage)
            != Some(installed.finite.has_card_coverage)
    {
        return Err(SpikeError {
            message: format!("library registry/core mismatch for package `{package}`"),
        });
    }
    let has_card_receipt = core
        .definition_receipt(installed.finite.has_card)
        .ok_or_else(|| SpikeError {
            message: format!("library receipt missing for package `{package}`"),
        })?;
    if installed.record.declarations[0].receipt != Some(has_card_receipt.id()) {
        return Err(SpikeError {
            message: format!("library receipt mismatch for `HasCard` in package `{package}`"),
        });
    }
    let dependency_receipt = |constant: ConstantId| {
        core.definition_receipt(constant)
            .map(|receipt| receipt.id())
            .ok_or_else(|| SpikeError {
                message: format!("library dependency receipt missing for package `{package}`"),
            })
    };
    let member_dependency = dependency_receipt(lists.lists.member)?;
    let nodup_dependency = dependency_receipt(lists.lists.nodup)?;
    let length_dependency = dependency_receipt(lists.length.constant)?;
    let expected_dependencies =
        BTreeSet::from([member_dependency, nodup_dependency, length_dependency]);
    if has_card_receipt.proof().direct_dependencies() != &expected_dependencies {
        return Err(SpikeError {
            message: format!("library dependency mismatch for package `{package}`"),
        });
    }
    let has_card_intro_receipt = core
        .theorem_receipt(installed.finite.has_card_intro)
        .ok_or_else(|| SpikeError {
            message: format!("library theorem receipt missing for package `{package}`"),
        })?;
    let mut expected_intro_dependencies = expected_dependencies;
    expected_intro_dependencies.insert(has_card_receipt.id());
    if installed.record.declarations[1].receipt != Some(has_card_intro_receipt.id())
        || has_card_intro_receipt.proof().direct_dependencies() != &expected_intro_dependencies
    {
        return Err(SpikeError {
            message: format!(
                "library receipt mismatch for `has_card_intro` in package `{package}`"
            ),
        });
    }
    for (index, theorem, logical_name, component_dependency) in [
        (
            2,
            installed.finite.has_card_nodup,
            "has_card_nodup",
            nodup_dependency,
        ),
        (
            3,
            installed.finite.has_card_length,
            "has_card_length",
            length_dependency,
        ),
        (
            4,
            installed.finite.has_card_coverage,
            "has_card_coverage",
            member_dependency,
        ),
    ] {
        let receipt = core.theorem_receipt(theorem).ok_or_else(|| SpikeError {
            message: format!("library theorem receipt missing for `{logical_name}` in `{package}`"),
        })?;
        let expected_projection_dependencies =
            BTreeSet::from([has_card_receipt.id(), component_dependency]);
        if installed.record.declarations[index].receipt != Some(receipt.id())
            || receipt.proof().direct_dependencies() != &expected_projection_dependencies
        {
            return Err(SpikeError {
                message: format!(
                    "library receipt mismatch for `{logical_name}` in package `{package}`: expected {:?}, found {:?}",
                    expected_projection_dependencies,
                    receipt.proof().direct_dependencies(),
                ),
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{EvidenceStatus, ProofFeature, StatementFragment};
    use crate::hol::inductive::{InductiveConstructorSpec, InductiveSpec};
    use crate::hol::prelude::CompatibilityPrelude;
    use crate::hol::terms::{infer_type, CoreTerm, TermContext};

    fn core_with_prelude() -> (SpikeElaborator, CompatibilityPrelude) {
        let mut core = SpikeElaborator::new();
        let prelude = CompatibilityPrelude::install(&mut core).expect("install prelude");
        (core, prelude)
    }

    #[test]
    fn list_v1_install_is_versioned_receipted_fragment_precise_and_idempotent() {
        let (mut core, prelude) = core_with_prelude();
        let mut registry = HolLibraryRegistry::default();
        let installed = registry
            .install_builtin_list_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
                prelude.addition(),
            )
            .expect("install registered List v1");

        assert_eq!(installed.record.id, LibraryPackageId::ListV1);
        assert_eq!(installed.record.id.to_string(), "std/hol/list@1");
        assert_eq!(installed.record.provenance.module, BUILTIN_LIST_V1_MODULE);
        assert_eq!(installed.record.provenance.version, 1);
        assert_eq!(
            installed.record.provenance.source,
            LibraryPackageSource::Builtin
        );
        assert_eq!(installed.record.core_namespace, BUILTIN_LIST_V1_NAMESPACE);
        assert_eq!(installed.record.declarations.len(), 22);
        assert_eq!(
            installed
                .record
                .declarations
                .iter()
                .filter(|declaration| declaration.receipt.is_some())
                .count(),
            19
        );
        let member_receipt = installed
            .record
            .declarations
            .iter()
            .find(|declaration| declaration.logical_name == "Member")
            .and_then(|declaration| declaration.receipt)
            .expect("Member definition receipt");
        assert_eq!(
            registry.receipt_name(member_receipt).as_deref(),
            Some("std/hol/list@1::Member")
        );
        let append_nil_left_receipt = core
            .theorem_receipt(installed.append_nil_left)
            .expect("append_nil_left theorem receipt");
        assert_eq!(
            registry
                .receipt_name(append_nil_left_receipt.id())
                .as_deref(),
            Some("std/hol/list@1::append_nil_left")
        );
        assert_eq!(append_nil_left_receipt.status(), EvidenceStatus::Checked);
        let append_receipt = core
            .definition_receipt(installed.lists.append)
            .expect("append definition receipt");
        assert!(append_nil_left_receipt
            .proof()
            .direct_dependencies()
            .contains(&append_receipt.id()));
        for (theorem, logical_name, definition) in [
            (installed.append_cons, "append_cons", installed.lists.append),
            (
                installed.length_nil,
                "length_nil",
                installed.length.constant,
            ),
            (
                installed.length_cons,
                "length_cons",
                installed.length.constant,
            ),
            (installed.member_nil, "member_nil", installed.lists.member),
            (installed.member_cons, "member_cons", installed.lists.member),
            (installed.nodup_nil, "nodup_nil", installed.lists.nodup),
            (installed.nodup_cons, "nodup_cons", installed.lists.nodup),
            (installed.all_nil, "all_nil", installed.lists.all),
            (installed.all_cons, "all_cons", installed.lists.all),
            (
                installed.append_nil_right,
                "append_nil_right",
                installed.lists.append,
            ),
            (
                installed.append_assoc,
                "append_assoc",
                installed.lists.append,
            ),
        ] {
            let theorem_receipt = core
                .theorem_receipt(theorem)
                .unwrap_or_else(|| panic!("{logical_name} theorem receipt"));
            assert_eq!(
                registry.receipt_name(theorem_receipt.id()).as_deref(),
                Some(format!("std/hol/list@1::{logical_name}").as_str())
            );
            let definition_receipt = core
                .definition_receipt(definition)
                .unwrap_or_else(|| panic!("{logical_name} definition receipt"));
            assert!(theorem_receipt
                .proof()
                .direct_dependencies()
                .contains(&definition_receipt.id()));
        }
        assert!(core
            .theorem_receipt(installed.append_nil_right)
            .expect("append_nil_right theorem receipt")
            .proof()
            .transitive_features()
            .contains(&ProofFeature::Induction));
        assert!(core
            .theorem_receipt(installed.append_assoc)
            .expect("append_assoc theorem receipt")
            .proof()
            .transitive_features()
            .contains(&ProofFeature::Induction));
        let length_append_receipt = core
            .theorem_receipt(installed.length_append)
            .expect("length_append theorem receipt");
        assert_eq!(
            registry.receipt_name(length_append_receipt.id()).as_deref(),
            Some("std/hol/list@1::length_append")
        );
        assert!(length_append_receipt
            .proof()
            .transitive_features()
            .contains(&ProofFeature::Induction));
        for definition in [installed.lists.append, installed.length.constant] {
            let definition_receipt = core
                .definition_receipt(definition)
                .expect("length_append definition receipt");
            assert!(length_append_receipt
                .proof()
                .direct_dependencies()
                .contains(&definition_receipt.id()));
        }
        let addition_receipt = core
            .definition_receipt(prelude.addition())
            .expect("checked Nat addition receipt");
        assert!(length_append_receipt
            .proof()
            .direct_dependencies()
            .contains(&addition_receipt.id()));
        let list_induction_receipt = core
            .theorem_receipt(installed.list_induction)
            .expect("list_induction theorem receipt");
        assert_eq!(
            registry
                .receipt_name(list_induction_receipt.id())
                .as_deref(),
            Some("std/hol/list@1::list_induction")
        );
        assert!(list_induction_receipt
            .proof()
            .transitive_features()
            .contains(&ProofFeature::Induction));
        assert!(installed
            .record
            .declarations
            .iter()
            .all(|declaration| declaration.core_name.starts_with(BUILTIN_LIST_V1_NAMESPACE)));
        assert_eq!(
            core.types().resolve("@library.list.v1.List"),
            Some(installed.lists.datatype)
        );

        let nat = prelude.nat_type();
        let nil_nat = installed.lists.nil_term(nat.clone());
        assert_eq!(
            infer_type(
                core.types(),
                core.constants(),
                &TermContext::new(),
                &nil_nat,
            )
            .expect("registered nil type"),
            installed.lists.list_type(nat.clone())
        );
        let open_membership = installed.lists.member_term(
            nat.clone(),
            CoreTerm::Constant(prelude.zero()),
            CoreTerm::Bound(0),
        );
        assert_eq!(
            core.classify_with_parameters(&[installed.lists.list_type(nat)], &open_membership,)
                .expect("registered Nat membership fragment"),
            StatementFragment::FirstOrderInductive
        );
        let higher_order_all =
            installed
                .lists
                .all_term(CoreType::Prop, CoreTerm::Bound(0), CoreTerm::Bound(1));
        assert_eq!(
            core.classify_with_parameters(
                &[
                    installed.lists.list_type(CoreType::Prop),
                    CoreType::arrow(CoreType::Prop, CoreType::Prop),
                ],
                &higher_order_all,
            )
            .expect("registered higher-order List instance"),
            StatementFragment::HigherOrder
        );

        let after_first_install = (core.clone(), registry.clone());
        let repeated = registry
            .install_builtin_list_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
                prelude.addition(),
            )
            .expect("repeat install is idempotent");
        assert_eq!(repeated, installed);
        assert_eq!((core.clone(), registry.clone()), after_first_install);

        let other_nat_id = core
            .declare_base_type("OtherNat", true)
            .expect("declare alternate Nat interface");
        let other_nat = CoreType::constructor(other_nat_id, Vec::new());
        let other_zero = core
            .declare_constant("other_zero", other_nat.clone())
            .expect("declare alternate zero");
        let other_successor = core
            .declare_constant(
                "other_successor",
                CoreType::arrow(other_nat.clone(), other_nat.clone()),
            )
            .expect("declare alternate successor");
        let before_rebind = (core.clone(), registry.clone());
        let rebind_error = registry
            .install_builtin_list_v1(
                &mut core,
                other_nat,
                other_zero,
                other_successor,
                prelude.addition(),
            )
            .expect_err("a package cannot be rebound to a different Nat interface");
        assert!(rebind_error.message.contains("different Nat interface"));
        assert_eq!((core.clone(), registry.clone()), before_rebind);

        let mut detached_registry = registry.clone();
        let (mut detached_core, detached_prelude) = core_with_prelude();
        let before_detached = (detached_core.clone(), detached_registry.clone());
        let detached_error = detached_registry
            .install_builtin_list_v1(
                &mut detached_core,
                detached_prelude.nat_type(),
                detached_prelude.zero(),
                detached_prelude.successor(),
                detached_prelude.addition(),
            )
            .expect_err("registry handles cannot be reused with another core");
        assert!(detached_error.message.contains("registry/core mismatch"));
        assert_eq!((detached_core, detached_registry), before_detached);
    }

    #[test]
    fn cardinality_v1_install_is_versioned_dependency_bound_and_idempotent() {
        let (mut core, prelude) = core_with_prelude();
        let mut registry = HolLibraryRegistry::default();
        let installed = registry
            .install_builtin_cardinality_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
                prelude.addition(),
            )
            .expect("install registered cardinality v1");

        assert_eq!(registry.packages().len(), 2);
        assert!(registry.list_v1().is_some());
        assert_eq!(registry.cardinality_v1(), Some(&installed));
        assert_eq!(installed.record.id, LibraryPackageId::CardinalityV1);
        assert_eq!(installed.record.id.to_string(), "std/hol/cardinality@1");
        assert_eq!(
            installed.record.provenance.module,
            BUILTIN_CARDINALITY_V1_MODULE
        );
        assert_eq!(installed.record.provenance.version, 1);
        assert_eq!(
            installed.record.provenance.source,
            LibraryPackageSource::Builtin
        );
        assert_eq!(
            installed.record.core_namespace,
            BUILTIN_CARDINALITY_V1_NAMESPACE
        );
        assert_eq!(installed.record.dependencies, [LibraryPackageId::ListV1]);
        assert_eq!(installed.record.declarations.len(), 15);
        assert!(installed
            .record
            .declarations
            .iter()
            .all(|declaration| declaration.receipt.is_some()
                && declaration
                    .core_name
                    .starts_with(BUILTIN_CARDINALITY_V1_NAMESPACE)));
        assert_eq!(
            installed
                .record
                .declarations
                .iter()
                .filter(|declaration| declaration.kind == LibraryDeclarationKind::Definition)
                .count(),
            1
        );
        assert_eq!(
            installed
                .record
                .declarations
                .iter()
                .filter(|declaration| declaration.kind == LibraryDeclarationKind::Theorem)
                .count(),
            14
        );
        for (theorem, stable_name) in [
            (installed.map_nil_schema, "std/hol/cardinality@1::map_nil"),
            (installed.map_cons_schema, "std/hol/cardinality@1::map_cons"),
        ] {
            let receipt = core
                .theorem_receipt(theorem)
                .expect("registered map computation receipt");
            assert_eq!(
                receipt.proof().statement_fragment(),
                StatementFragment::HigherOrder
            );
            assert_eq!(
                registry.receipt_name(receipt.id()).as_deref(),
                Some(stable_name)
            );
        }
        for (theorem, stable_name) in [
            (
                installed.member_map_forward_schema,
                "std/hol/cardinality@1::member_map_forward_schema",
            ),
            (
                installed.member_map_reverse_schema,
                "std/hol/cardinality@1::member_map_reverse_schema",
            ),
            (
                installed.nodup_map_injective_schema,
                "std/hol/cardinality@1::nodup_map_injective_schema",
            ),
            (
                installed.map_coverage_surjective_schema,
                "std/hol/cardinality@1::map_coverage_surjective_schema",
            ),
        ] {
            let receipt = core
                .theorem_receipt(theorem)
                .expect("registered cardinality supporting source template receipt");
            assert_eq!(
                receipt.proof().statement_fragment(),
                StatementFragment::HigherOrder
            );
            assert_eq!(
                registry.receipt_name(receipt.id()).as_deref(),
                Some(stable_name)
            );
        }

        let map_length_schema_receipt = core
            .theorem_receipt(installed.map_length_schema)
            .expect("registered map_length source template receipt");
        assert_eq!(
            map_length_schema_receipt.proof().statement_fragment(),
            StatementFragment::HigherOrder
        );
        assert_eq!(
            registry
                .receipt_name(map_length_schema_receipt.id())
                .as_deref(),
            Some("std/hol/cardinality@1::map_length_schema")
        );
        let map_length_schema_dependencies = map_length_schema_receipt
            .proof()
            .direct_dependencies()
            .iter()
            .map(|dependency| {
                registry
                    .receipt_name(*dependency)
                    .expect("every map_length template dependency belongs to a package")
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            map_length_schema_dependencies,
            BTreeSet::from([
                "std/hol/cardinality@1::map".to_string(),
                "std/hol/cardinality@1::map_length".to_string(),
                "std/hol/list@1::length".to_string(),
            ])
        );

        let transport_schema_receipt = core
            .theorem_receipt(installed.cardinality_transport_schema)
            .expect("registered cardinality transport source template receipt");
        assert_eq!(
            transport_schema_receipt.proof().statement_fragment(),
            StatementFragment::HigherOrder
        );
        assert_eq!(
            registry
                .receipt_name(transport_schema_receipt.id())
                .as_deref(),
            Some("std/hol/cardinality@1::cardinality_transport_schema")
        );
        let transport_schema_dependencies = transport_schema_receipt
            .proof()
            .direct_dependencies()
            .iter()
            .map(|dependency| {
                registry
                    .receipt_name(*dependency)
                    .expect("every transport template dependency belongs to a package")
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            transport_schema_dependencies,
            BTreeSet::from([
                "std/hol/cardinality@1::cardinality_transport".to_string(),
                "std/hol/cardinality@1::map".to_string(),
                "std/hol/list@1::Member".to_string(),
                "std/hol/list@1::Nodup".to_string(),
                "std/hol/list@1::length".to_string(),
            ])
        );

        let final_receipt = core
            .theorem_receipt(installed.cardinality.theorem)
            .expect("registered transport receipt");
        assert_eq!(
            final_receipt.proof().statement_fragment(),
            StatementFragment::HigherOrder
        );
        assert_eq!(
            final_receipt.proof().required_fragment(),
            StatementFragment::HigherOrder
        );
        assert!(final_receipt.proof().axiom_dependencies().is_empty());
        assert!(final_receipt.proof().incomplete_dependencies().is_empty());
        assert_eq!(
            registry.receipt_name(final_receipt.id()).as_deref(),
            Some("std/hol/cardinality@1::cardinality_transport")
        );
        let dependency_names = final_receipt
            .proof()
            .direct_dependencies()
            .iter()
            .map(|dependency| {
                registry
                    .receipt_name(*dependency)
                    .expect("every transport dependency belongs to a package")
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            dependency_names,
            BTreeSet::from([
                "std/hol/cardinality@1::map".to_string(),
                "std/hol/cardinality@1::map_coverage_surjective".to_string(),
                "std/hol/cardinality@1::map_length".to_string(),
                "std/hol/cardinality@1::nodup_map_injective".to_string(),
                "std/hol/list@1::Member".to_string(),
                "std/hol/list@1::Nodup".to_string(),
                "std/hol/list@1::length".to_string(),
            ])
        );

        let after_first_install = (core.clone(), registry.clone());
        let repeated = registry
            .install_builtin_cardinality_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
                prelude.addition(),
            )
            .expect("repeat install is idempotent");
        assert_eq!(repeated, installed);
        assert_eq!((core.clone(), registry.clone()), after_first_install);

        let mut detached_registry = registry.clone();
        let (mut detached_core, detached_prelude) = core_with_prelude();
        let before_detached = (detached_core.clone(), detached_registry.clone());
        let detached_error = detached_registry
            .install_builtin_cardinality_v1(
                &mut detached_core,
                detached_prelude.nat_type(),
                detached_prelude.zero(),
                detached_prelude.successor(),
                detached_prelude.addition(),
            )
            .expect_err("package handles cannot be reused with another core");
        assert!(detached_error.message.contains("registry/core mismatch"));
        assert_eq!((detached_core, detached_registry), before_detached);
    }

    #[test]
    fn finite_v1_owns_has_card_but_not_client_enumeration_receipts() {
        let (mut core, prelude) = core_with_prelude();
        let mut registry = HolLibraryRegistry::default();
        let installed = registry
            .install_builtin_finite_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
                prelude.addition(),
            )
            .expect("install registered finite v1");

        assert_eq!(registry.packages().len(), 2);
        assert!(registry.list_v1().is_some());
        assert_eq!(registry.finite_v1(), Some(&installed));
        assert_eq!(installed.record.id, LibraryPackageId::FiniteV1);
        assert_eq!(installed.record.id.to_string(), "std/hol/finite@1");
        assert_eq!(installed.record.provenance.module, BUILTIN_FINITE_V1_MODULE);
        assert_eq!(installed.record.provenance.version, 1);
        assert_eq!(
            installed.record.provenance.source,
            LibraryPackageSource::Builtin
        );
        assert_eq!(installed.record.core_namespace, BUILTIN_FINITE_V1_NAMESPACE);
        assert_eq!(installed.record.dependencies, [LibraryPackageId::ListV1]);
        assert_eq!(installed.record.declarations.len(), 5);
        let has_card = &installed.record.declarations[0];
        assert_eq!(has_card.logical_name, "HasCard");
        assert_eq!(has_card.kind, LibraryDeclarationKind::Definition);
        assert_eq!(
            registry.receipt_name(has_card.receipt.expect("HasCard receipt")),
            Some("std/hol/finite@1::HasCard".to_string())
        );
        let dependency_names = core
            .definition_receipt(installed.finite.has_card)
            .expect("registered HasCard receipt")
            .proof()
            .direct_dependencies()
            .iter()
            .map(|dependency| {
                registry
                    .receipt_name(*dependency)
                    .expect("every HasCard dependency belongs to List v1")
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            dependency_names,
            BTreeSet::from([
                "std/hol/list@1::Member".to_string(),
                "std/hol/list@1::Nodup".to_string(),
                "std/hol/list@1::length".to_string(),
            ])
        );
        let has_card_intro = &installed.record.declarations[1];
        assert_eq!(has_card_intro.logical_name, "has_card_intro");
        assert_eq!(has_card_intro.kind, LibraryDeclarationKind::Theorem);
        assert_eq!(
            registry.receipt_name(
                has_card_intro
                    .receipt
                    .expect("has_card_intro theorem receipt")
            ),
            Some("std/hol/finite@1::has_card_intro".to_string())
        );
        let intro_receipt = core
            .theorem_receipt(installed.finite.has_card_intro)
            .expect("registered has_card_intro receipt");
        assert_eq!(intro_receipt.status(), EvidenceStatus::Checked);
        // The stored theorem is generic over an unrestricted HOL type. A
        // concrete first-order source application is classified again at its
        // instance and can remain `fol+induction`.
        assert_eq!(
            intro_receipt.proof().required_fragment(),
            StatementFragment::HigherOrder
        );
        assert!(intro_receipt.proof().axiom_dependencies().is_empty());
        let intro_dependency_names = intro_receipt
            .proof()
            .direct_dependencies()
            .iter()
            .map(|dependency| {
                registry
                    .receipt_name(*dependency)
                    .expect("every has_card_intro dependency belongs to a package")
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            intro_dependency_names,
            BTreeSet::from([
                "std/hol/finite@1::HasCard".to_string(),
                "std/hol/list@1::Member".to_string(),
                "std/hol/list@1::Nodup".to_string(),
                "std/hol/list@1::length".to_string(),
            ])
        );
        for (index, logical_name, theorem) in [
            (2, "has_card_nodup", installed.finite.has_card_nodup),
            (3, "has_card_length", installed.finite.has_card_length),
            (4, "has_card_coverage", installed.finite.has_card_coverage),
        ] {
            let declaration = &installed.record.declarations[index];
            assert_eq!(declaration.logical_name, logical_name);
            assert_eq!(declaration.kind, LibraryDeclarationKind::Theorem);
            assert_eq!(
                registry.receipt_name(declaration.receipt.expect("projection receipt")),
                Some(format!("std/hol/finite@1::{logical_name}"))
            );
            let receipt = core
                .theorem_receipt(theorem)
                .expect("checked HasCard projection receipt");
            assert_eq!(receipt.status(), EvidenceStatus::Checked);
            assert_eq!(
                receipt.proof().required_fragment(),
                StatementFragment::HigherOrder
            );
            assert!(receipt.proof().axiom_dependencies().is_empty());
        }

        let traffic = core
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
        let evidence = installed
            .finite
            .declare_nullary_inductive(&mut core, "traffic_has_card", traffic)
            .expect("generate client enumeration evidence");
        assert_eq!(
            evidence.receipt.proof().required_fragment(),
            StatementFragment::FirstOrderInductive
        );
        assert_eq!(registry.receipt_name(evidence.receipt.id()), None);

        let after_first_install = (core.clone(), registry.clone());
        let repeated = registry
            .install_builtin_finite_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
                prelude.addition(),
            )
            .expect("repeat install is idempotent");
        assert_eq!(repeated, installed);
        assert_eq!((core.clone(), registry.clone()), after_first_install);

        let mut detached_registry = registry.clone();
        let (mut detached_core, detached_prelude) = core_with_prelude();
        let before_detached = (detached_core.clone(), detached_registry.clone());
        let detached_error = detached_registry
            .install_builtin_finite_v1(
                &mut detached_core,
                detached_prelude.nat_type(),
                detached_prelude.zero(),
                detached_prelude.successor(),
                detached_prelude.addition(),
            )
            .expect_err("package handles cannot be reused with another core");
        assert!(detached_error.message.contains("registry/core mismatch"));
        assert_eq!((detached_core, detached_registry), before_detached);
    }

    #[test]
    fn list_v1_install_rolls_back_core_and_metadata_after_a_late_collision() {
        let (mut core, prelude) = core_with_prelude();
        let names = ListLibraryNames::under_namespace(BUILTIN_LIST_V1_NAMESPACE);
        core.declare_theorem(
            names.list_induction.clone(),
            Vec::new(),
            CoreTerm::Truth,
            HolDraftProof::TruthIntro,
        )
        .expect("reserve the final package theorem name");
        let mut registry = HolLibraryRegistry::default();
        let before = (core.clone(), registry.clone());

        let error = registry
            .install_builtin_list_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
                prelude.addition(),
            )
            .expect_err("late collision must reject the package");
        assert!(error.message.contains(&names.list_induction));
        assert_eq!((core, registry), before);
    }

    #[test]
    fn cardinality_v1_rolls_back_its_new_list_dependency_after_a_late_collision() {
        let (mut core, prelude) = core_with_prelude();
        let names = CardinalityTransportNames::under_namespace(BUILTIN_CARDINALITY_V1_NAMESPACE);
        core.declare_theorem(
            names.member_map_reverse.clone(),
            Vec::new(),
            CoreTerm::Truth,
            super::super::proofs::HolDraftProof::TruthIntro,
        )
        .expect("reserve a name reached after List and earlier cardinality declarations");
        let mut registry = HolLibraryRegistry::default();
        let before = (core.clone(), registry.clone());

        let error = registry
            .install_builtin_cardinality_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
                prelude.addition(),
            )
            .expect_err("late cardinality collision must reject the dependency closure");
        assert!(error.message.contains(&names.member_map_reverse));
        assert_eq!((core, registry), before);
    }

    #[test]
    fn finite_v1_rolls_back_its_new_list_dependency_after_a_late_collision() {
        let (mut core, prelude) = core_with_prelude();
        let names = FiniteEnumerationNames::under_namespace(BUILTIN_FINITE_V1_NAMESPACE);
        core.declare_theorem(
            names.has_card_intro.clone(),
            Vec::new(),
            CoreTerm::Truth,
            HolDraftProof::TruthIntro,
        )
        .expect("reserve has_card_intro after the staged definition and List dependency");
        let mut registry = HolLibraryRegistry::default();
        let before = (core.clone(), registry.clone());

        let error = registry
            .install_builtin_finite_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
                prelude.addition(),
            )
            .expect_err("finite collision must reject the dependency closure");
        assert!(error.message.contains(&names.has_card_intro));
        assert_eq!((core, registry), before);
    }
}
