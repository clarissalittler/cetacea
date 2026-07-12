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
use super::terms::{ConstantId, CoreTerm};
use super::theorems::TheoremId;
use super::types::CoreType;

pub const BUILTIN_LIST_V1_MODULE: &str = "std/hol/list";
pub const BUILTIN_LIST_V1_NAMESPACE: &str = "@library.list.v1";
pub const BUILTIN_CARDINALITY_V1_MODULE: &str = "std/hol/cardinality";
pub const BUILTIN_CARDINALITY_V1_NAMESPACE: &str = "@library.cardinality.v1";
pub const BUILTIN_FINITE_V1_MODULE: &str = "std/hol/finite";
pub const BUILTIN_FINITE_V1_NAMESPACE: &str = "@library.finite.v1";

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
    pub append_nil_left: TheoremId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstalledCardinalityLibrary {
    pub record: LibraryPackageRecord,
    pub cardinality: CardinalityTransportLibrary,
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
    ) -> Result<InstalledListLibrary, SpikeError> {
        if let Some(installed) = self.list_v1() {
            validate_installed_list_v1(core, installed)?;
            if installed.length.natural_type != natural_type
                || installed.length.zero != zero
                || installed.length.successor != successor
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
                lists.nil_term(element_type),
                CoreTerm::Bound(0),
            ),
            CoreTerm::Bound(0),
        );
        let (append_nil_left, append_nil_left_receipt) = staged_core
            .declare_theorem_with_parameters(
                names.append_nil_left.clone(),
                vec![lists.element_parameter],
                vec![list_type],
                append_nil_left_statement,
                HolDraftProof::EqualityRefl(CoreTerm::Bound(0)),
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
                ],
            },
            lists,
            length,
            append_nil_left,
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
    ) -> Result<InstalledCardinalityLibrary, SpikeError> {
        let mut staged_core = core.clone();
        let mut staged_registry = self.clone();
        let lists = staged_registry.install_builtin_list_v1(
            &mut staged_core,
            natural_type,
            zero,
            successor,
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
                    theorem("map_length", &names.map_length, cardinality.map_length)?,
                    theorem(
                        "member_map_forward",
                        &names.member_map_forward,
                        cardinality.member_map_forward,
                    )?,
                    theorem(
                        "member_map_reverse",
                        &names.member_map_reverse,
                        cardinality.member_map_reverse,
                    )?,
                    theorem(
                        "nodup_map_injective",
                        &names.nodup_map_injective,
                        cardinality.nodup_map_injective,
                    )?,
                    theorem(
                        "map_coverage_surjective",
                        &names.map_coverage_surjective,
                        cardinality.map_coverage_surjective,
                    )?,
                    theorem(
                        "cardinality_transport",
                        &names.cardinality_transport,
                        cardinality.theorem,
                    )?,
                ],
            },
            cardinality,
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
    ) -> Result<InstalledFiniteLibrary, SpikeError> {
        let mut staged_core = core.clone();
        let mut staged_registry = self.clone();
        let lists = staged_registry.install_builtin_list_v1(
            &mut staged_core,
            natural_type,
            zero,
            successor,
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
        let receipt = staged_core
            .definition_receipt(finite.has_card)
            .ok_or_else(|| SpikeError {
                message: format!(
                    "checked definition `{}` has no declaration receipt",
                    names.has_card
                ),
            })?
            .id();
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
                declarations: vec![LibraryDeclaration {
                    logical_name: "HasCard".to_string(),
                    core_name: names.has_card,
                    kind: LibraryDeclarationKind::Definition,
                    receipt: Some(receipt),
                }],
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
    let matches = core.types().resolve(&names.datatype) == Some(installed.lists.datatype)
        && core.constants().resolve(&names.nil) == Some(installed.lists.nil)
        && core.constants().resolve(&names.cons) == Some(installed.lists.cons)
        && core.constants().resolve(&names.all) == Some(installed.lists.all)
        && core.constants().resolve(&names.member) == Some(installed.lists.member)
        && core.constants().resolve(&names.nodup) == Some(installed.lists.nodup)
        && core.constants().resolve(&names.append) == Some(installed.lists.append)
        && core.constants().resolve(&names.length) == Some(installed.length.constant)
        && core.theorems().resolve(&names.append_nil_left) == Some(installed.append_nil_left);
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
        || installed.record.declarations.len() != 7
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
            "map_length",
            names.map_length.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "member_map_forward",
            names.member_map_forward.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "member_map_reverse",
            names.member_map_reverse.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "nodup_map_injective",
            names.nodup_map_injective.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "map_coverage_surjective",
            names.map_coverage_surjective.as_str(),
            LibraryDeclarationKind::Theorem,
        ),
        (
            "cardinality_transport",
            names.cardinality_transport.as_str(),
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
        && core.theorems().resolve(&names.map_length) == Some(cardinality.map_length)
        && core.theorems().resolve(&names.member_map_forward)
            == Some(cardinality.member_map_forward)
        && core.theorems().resolve(&names.member_map_reverse)
            == Some(cardinality.member_map_reverse)
        && core.theorems().resolve(&names.nodup_map_injective)
            == Some(cardinality.nodup_map_injective)
        && core.theorems().resolve(&names.map_coverage_surjective)
            == Some(cardinality.map_coverage_surjective)
        && core.theorems().resolve(&names.cardinality_transport) == Some(cardinality.theorem);
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
        || installed.record.declarations.len() != 1
    {
        return Err(SpikeError {
            message: format!("invalid package metadata for `{package}`"),
        });
    }
    let declaration = &installed.record.declarations[0];
    if declaration.logical_name != "HasCard"
        || declaration.core_name != names.has_card
        || declaration.kind != LibraryDeclarationKind::Definition
        || declaration.receipt.is_none()
    {
        return Err(SpikeError {
            message: format!("invalid declaration catalog for package `{package}`"),
        });
    }
    if core.constants().resolve(&names.has_card) != Some(installed.finite.has_card) {
        return Err(SpikeError {
            message: format!("library registry/core mismatch for package `{package}`"),
        });
    }
    let receipt = core
        .definition_receipt(installed.finite.has_card)
        .ok_or_else(|| SpikeError {
            message: format!("library receipt missing for package `{package}`"),
        })?;
    if declaration.receipt != Some(receipt.id()) {
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
    let expected_dependencies = BTreeSet::from([
        dependency_receipt(lists.lists.member)?,
        dependency_receipt(lists.lists.nodup)?,
        dependency_receipt(lists.length.constant)?,
    ]);
    if receipt.proof().direct_dependencies() != &expected_dependencies {
        return Err(SpikeError {
            message: format!("library dependency mismatch for package `{package}`"),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::{EvidenceStatus, StatementFragment};
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
        assert_eq!(installed.record.declarations.len(), 9);
        assert_eq!(
            installed
                .record
                .declarations
                .iter()
                .filter(|declaration| declaration.receipt.is_some())
                .count(),
            6
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
            .install_builtin_list_v1(&mut core, other_nat, other_zero, other_successor)
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
        assert_eq!(installed.record.declarations.len(), 7);
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
            6
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
        assert_eq!(installed.record.declarations.len(), 1);
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
            names.append_nil_left.clone(),
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
            )
            .expect_err("late collision must reject the package");
        assert!(error.message.contains(&names.append_nil_left));
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
            )
            .expect_err("late cardinality collision must reject the dependency closure");
        assert!(error.message.contains(&names.member_map_reverse));
        assert_eq!((core, registry), before);
    }

    #[test]
    fn finite_v1_rolls_back_its_new_list_dependency_after_a_late_collision() {
        let (mut core, prelude) = core_with_prelude();
        let names = FiniteEnumerationNames::under_namespace(BUILTIN_FINITE_V1_NAMESPACE);
        core.declare_constant(names.has_card.clone(), CoreType::Prop)
            .expect("reserve HasCard after the staged List dependency");
        let mut registry = HolLibraryRegistry::default();
        let before = (core.clone(), registry.clone());

        let error = registry
            .install_builtin_finite_v1(
                &mut core,
                prelude.nat_type(),
                prelude.zero(),
                prelude.successor(),
            )
            .expect_err("finite collision must reject the dependency closure");
        assert!(error.message.contains(&names.has_card));
        assert_eq!((core, registry), before);
    }
}
