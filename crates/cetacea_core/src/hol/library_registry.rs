//! Versioned installation registry for checked HOL library packages.
//!
//! The registry is deliberately independent of surface syntax. It gives the
//! compatibility driver and a future native HOL frontend one atomic package
//! mechanism, with logical provenance and stable reserved core names. Surface
//! imports can later bind aliases to these records without reinstalling or
//! duplicating kernel declarations.

use std::collections::BTreeMap;
use std::fmt;

use super::fragments::DeclarationId;
use super::library::{ListLength, ListLibrary, ListLibraryNames};
use super::spike::{SpikeElaborator, SpikeError};
use super::terms::ConstantId;
use super::types::CoreType;

pub const BUILTIN_LIST_V1_MODULE: &str = "std/hol/list";
pub const BUILTIN_LIST_V1_NAMESPACE: &str = "@library.list.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LibraryPackageId {
    ListV1,
}

impl fmt::Display for LibraryPackageId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ListV1 => write!(f, "{BUILTIN_LIST_V1_MODULE}@1"),
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
    pub declarations: Vec<LibraryDeclaration>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstalledListLibrary {
    pub record: LibraryPackageRecord,
    pub lists: ListLibrary,
    pub length: ListLength,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstalledLibraryPackage {
    ListV1(InstalledListLibrary),
}

impl InstalledLibraryPackage {
    pub fn record(&self) -> &LibraryPackageRecord {
        match self {
            Self::ListV1(installed) => &installed.record,
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
            None => None,
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
                ],
            },
            lists,
            length,
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
}

fn validate_installed_list_v1(
    core: &SpikeElaborator,
    installed: &InstalledListLibrary,
) -> Result<(), SpikeError> {
    let names = ListLibraryNames::under_namespace(BUILTIN_LIST_V1_NAMESPACE);
    let matches = core.types().resolve(&names.datatype) == Some(installed.lists.datatype)
        && core.constants().resolve(&names.nil) == Some(installed.lists.nil)
        && core.constants().resolve(&names.cons) == Some(installed.lists.cons)
        && core.constants().resolve(&names.all) == Some(installed.lists.all)
        && core.constants().resolve(&names.member) == Some(installed.lists.member)
        && core.constants().resolve(&names.nodup) == Some(installed.lists.nodup)
        && core.constants().resolve(&names.append) == Some(installed.lists.append)
        && core.constants().resolve(&names.length) == Some(installed.length.constant);
    if !matches {
        return Err(SpikeError {
            message: format!(
                "library registry/core mismatch for package `{}`",
                LibraryPackageId::ListV1
            ),
        });
    }
    for declaration in &installed.record.declarations {
        let Some(expected_receipt) = declaration.receipt else {
            continue;
        };
        let Some(constant) = core.constants().resolve(&declaration.core_name) else {
            return Err(SpikeError {
                message: format!(
                    "library registry/core mismatch for package `{}`",
                    LibraryPackageId::ListV1
                ),
            });
        };
        if core
            .definition_receipt(constant)
            .map(|receipt| receipt.id())
            != Some(expected_receipt)
        {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::fragments::StatementFragment;
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
        assert_eq!(installed.record.declarations.len(), 8);
        assert_eq!(
            installed
                .record
                .declarations
                .iter()
                .filter(|declaration| declaration.receipt.is_some())
                .count(),
            5
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
    fn list_v1_install_rolls_back_core_and_metadata_after_a_late_collision() {
        let (mut core, prelude) = core_with_prelude();
        let names = ListLibraryNames::under_namespace(BUILTIN_LIST_V1_NAMESPACE);
        core.declare_constant(names.nodup.clone(), CoreType::Prop)
            .expect("reserve a name reached after earlier List declarations");
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
        assert!(error.message.contains(&names.nodup));
        assert_eq!((core, registry), before);
    }
}
