//! Checked matrix sums with the shared List package as dependency.
use super::*;
use crate::hol::matrix_library::MatrixLibrary;
const NAMESPACE: &str = "@library.matrix.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstalledMatrixLibrary {
    pub record: LibraryPackageRecord,
    pub matrix: MatrixLibrary,
}

impl HolLibraryRegistry {
    pub fn install_builtin_matrix_v1(
        &mut self,
        core: &mut SpikeElaborator,
        natural_type: CoreType,
        zero: ConstantId,
        successor: ConstantId,
        addition: ConstantId,
    ) -> Result<InstalledMatrixLibrary, SpikeError> {
        let mut staged_core = core.clone();
        let mut staged_registry = self.clone();
        let lists = staged_registry.install_builtin_list_v1(
            &mut staged_core,
            natural_type.clone(),
            zero,
            successor,
            addition,
        )?;
        if let Some(InstalledLibraryPackage::MatrixV1(installed)) =
            staged_registry.get(LibraryPackageId::MatrixV1)
        {
            validate(&staged_core, installed)?;
            let installed = installed.clone();
            *core = staged_core;
            *self = staged_registry;
            return Ok(installed);
        }
        let matrix = MatrixLibrary::install_named(
            &mut staged_core,
            &lists.lists,
            natural_type,
            zero,
            addition,
            NAMESPACE,
        )?;
        let mut installed = InstalledMatrixLibrary {
            record: LibraryPackageRecord {
                id: LibraryPackageId::MatrixV1,
                provenance: LibraryPackageProvenance {
                    module: "std/hol/matrix".into(),
                    version: 1,
                    source: LibraryPackageSource::Builtin,
                },
                core_namespace: NAMESPACE.into(),
                dependencies: vec![LibraryPackageId::ListV1],
                declarations: vec![],
            },
            matrix,
        };
        installed.record.declarations = catalog(&staged_core, &installed)?;
        validate(&staged_core, &installed)?;
        staged_registry.packages.insert(
            LibraryPackageId::MatrixV1,
            InstalledLibraryPackage::MatrixV1(installed.clone()),
        );
        *core = staged_core;
        *self = staged_registry;
        Ok(installed)
    }
}
fn catalog(
    core: &SpikeElaborator,
    installed: &InstalledMatrixLibrary,
) -> Result<Vec<LibraryDeclaration>, SpikeError> {
    let mut entries = Vec::new();
    for (name, constant) in MatrixLibrary::EXPORTS
        .into_iter()
        .zip(installed.matrix.constants())
    {
        if core.constants().resolve(&format!("{NAMESPACE}.{name}")) != Some(constant) {
            return Err(SpikeError {
                message: "matrix constant registry/core mismatch".into(),
            });
        }
        entries.push((
            name,
            LibraryDeclarationKind::Definition,
            core.definition_receipt(constant),
        ));
    }
    for equation in &installed.matrix.equations {
        if core
            .theorems()
            .resolve(&format!("{NAMESPACE}.{}", equation.name))
            != Some(equation.theorem)
        {
            return Err(SpikeError {
                message: "matrix theorem registry/core mismatch".into(),
            });
        }
        entries.push((
            &equation.name,
            LibraryDeclarationKind::Theorem,
            core.theorem_receipt(equation.theorem),
        ));
    }
    entries
        .into_iter()
        .map(|(name, kind, receipt)| {
            let receipt = receipt.ok_or_else(|| SpikeError {
                message: format!("missing matrix receipt for {name}"),
            })?;
            if !receipt.proof().axiom_dependencies().is_empty()
                || !receipt.proof().incomplete_dependencies().is_empty()
            {
                return Err(SpikeError {
                    message: format!("untrusted matrix declaration {name}"),
                });
            }
            Ok(LibraryDeclaration {
                logical_name: name.into(),
                core_name: format!("{NAMESPACE}.{name}"),
                kind,
                receipt: Some(receipt.id()),
            })
        })
        .collect()
}
fn validate(core: &SpikeElaborator, installed: &InstalledMatrixLibrary) -> Result<(), SpikeError> {
    if installed.record.id != LibraryPackageId::MatrixV1
        || installed.record.provenance
            != (LibraryPackageProvenance {
                module: "std/hol/matrix".into(),
                version: 1,
                source: LibraryPackageSource::Builtin,
            })
        || installed.record.core_namespace != NAMESPACE
        || installed.record.dependencies != [LibraryPackageId::ListV1]
        || installed.matrix.equations.len() != 8
        || installed.record.declarations != catalog(core, installed)?
    {
        return Err(SpikeError {
            message: "matrix package registry/core mismatch".into(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::hol::CompatibilityElaborator;
    #[test]
    fn matrix_import_is_idempotent_and_alias_collisions_are_atomic() {
        let mut elaborator = CompatibilityElaborator::new().unwrap();
        let installed = elaborator.import_builtin_matrix_v1(Some("G")).unwrap();
        let before = elaborator.clone();
        assert_eq!(
            elaborator.import_builtin_matrix_v1(Some("G")).unwrap(),
            installed
        );
        assert_eq!(elaborator, before);
        assert_eq!(
            elaborator.import_builtin_matrix_v1(Some("H")).unwrap(),
            installed
        );
        let mut collision = CompatibilityElaborator::new().unwrap();
        collision
            .declare_constant("G.columns_total_cons", &crate::Type::Nat)
            .unwrap();
        let before = collision.clone();
        assert!(collision.import_builtin_matrix_v1(Some("G")).is_err());
        assert_eq!(collision, before);
        assert!(collision
            .core()
            .constants()
            .resolve("@library.matrix.v1.rows_total")
            .is_none());
    }
}
