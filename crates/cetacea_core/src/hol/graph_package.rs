//! Checked explicit-path package, with the shared List package as dependency.
use super::*;
use crate::hol::graph_library::{GraphLibrary, GraphLibraryNames, RelationPathLibrary};

const NAMESPACE: &str = "@library.graph.v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstalledGraphLibrary {
    pub record: LibraryPackageRecord,
    pub paths: RelationPathLibrary,
    pub path_nil: TheoremId,
    pub path_cons: TheoremId,
}

impl HolLibraryRegistry {
    pub fn install_builtin_graph_v1(
        &mut self,
        core: &mut SpikeElaborator,
        natural_type: CoreType,
        zero: ConstantId,
        successor: ConstantId,
        addition: ConstantId,
    ) -> Result<InstalledGraphLibrary, SpikeError> {
        let mut staged_core = core.clone();
        let mut staged_registry = self.clone();
        let installed_lists = staged_registry.install_builtin_list_v1(
            &mut staged_core,
            natural_type,
            zero,
            successor,
            addition,
        )?;
        if let Some(InstalledLibraryPackage::GraphV1(installed)) =
            staged_registry.get(LibraryPackageId::GraphV1)
        {
            validate(&staged_core, installed)?;
            let installed = installed.clone();
            *core = staged_core;
            *self = staged_registry;
            return Ok(installed);
        }
        let lists = &installed_lists.lists;
        let paths = RelationPathLibrary::install_named(
            &mut staged_core,
            lists,
            &GraphLibraryNames::under_namespace(NAMESPACE),
        )?;
        let element = CoreType::Parameter(lists.element_parameter);
        let edge = GraphLibrary::edge_type(element.clone());
        let nil_left = paths.valid_path_term(
            element.clone(),
            CoreTerm::Bound(2),
            lists.nil_term(element.clone()),
            CoreTerm::Bound(1),
            CoreTerm::Bound(0),
        );
        let nil_right = CoreTerm::equality(element.clone(), CoreTerm::Bound(0), CoreTerm::Bound(1));
        let cons_left = paths.valid_path_term(
            element.clone(),
            CoreTerm::Bound(4),
            lists.cons_term(element.clone(), CoreTerm::Bound(3), CoreTerm::Bound(2)),
            CoreTerm::Bound(1),
            CoreTerm::Bound(0),
        );
        let cons_right = CoreTerm::and(
            CoreTerm::apply(
                CoreTerm::apply(CoreTerm::Bound(4), CoreTerm::Bound(1)),
                CoreTerm::Bound(3),
            ),
            paths.valid_path_term(
                element.clone(),
                CoreTerm::Bound(4),
                CoreTerm::Bound(2),
                CoreTerm::Bound(3),
                CoreTerm::Bound(0),
            ),
        );
        let mut laws = Vec::new();
        for (name, parameters, left, right) in [
            (
                "path_nil",
                vec![edge.clone(), element.clone(), element.clone()],
                nil_left,
                nil_right,
            ),
            (
                "path_cons",
                vec![
                    edge,
                    element.clone(),
                    lists.list_type(element.clone()),
                    element.clone(),
                    element,
                ],
                cons_left,
                cons_right,
            ),
        ] {
            let (theorem, _) = staged_core.declare_theorem_with_parameters(
                format!("{NAMESPACE}.{name}"),
                vec![lists.element_parameter],
                parameters,
                CoreTerm::and(
                    CoreTerm::implies(left.clone(), right.clone()),
                    CoreTerm::implies(right.clone(), left.clone()),
                ),
                definitional_iff_proof(left, right),
            )?;
            laws.push(theorem);
        }
        let mut installed = InstalledGraphLibrary {
            record: LibraryPackageRecord {
                id: LibraryPackageId::GraphV1,
                provenance: LibraryPackageProvenance {
                    module: "std/hol/graph".into(),
                    version: 1,
                    source: LibraryPackageSource::Builtin,
                },
                core_namespace: NAMESPACE.into(),
                dependencies: vec![LibraryPackageId::ListV1],
                declarations: vec![],
            },
            paths,
            path_nil: laws[0],
            path_cons: laws[1],
        };
        installed.record.declarations = catalog(&staged_core, &installed)?;
        validate(&staged_core, &installed)?;
        staged_registry.packages.insert(
            LibraryPackageId::GraphV1,
            InstalledLibraryPackage::GraphV1(installed.clone()),
        );
        *core = staged_core;
        *self = staged_registry;
        Ok(installed)
    }
}

fn catalog(
    core: &SpikeElaborator,
    installed: &InstalledGraphLibrary,
) -> Result<Vec<LibraryDeclaration>, SpikeError> {
    let entries = [
        (
            "ValidPath",
            LibraryDeclarationKind::Definition,
            core.definition_receipt(installed.paths.valid_path),
        ),
        (
            "path_nil",
            LibraryDeclarationKind::Theorem,
            core.theorem_receipt(installed.path_nil),
        ),
        (
            "path_cons",
            LibraryDeclarationKind::Theorem,
            core.theorem_receipt(installed.path_cons),
        ),
    ];
    entries
        .into_iter()
        .map(|(name, kind, receipt)| {
            let receipt = receipt.ok_or_else(|| SpikeError {
                message: format!("missing graph package receipt for {name}"),
            })?;
            if !receipt.proof().axiom_dependencies().is_empty()
                || !receipt.proof().incomplete_dependencies().is_empty()
            {
                return Err(SpikeError {
                    message: format!("untrusted graph package declaration {name}"),
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

fn validate(core: &SpikeElaborator, installed: &InstalledGraphLibrary) -> Result<(), SpikeError> {
    if installed.record.id != LibraryPackageId::GraphV1
        || installed.record.provenance
            != (LibraryPackageProvenance {
                module: "std/hol/graph".into(),
                version: 1,
                source: LibraryPackageSource::Builtin,
            })
        || installed.record.core_namespace != NAMESPACE
        || installed.record.dependencies != [LibraryPackageId::ListV1]
        || installed.record.declarations != catalog(core, installed)?
        || core.constants().resolve(&format!("{NAMESPACE}.ValidPath"))
            != Some(installed.paths.valid_path)
        || core.theorems().resolve(&format!("{NAMESPACE}.path_nil")) != Some(installed.path_nil)
        || core.theorems().resolve(&format!("{NAMESPACE}.path_cons")) != Some(installed.path_cons)
    {
        return Err(SpikeError {
            message: "graph package registry/core mismatch".into(),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::hol::CompatibilityElaborator;
    #[test]
    fn graph_import_is_idempotent_and_alias_collisions_are_atomic() {
        let mut elaborator = CompatibilityElaborator::new().unwrap();
        let installed = elaborator.import_builtin_graph_v1(Some("G")).unwrap();
        let before = elaborator.clone();
        assert_eq!(
            elaborator.import_builtin_graph_v1(Some("G")).unwrap(),
            installed
        );
        assert_eq!(elaborator, before);
        assert_eq!(
            elaborator.import_builtin_graph_v1(Some("H")).unwrap(),
            installed
        );
        let mut collision = CompatibilityElaborator::new().unwrap();
        collision
            .declare_constant("G.path_cons", &crate::Type::Nat)
            .unwrap();
        let before = collision.clone();
        assert!(collision.import_builtin_graph_v1(Some("G")).is_err());
        assert_eq!(collision, before);
        assert!(collision
            .core()
            .constants()
            .resolve("@library.graph.v1.ValidPath")
            .is_none());
    }
}
