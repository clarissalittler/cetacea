//! Instructor-owned assignment context for in-memory student projects.
use super::{
    check_receipt_requirements, parse_manifest, AssignmentManifest, AssignmentViolation,
    ReceiptRequirements,
};
use crate::{
    hol::LibraryPackageId, DiagnosticSeverity, HolShadowReport, VirtualFile, VirtualProject,
};
use std::collections::BTreeSet;

/// Trusted manifests and libraries must be supplied independently of student
/// project archives. This type owns its copies and never exposes mutable files.
pub struct VirtualAssignment {
    manifest: AssignmentManifest,
    trusted: Vec<VirtualFile>,
    allowed: BTreeSet<String>,
    required: Vec<(String, String)>,
    grants: Vec<String>,
}

pub struct AssignmentResult {
    pub report: HolShadowReport,
    pub violations: Vec<AssignmentViolation>,
}
impl AssignmentResult {
    /// Policy success cannot hide failed elaboration or kernel certification.
    pub fn accepted(&self) -> bool {
        self.report.is_match()
            && !self
                .report
                .legacy
                .diagnostics
                .iter()
                .any(|d| d.severity == DiagnosticSeverity::Error)
            && self.violations.is_empty()
    }
}

impl VirtualAssignment {
    pub fn new(path: &str, source: &str, trusted: Vec<VirtualFile>) -> Result<Self, String> {
        if !path.ends_with(".ctea-assignment")
            || path.len() > 512
            || path.contains(['\\', ':'])
            || path.chars().any(char::is_control)
            || path.split('/').any(|part| matches!(part, "" | "." | ".."))
        {
            return Err("invalid project-relative assignment path".into());
        }
        let manifest = parse_manifest(source).map_err(|e| e.to_string())?;
        if let Some(first) = trusted.first() {
            VirtualProject::new(&first.path, &trusted)?;
        }
        let base = path.rsplit_once('/').map(|(base, _)| base);
        let resolve = |name: &str| resolve_identity(base, name, &trusted);
        let mut allowed = BTreeSet::new();
        for import in &manifest.allowed_imports {
            let identity = resolve(import)?;
            if !allowed.insert(identity) {
                return Err(format!(
                    "allowed import `{import}` repeats a resolved identity"
                ));
            }
        }
        let mut required = Vec::new();
        for import in &manifest.required_imports {
            let identity = resolve(import)?;
            if required.iter().any(|(_, existing)| existing == &identity) {
                return Err(format!(
                    "required import `{import}` repeats a resolved identity"
                ));
            }
            allowed.insert(identity.clone());
            required.push((import.clone(), identity));
        }
        let mut grants = Vec::new();
        for grant in &manifest.allowed_theorems {
            let (library, export) = grant.rsplit_once("::").expect("parsed grant identity");
            let identity = format!("{}::{export}", resolve(library)?);
            if grants.contains(&identity) {
                return Err(format!("theorem grant `{grant}` repeats a resolved export"));
            }
            grants.push(identity);
        }
        // Validate trusted libraries without any student files in scope. A
        // trusted library cannot obtain its meaning from an editable helper.
        for file in &trusted {
            let report = VirtualProject::new(&file.path, &trusted)?.check();
            if !report.is_match()
                || report
                    .legacy
                    .diagnostics
                    .iter()
                    .any(|d| d.severity == DiagnosticSeverity::Error)
            {
                return Err(format!(
                    "trusted library `{}` does not check independently",
                    file.path
                ));
            }
        }
        Ok(Self {
            manifest,
            trusted,
            allowed,
            required,
            grants,
        })
    }

    fn with_project<T>(
        &self,
        root: &str,
        student_files: &[VirtualFile],
        analyze: impl FnOnce(&VirtualProject<'_>) -> T,
    ) -> Result<T, String> {
        VirtualProject::new(root, student_files)?;
        for file in student_files {
            if self.trusted.iter().any(|trusted| trusted.path == file.path) {
                return Err(format!(
                    "student file `{}` collides with a trusted assignment library",
                    file.path
                ));
            }
        }
        let mut files = self.trusted.clone();
        files.extend_from_slice(student_files);
        let project = VirtualProject::new(root, &files)?;
        Ok(analyze(&project))
    }

    pub fn goals_at(
        &self,
        root: &str,
        files: &[VirtualFile],
        position: crate::Position,
    ) -> Result<crate::GoalStepResult, String> {
        self.with_project(root, files, |project| project.goals_at(position))
    }
    pub fn run_tactic(
        &self,
        root: &str,
        files: &[VirtualFile],
        theorem: &str,
        index: usize,
    ) -> Result<crate::GoalStepResult, String> {
        self.with_project(root, files, |project| project.run_tactic(theorem, index))
    }
    pub fn explain(
        &self,
        root: &str,
        files: &[VirtualFile],
        theorem: &str,
    ) -> Result<crate::ExplanationResult, String> {
        self.with_project(root, files, |project| project.explain(theorem))
    }
    pub fn outline(
        &self,
        root: &str,
        files: &[VirtualFile],
    ) -> Result<crate::SourceOutline, String> {
        self.with_project(root, files, |_| {
            crate::outline(
                &files
                    .iter()
                    .find(|file| file.path == root)
                    .expect("validated student root")
                    .source,
            )
        })
    }

    pub fn check(
        &self,
        root: &str,
        student_files: &[VirtualFile],
    ) -> Result<AssignmentResult, String> {
        let report = self.with_project(root, student_files, |project| project.check())?;
        let mut violations = check_receipt_requirements(
            &report,
            self.manifest.teaching_policy(),
            Some(ReceiptRequirements {
                allowed_theorem_identities: &self.grants,
                allowed_axioms: &self.manifest.allowed_axioms,
                required_theorems: &self.manifest.required_theorems,
            }),
        );
        for identity in report
            .imported_virtual_files
            .iter()
            .chain(&report.imported_packages)
        {
            if !self.allowed.contains(identity) {
                violations.push(AssignmentViolation {
                    declaration: identity.clone(),
                    kind: "import",
                    message: format!("resolved import `{identity}` is not allowed"),
                });
            }
        }
        for (written, identity) in &self.required {
            if !report.imported_virtual_files.contains(identity)
                && !report.imported_packages.contains(identity)
            {
                violations.push(AssignmentViolation {
                    declaration: written.clone(),
                    kind: "required_import",
                    message: format!("required import `{written}` was not loaded"),
                });
            }
        }
        for path in &report.imported_files {
            violations.push(AssignmentViolation {
                declaration: path.display().to_string(),
                kind: "import",
                message: "host filesystem imports are not allowed in a virtual assignment".into(),
            });
        }
        violations.sort_by(|a, b| {
            (&a.declaration, a.kind, &a.message).cmp(&(&b.declaration, b.kind, &b.message))
        });
        violations.dedup();
        Ok(AssignmentResult { report, violations })
    }
}

fn resolve_identity(
    base: Option<&str>,
    name: &str,
    trusted: &[VirtualFile],
) -> Result<String, String> {
    if let Some(package) = LibraryPackageId::from_logical_id(name) {
        return Ok(package.to_string());
    }
    if name.starts_with("builtin:") {
        return crate::stdlib::bundled_source(name)
            .map(|_| name.to_string())
            .ok_or_else(|| format!("unknown bundled assignment import `{name}`"));
    }
    let path = if name.starts_with("std/") {
        name.to_string()
    } else {
        crate::virtual_project::project_import_path(base, name).ok_or_else(|| {
            format!("assignment import `{name}` escapes the project or uses an invalid path")
        })?
    };
    let bundled = format!("builtin:{path}");
    if path.starts_with("std/") && crate::stdlib::bundled_source(&bundled).is_some() {
        return Ok(bundled);
    }
    if trusted.iter().any(|file| file.path == path) {
        return Ok(path);
    }
    Err(format!(
        "assignment import `{name}` does not resolve to a pinned library or registered package"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn file(path: &str, source: &str) -> VirtualFile {
        VirtualFile {
            path: path.into(),
            source: source.into(),
        }
    }
    const HELPER: &str = "theorem helper : True := by\n  trivial\n";
    const MAIN: &str =
        "import ../lib/helper.ctea as H\ntheorem answer : True := by\n  exact H.helper\n";
    const MANIFEST: &str = "version = 1\nprofile = 'prop'\nrequired_imports = ['../lib/helper.ctea']\nallowed_theorems = ['../lib/helper.ctea::helper']\nrequired_theorem.answer = 'True'\n";
    #[test]
    fn pinned_libraries_and_source_grants_are_checked_without_student_substitution() {
        let assignment = VirtualAssignment::new(
            "course/task.ctea-assignment",
            MANIFEST,
            vec![file("lib/helper.ctea", HELPER)],
        )
        .unwrap();
        assert!(assignment
            .check("work/main.ctea", &[file("work/main.ctea", MAIN)])
            .unwrap()
            .accepted());
        for source in [HELPER, "axiom helper : True\n"] {
            assert!(assignment
                .check(
                    "work/main.ctea",
                    &[
                        file("work/main.ctea", MAIN),
                        file("lib/helper.ctea", source)
                    ]
                )
                .is_err());
        }
        let broken = MAIN.replace("exact H.helper", "sorry");
        let result = assignment
            .check("work/main.ctea", &[file("work/main.ctea", &broken)])
            .unwrap();
        assert!(!result.accepted());
        assert!(result.violations.iter().any(|v| v.kind == "incomplete"));
    }
    #[test]
    fn trusted_dependencies_cannot_be_filled_from_the_student_project() {
        let helper = "import missing.ctea\ntheorem helper : True := by\n  trivial\n";
        assert!(VirtualAssignment::new(
            "course/task.ctea-assignment",
            MANIFEST,
            vec![file("lib/helper.ctea", helper)]
        )
        .is_err());
        assert!(VirtualAssignment::new("course/task.ctea-assignment", MANIFEST, vec![]).is_err());
    }
    #[test]
    fn acceptance_requires_kernel_success_required_theorems_and_authorized_transitive_imports() {
        let policy = "version = 1\nprofile = 'prop'\nrequired_theorem.answer = 'True'\n";
        let assignment = VirtualAssignment::new("task.ctea-assignment", policy, vec![]).unwrap();
        for source in [
            "",
            "theorem answer : False := by\n  trivial\n",
            "theorem answer : False -> False := by\n  intro h\n  exact h\n",
        ] {
            assert!(!assignment
                .check("main.ctea", &[file("main.ctea", source)])
                .unwrap()
                .accepted());
        }
        let trusted = vec![
            file(
                "lib/helper.ctea",
                "import second.ctea\ntheorem helper : True := by\n  trivial\n",
            ),
            file(
                "lib/second.ctea",
                HELPER.replace("helper", "second").as_str(),
            ),
        ];
        let assignment =
            VirtualAssignment::new("course/task.ctea-assignment", MANIFEST, trusted).unwrap();
        let result = assignment
            .check("work/main.ctea", &[file("work/main.ctea", MAIN)])
            .unwrap();
        assert!(result
            .violations
            .iter()
            .any(|v| v.kind == "import" && v.declaration == "lib/second.ctea"));
        assert!(!result.accepted());
    }
    #[test]
    fn relative_standard_library_imports_resolve_to_reserved_bundled_sources() {
        let source = "import ../../std/prop.ctea as P\ntheorem answer : True := by\n  trivial\n";
        let manifest = "version = 1\nprofile = 'prop'\nrequired_imports = ['../../std/prop.ctea']\nrequired_theorem.answer = 'True'\n";
        let assignment =
            VirtualAssignment::new("course/week/task.ctea-assignment", manifest, vec![]).unwrap();
        let result = assignment
            .check(
                "work/week/main.ctea",
                &[file("work/week/main.ctea", source)],
            )
            .unwrap();
        assert!(result.accepted(), "{:?}", result.violations);
        assert!(result
            .report
            .imported_virtual_files
            .contains(&"builtin:std/prop.ctea".into()));
    }
}
