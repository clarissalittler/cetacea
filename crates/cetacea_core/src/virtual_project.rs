//! In-memory project entry points shared by browser checking and editor analysis.
use super::*;

/// A bounded set of source files with one active file. Paths are relative to the
/// project root; imports resolve relative to the importing file. Host files are
/// never consulted. The standard library remains available through its bundled
/// identities and logical package registry.
pub struct VirtualProject<'a> {
    root: &'a str,
    files: &'a [VirtualFile],
}

impl<'a> VirtualProject<'a> {
    pub fn new(root: &'a str, files: &'a [VirtualFile]) -> Result<Self, String> {
        if files.len() > 64 {
            return Err("a project may contain at most 64 source files".into());
        }
        let mut seen = HashSet::new();
        let mut total = 0usize;
        for file in files {
            let path = &file.path;
            if path.is_empty()
                || path.len() > 512
                || path.starts_with("std/")
                || path.contains(['\\', ':'])
                || path.chars().any(char::is_control)
                || path.split('/').any(|part| matches!(part, "" | "." | ".."))
                || !path.ends_with(".ctea")
            {
                return Err(format!("invalid project source path `{path}`"));
            }
            if !seen.insert(path.as_str()) {
                return Err(format!("duplicate project source path `{path}`"));
            }
            if file.source.len() > 1024 * 1024 {
                return Err(format!("project source `{path}` exceeds 1 MiB"));
            }
            total += file.source.len();
        }
        if total > 8 * 1024 * 1024 {
            return Err("project sources exceed 8 MiB".into());
        }
        if !seen.contains(root) {
            return Err(format!("active project source `{root}` is missing"));
        }
        Ok(Self { root, files })
    }

    fn source(&self) -> &str {
        &self
            .files
            .iter()
            .find(|file| file.path == self.root)
            .expect("validated root")
            .source
    }

    fn location(&self) -> EditorLocation<'_> {
        EditorLocation {
            virtual_path: Some(self.root),
            ..EditorLocation::default()
        }
    }

    pub fn check(&self) -> HolShadowReport {
        match FileChecker::with_virtual_files_and_hol_shadow(self.files) {
            Ok(mut checker) => {
                checker.virtual_project = true;
                checker.check_virtual_path(self.root, false, None);
                checker.finish_hol_shadow()
            }
            Err(error) => {
                let mut checker = FileChecker::with_virtual_files(self.files);
                checker.virtual_project = true;
                checker.check_virtual_path(self.root, false, None);
                unavailable_hol_shadow(checker.result, error)
            }
        }
    }

    pub fn goals_at(&self, position: Position) -> GoalStepResult {
        goals_at_with_imports_in_mode(
            self.source(),
            position,
            self.files,
            EditorAnalysisMode::HolShadow,
            self.location(),
        )
    }

    pub fn run_tactic(&self, theorem: &str, tactic_index: usize) -> GoalStepResult {
        run_tactic_with_imports_in_mode(
            self.source(),
            theorem,
            tactic_index,
            self.files,
            EditorAnalysisMode::HolShadow,
            self.location(),
        )
    }

    pub fn explain(&self, theorem: &str) -> ExplanationResult {
        explain_theorem_with_imports_in_mode(
            self.source(),
            theorem,
            self.files,
            EditorAnalysisMode::HolShadow,
            self.location(),
        )
    }
}

/// Resolve a project-relative import without silently clamping `..` at root.
pub(super) fn project_import_path(base: Option<&str>, path: &str) -> Option<String> {
    if path.starts_with('/') || path.contains(['\\', ':']) {
        return None;
    }
    let mut parts: Vec<&str> = base.into_iter().flat_map(|s| s.split('/')).collect();
    for part in path.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                parts.pop()?;
            }
            part => parts.push(part),
        }
    }
    Some(parts.join("/"))
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
    fn errors(diagnostics: &[Diagnostic]) -> bool {
        diagnostics
            .iter()
            .any(|d| d.severity == DiagnosticSeverity::Error)
    }
    #[test]
    fn nested_project_imports_work_in_all_editor_surfaces() {
        let files = vec![
            file("lessons/main.ctea", "import ../lib/helper.ctea as H\nimport std/qualified_prelude.ctea\nimport sibling.ctea as S\ntheorem answer : True /\\ True := by\n  split\n  exact H.helper\n  exact S.local\n"),
            file("lib/helper.ctea", "import detail/base.ctea as B\ntheorem helper : True := by\n  exact B.base\n"),
            file("lib/detail/base.ctea", "theorem base : True := by\n  trivial\n"),
            file("lessons/sibling.ctea", "theorem local : True := by\n  trivial\n"),
            file("sibling.ctea", "theorem wrong : False := by\n  trivial\n"),
        ];
        let project = VirtualProject::new("lessons/main.ctea", &files).unwrap();
        let report = project.check();
        assert!(report.is_match(), "{:?}", report.mismatches);
        assert!(
            !errors(&report.legacy.diagnostics),
            "{:?}",
            report.legacy.diagnostics
        );
        let root: Vec<_> = report
            .legacy
            .theorems
            .iter()
            .filter(|t| !t.is_imported)
            .collect();
        assert_eq!(root.len(), 1);
        assert_eq!(root[0].name, "answer");
        let goals = project.goals_at(Position { line: 5, column: 1 });
        assert!(!errors(&goals.diagnostics), "{:?}", goals.diagnostics);
        assert_eq!(goals.goals.len(), 1);
        assert!(project.run_tactic("answer", 2).completed);
        let explanation = project.explain("answer");
        assert!(
            !errors(&explanation.diagnostics),
            "{:?}",
            explanation.diagnostics
        );
        assert_eq!(explanation.steps.len(), 3);
    }
    #[test]
    fn missing_imports_do_not_read_host_files_and_edits_are_rechecked() {
        let mut files = vec![file(
            "main.ctea",
            "import docs/book/code/ch01-examples.ctea\ntheorem answer : True := by\n  trivial\n",
        )];
        let report = VirtualProject::new("main.ctea", &files).unwrap().check();
        assert!(report
            .legacy
            .diagnostics
            .iter()
            .any(|d| d.message.contains("project source") && d.message.contains("missing")));
        files[0].source =
            "import helper.ctea\ntheorem answer : True := by\n  exact helper\n".into();
        files.push(file(
            "helper.ctea",
            "theorem helper : True := by\n  trivial\n",
        ));
        assert!(!errors(
            &VirtualProject::new("main.ctea", &files)
                .unwrap()
                .check()
                .legacy
                .diagnostics
        ));
        files[1].source = "theorem helper : False := by\n  trivial\n".into();
        let project = VirtualProject::new("main.ctea", &files).unwrap();
        assert!(errors(&project.check().legacy.diagnostics));
        assert!(!project.run_tactic("answer", 0).completed);
        assert!(errors(&project.explain("answer").diagnostics));
    }
    #[test]
    fn project_cycles_and_root_escape_are_rejected() {
        for imported in ["main.ctea", "../main.ctea", "/main.ctea"] {
            let files = vec![file(
                "main.ctea",
                &format!("import {imported}\ntheorem answer : True := by\n  trivial\n"),
            )];
            let project = VirtualProject::new("main.ctea", &files).unwrap();
            assert!(errors(&project.check().legacy.diagnostics), "{imported}");
            assert!(!project.run_tactic("answer", 0).completed, "{imported}");
        }
    }
    #[test]
    fn project_manifest_rejects_ambiguous_paths_and_oversized_sources() {
        for path in [
            "../main.ctea",
            "/main.ctea",
            "a/../main.ctea",
            "a\\main.ctea",
            "builtin:std/nat.ctea",
            "std/nat.ctea",
            "main.json",
            "a//main.ctea",
        ] {
            assert!(
                VirtualProject::new(path, &[file(path, "")]).is_err(),
                "{path}"
            );
        }
        assert!(
            VirtualProject::new("main.ctea", &[file("main.ctea", ""), file("main.ctea", "")])
                .is_err()
        );
        assert!(VirtualProject::new("missing.ctea", &[file("main.ctea", "")]).is_err());
        assert!(VirtualProject::new(
            "main.ctea",
            &[file("main.ctea", &" ".repeat(1024 * 1024 + 1))]
        )
        .is_err());
    }
}
