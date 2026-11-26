//! Assignment manifests: the tier, policy, allowed imports, and the
//! theorem statements a submission must keep. An instructor generates a
//! manifest from the skeleton file they hand out; the checker fails a
//! submission that changes a statement, drops a theorem, or imports
//! something the assignment does not allow.

use serde::{Deserialize, Serialize};

use crate::{CheckResult, DeclStatus, Policy};

#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct ManifestTheorem {
    pub name: String,
    /// The statement as the checker prints it.
    pub statement: String,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct Manifest {
    #[serde(default)]
    pub title: String,
    /// `fol`, `fol_nat`, or `hol`.
    #[serde(default)]
    pub tier: Option<String>,
    #[serde(default)]
    pub policy: Policy,
    /// Import paths allowed in the submission, compared by suffix so
    /// `std/prelude.ctea` matches `../../std/prelude.ctea`. Empty means
    /// imports are not restricted.
    #[serde(default)]
    pub allowed_imports: Vec<String>,
    #[serde(default)]
    pub theorems: Vec<ManifestTheorem>,
}

#[derive(Clone, Debug, Serialize)]
pub struct AssignmentTheoremStatus {
    pub name: String,
    pub expected: String,
    pub status: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct AssignmentReport {
    pub title: String,
    pub violations: Vec<String>,
    pub theorems: Vec<AssignmentTheoremStatus>,
    pub complete: bool,
}

/// Builds a manifest from a checked skeleton: every root theorem's
/// statement is pinned and the root's imports become the allowed set.
pub fn manifest_from_result(result: &CheckResult, title: &str, tier: Option<&str>) -> Manifest {
    manifest_with_policy(result, title, tier, Policy::default())
}

/// Like [`manifest_from_result`], with the rules of a course section (or
/// any other policy) written into the manifest, so the assignment is
/// graded under them wherever it is checked.
pub fn manifest_with_policy(
    result: &CheckResult,
    title: &str,
    tier: Option<&str>,
    policy: Policy,
) -> Manifest {
    Manifest {
        title: title.to_string(),
        tier: tier.map(str::to_string),
        policy: Policy {
            deny_sorry: true,
            deny_axioms: true,
            ..policy
        },
        allowed_imports: result
            .root_imports
            .iter()
            .map(|p| {
                p.rsplit("std/")
                    .next()
                    .map(|s| format!("std/{s}"))
                    .unwrap_or_else(|| p.clone())
            })
            .collect(),
        theorems: result
            .decls
            .iter()
            .filter(|d| !d.is_imported && d.kind == "theorem")
            .map(|d| ManifestTheorem {
                name: d.name.clone(),
                statement: d.statement.clone(),
            })
            .collect(),
    }
}

/// Checks a submission's result against a manifest.
pub fn check_manifest(result: &CheckResult, manifest: &Manifest) -> AssignmentReport {
    let mut violations = Vec::new();
    if !manifest.allowed_imports.is_empty() {
        for import in &result.root_imports {
            let allowed = manifest
                .allowed_imports
                .iter()
                .any(|a| import.ends_with(a.as_str()) || a.ends_with(import.as_str()));
            if !allowed {
                violations.push(format!(
                    "the import `{import}` is not allowed in this assignment"
                ));
            }
        }
    }
    let mut theorems = Vec::new();
    let mut complete = true;
    for expected in &manifest.theorems {
        let found = result
            .decls
            .iter()
            .find(|d| !d.is_imported && d.name == expected.name);
        let status = match found {
            None => {
                violations.push(format!("the theorem `{}` is missing", expected.name));
                complete = false;
                "missing".to_string()
            }
            Some(decl) if decl.statement != expected.statement => {
                violations.push(format!(
                    "the statement of `{}` was changed: expected `{}`, found `{}`",
                    expected.name, expected.statement, decl.statement
                ));
                complete = false;
                "changed".to_string()
            }
            Some(decl) => {
                if decl.status != DeclStatus::Accepted {
                    complete = false;
                }
                match decl.status {
                    DeclStatus::Accepted => "accepted",
                    DeclStatus::Incomplete => "incomplete",
                    DeclStatus::TrustedAxiom => "axiom",
                    DeclStatus::Failed => "failed",
                }
                .to_string()
            }
        };
        theorems.push(AssignmentTheoremStatus {
            name: expected.name.clone(),
            expected: expected.statement.clone(),
            status,
        });
    }
    if !result.violations.is_empty() {
        complete = false;
    }
    let complete = complete && violations.is_empty();
    AssignmentReport {
        title: manifest.title.clone(),
        violations,
        theorems,
        complete,
    }
}
