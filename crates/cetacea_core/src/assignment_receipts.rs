//! Receipt-level assignment requirements shared by native and browser consumers.
//! Import authorization and trusted-source resolution belong to the caller.
use super::{RequiredTheorem, TeachingPolicy};
use crate::hol::{DeclarationId, EvidenceStatus, PolicyViolation as HolReceiptPolicyViolation};
use crate::HolShadowReport;

/// Resolved identities must come from an instructor-controlled assignment
/// context. Student file names alone do not authorize theorem grants.
#[derive(Clone, Copy)]
pub struct ReceiptRequirements<'a> {
    pub allowed_theorem_identities: &'a [String],
    pub allowed_axioms: &'a [String],
    pub required_theorems: &'a [RequiredTheorem],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssignmentViolation {
    pub declaration: String,
    pub kind: &'static str,
    pub message: String,
}

/// Check grants, required root signatures, and root receipt restrictions.
/// An empty result alone does not certify a file: callers must also require
/// successful kernel checking and separately enforce authorized imports.
pub fn check_receipt_requirements(
    report: &HolShadowReport,
    config: TeachingPolicy,
    assignment: Option<ReceiptRequirements<'_>>,
) -> Vec<AssignmentViolation> {
    let mut policy = config.receipt_policy();

    let mut violations = Vec::new();
    if let Some(assignment) = assignment {
        for name in assignment.allowed_theorem_identities {
            let mut matched = false;
            let mut valid = true;
            for theorem in report
                .package_theorems
                .iter()
                .chain(&report.theorems)
                .filter(|t| t.is_imported && t.library_identity.as_ref() == Some(name))
            {
                matched = true;
                valid &= policy.allow_checked_dependency(&theorem.receipt);
            }
            if !matched || !valid {
                violations.push(AssignmentViolation {
                    declaration: name.clone(),
                    kind: "allowed_theorem",
                    message:
                        "grant must resolve to an imported, checked, trust-free library theorem"
                            .to_string(),
                });
            }
        }
        for name in assignment.allowed_axioms {
            match report.theorems.iter().find(|theorem| theorem.name == *name) {
                Some(theorem)
                    if theorem.hol_status == EvidenceStatus::TrustedAxiom
                        && theorem.is_imported =>
                {
                    policy.allow_axiom(theorem.receipt.id());
                }
                Some(theorem) if theorem.hol_status != EvidenceStatus::TrustedAxiom => {
                    violations.push(AssignmentViolation {
                        declaration: name.clone(),
                        kind: "allowed_axiom",
                        message: "manifest entry does not name a trusted axiom".to_string(),
                    });
                }
                Some(_) => violations.push(AssignmentViolation {
                    declaration: name.clone(),
                    kind: "allowed_axiom",
                    message: "manifest may allow only imported trusted axioms".to_string(),
                }),
                None => violations.push(AssignmentViolation {
                    declaration: name.clone(),
                    kind: "allowed_axiom",
                    message: "manifest entry does not resolve to a checked declaration".to_string(),
                }),
            }
        }

        for required in assignment.required_theorems {
            match report
                .theorems
                .iter()
                .find(|theorem| !theorem.is_imported && theorem.name == required.name)
            {
                None => violations.push(AssignmentViolation {
                    declaration: required.name.clone(),
                    kind: "required_theorem",
                    message: "required root theorem is missing".to_string(),
                }),
                Some(theorem) if theorem.signature != required.signature => {
                    violations.push(AssignmentViolation {
                        declaration: required.name.clone(),
                        kind: "theorem_signature",
                        message: format!(
                            "signature does not match manifest: expected `{}`, found `{}`",
                            required.signature, theorem.signature
                        ),
                    });
                }
                Some(_) => {}
            }
        }
    }

    for theorem in report
        .theorems
        .iter()
        .filter(|theorem| !theorem.is_imported)
    {
        violations.extend(policy.check(&theorem.receipt).into_iter().map(|violation| {
            AssignmentViolation {
                declaration: theorem.name.clone(),
                kind: hol_policy_violation_kind(violation),
                message: describe_hol_policy_violation(report, violation),
            }
        }));
    }
    violations.sort_by(|left, right| {
        (&left.declaration, left.kind, &left.message).cmp(&(
            &right.declaration,
            right.kind,
            &right.message,
        ))
    });
    violations.dedup();
    violations
}

fn hol_policy_violation_kind(violation: HolReceiptPolicyViolation) -> &'static str {
    match violation {
        HolReceiptPolicyViolation::StatementFragmentExceeds { .. } => "statement_fragment",
        HolReceiptPolicyViolation::DependencyFragmentExceeds { .. } => "dependency_fragment",
        HolReceiptPolicyViolation::FeatureNotAllowed(_) => "feature",
        HolReceiptPolicyViolation::FeatureFragmentExceeds { .. } => "feature_fragment",
        HolReceiptPolicyViolation::TrustedAxiomNotAllowed(_) => "trusted_axiom",
        HolReceiptPolicyViolation::IncompleteNotAllowed(_) => "incomplete",
        HolReceiptPolicyViolation::DependencyNotAllowed(_) => "dependency",
    }
}

fn describe_hol_policy_violation(
    report: &HolShadowReport,
    violation: HolReceiptPolicyViolation,
) -> String {
    let named = |id: DeclarationId| {
        report
            .receipt_names
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("declaration {}", id.0))
    };
    match violation {
        HolReceiptPolicyViolation::TrustedAxiomNotAllowed(id) => {
            format!("trusted axiom `{}` is not allowed", named(id))
        }
        HolReceiptPolicyViolation::IncompleteNotAllowed(id) => {
            format!("incomplete declaration `{}` is not allowed", named(id))
        }
        HolReceiptPolicyViolation::DependencyNotAllowed(id) => {
            format!("declaration dependency `{}` is not allowed", named(id))
        }
        other => other.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{check_file_with_hol_shadow, check_file_with_imports_and_hol_shadow, VirtualFile};
    fn policy() -> TeachingPolicy {
        super::super::parse_manifest("version = 1\nprofile = 'prop'\n")
            .unwrap()
            .teaching_policy()
    }
    #[test]
    fn required_theorems_must_be_roots_with_the_exact_signature() {
        let report = check_file_with_hol_shadow("theorem answer : True := by\n  trivial\n");
        let mut required = vec![RequiredTheorem {
            name: "answer".into(),
            signature: report.theorems[0].signature.clone(),
        }];
        let check = |required: &[RequiredTheorem]| {
            check_receipt_requirements(
                &report,
                policy(),
                Some(ReceiptRequirements {
                    allowed_theorem_identities: &[],
                    allowed_axioms: &[],
                    required_theorems: required,
                }),
            )
        };
        assert!(check(&required).is_empty());
        required[0].signature = "False".into();
        assert!(check(&required)
            .iter()
            .any(|v| v.kind == "theorem_signature"));
        let imported = check_file_with_imports_and_hol_shadow(
            "import helper.ctea\n",
            &[VirtualFile {
                path: "helper.ctea".into(),
                source: "theorem answer : True := by\n  trivial\n".into(),
            }],
        );
        let violations = check_receipt_requirements(
            &imported,
            policy(),
            Some(ReceiptRequirements {
                allowed_theorem_identities: &[],
                allowed_axioms: &[],
                required_theorems: &required,
            }),
        );
        assert!(violations.iter().any(|v| v.kind == "required_theorem"));
    }
    #[test]
    fn listing_a_local_axiom_does_not_authorize_it() {
        let report = check_file_with_hol_shadow("axiom allowed : True\n");
        let names = vec!["allowed".into()];
        let violations = check_receipt_requirements(
            &report,
            policy(),
            Some(ReceiptRequirements {
                allowed_theorem_identities: &[],
                allowed_axioms: &names,
                required_theorems: &[],
            }),
        );
        assert!(violations.iter().any(|v| v.kind == "allowed_axiom"));
        assert!(violations.iter().any(|v| v.kind == "trusted_axiom"));
    }
    #[test]
    fn grants_require_an_imported_checked_trust_free_export() {
        let good = "import builtin:std/prop.ctea as P\ntheorem answer : True := by\n  trivial\n";
        let report = check_file_with_hol_shadow(good);
        assert!(report.is_match());
        let imported = report
            .theorems
            .iter()
            .find(|t| t.is_imported && t.hol_status == EvidenceStatus::Checked)
            .unwrap();
        let identity = imported.library_identity.clone().unwrap();
        let check = |names: &[String]| {
            check_receipt_requirements(
                &report,
                policy(),
                Some(ReceiptRequirements {
                    allowed_theorem_identities: names,
                    allowed_axioms: &[],
                    required_theorems: &[],
                }),
            )
        };
        assert!(check(std::slice::from_ref(&identity)).is_empty());
        assert!(check(&["answer".into()])
            .iter()
            .any(|v| v.kind == "allowed_theorem"));
        assert!(check(&[identity.clone(), identity + "_missing"])
            .iter()
            .any(|v| v.kind == "allowed_theorem"));
        for helper in [
            "axiom assumed : True\ntheorem tainted : True := by\n  exact assumed\n",
            "theorem tainted : True := by\n  sorry\n",
        ] {
            let report = check_file_with_imports_and_hol_shadow(
                "import helper.ctea\ntheorem answer : True := by\n  trivial\n",
                &[VirtualFile {
                    path: "helper.ctea".into(),
                    source: helper.into(),
                }],
            );
            let identity = report
                .theorems
                .iter()
                .find(|t| t.name == "tainted")
                .unwrap()
                .library_identity
                .clone()
                .unwrap();
            let violations = check_receipt_requirements(
                &report,
                policy(),
                Some(ReceiptRequirements {
                    allowed_theorem_identities: &[identity],
                    allowed_axioms: &[],
                    required_theorems: &[],
                }),
            );
            assert!(violations.iter().any(|v| v.kind == "allowed_theorem"));
        }
    }
}
