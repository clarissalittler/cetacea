use cetacea_core::hol::{run_linked_hol_smoke, EvidenceStatus};
use cetacea_core::{
    check_file_with_imports_and_hol_shadow, explain_theorem_with_imports_and_hol_shadow,
    goals_at_with_imports_and_hol_shadow, outline, run_tactic_with_imports_and_hol_shadow,
    Diagnostic, DiagnosticSeverity, ExplanationResult, GoalSnapshot, GoalStepResult,
    HolShadowMismatch, HolShadowReport, HolShadowTheorem, LogicMode, Position, SourceOutline,
    VirtualFile,
};

#[no_mangle]
pub extern "C" fn cetacea_alloc(len: usize) -> *mut u8 {
    let mut buf = Vec::<u8>::with_capacity(len);
    let ptr = buf.as_mut_ptr();
    std::mem::forget(buf);
    ptr
}

/// Frees memory allocated by `cetacea_alloc` or returned by another export.
///
/// # Safety
///
/// `ptr` and `len` must match a live allocation returned by this module. The
/// same allocation must not be freed more than once.
#[no_mangle]
pub unsafe extern "C" fn cetacea_free(ptr: *mut u8, len: usize) {
    if !ptr.is_null() {
        drop(Vec::from_raw_parts(ptr, 0, len));
    }
}

#[no_mangle]
pub extern "C" fn cetacea_version() -> *mut u8 {
    response_json(r#"{"version":"0.1.0"}"#.to_string())
}

/// Runs the bounded constructive-HOL spike through its real kernel path.
///
/// This export is intentionally small at the ABI boundary but keeps the HOL
/// engine reachable in release Wasm artifacts, so H3.5 size and latency
/// measurements cannot be artifacts of linker dead-code elimination.
#[no_mangle]
pub extern "C" fn cetacea_hol_spike_smoke() -> *mut u8 {
    match run_linked_hol_smoke() {
        Ok(report) => response_json(format!(
            r#"{{"ok":true,"structural_required":{},"transparent_required":{},"facade_required":{},"polymorphic_required":{},"product_required":{},"set_required":{},"axioms":{},"incomplete":{},"trusted_deps":{},"incomplete_user_deps":{},"classical_features":{}}}"#,
            json_string(&report.structural_required.to_string()),
            json_string(&report.transparent_required.to_string()),
            json_string(&report.facade_required.to_string()),
            json_string(&report.polymorphic_required.to_string()),
            json_string(&report.product_required.to_string()),
            json_string(&report.set_required.to_string()),
            report.axiom_dependencies,
            report.incomplete_dependencies,
            report.trusted_user_axiom_dependencies,
            report.incomplete_user_dependencies,
            report.classical_user_features,
        )),
        Err(error) => response_json(error_json(&error.message)),
    }
}

/// Checks a Cetacea source string and returns a length-prefixed JSON response.
///
/// # Safety
///
/// `source_ptr` must point to `source_len` bytes of readable UTF-8 memory
/// allocated in this wasm instance.
#[no_mangle]
pub unsafe extern "C" fn cetacea_check(source_ptr: *const u8, source_len: usize) -> *mut u8 {
    match read_input(source_ptr, source_len) {
        Ok(source) => response_json(hol_shadow_result_json(
            &check_file_with_imports_and_hol_shadow(&source, &standard_imports()),
        )),
        Err(err) => response_json(error_json(&err)),
    }
}

/// Returns a parsed theorem outline as a length-prefixed JSON response.
///
/// # Safety
///
/// `source_ptr` must point to `source_len` bytes of readable UTF-8 memory
/// allocated in this wasm instance.
#[no_mangle]
pub unsafe extern "C" fn cetacea_outline(source_ptr: *const u8, source_len: usize) -> *mut u8 {
    match read_input(source_ptr, source_len) {
        Ok(source) => response_json(outline_json(&outline(&source))),
        Err(err) => response_json(error_json(&err)),
    }
}

/// Returns the proof goals at a source position as a length-prefixed JSON response.
///
/// # Safety
///
/// `source_ptr` must point to `source_len` bytes of readable UTF-8 memory
/// allocated in this wasm instance.
#[no_mangle]
pub unsafe extern "C" fn cetacea_goals_at(
    source_ptr: *const u8,
    source_len: usize,
    line: usize,
    column: usize,
) -> *mut u8 {
    match read_input(source_ptr, source_len) {
        Ok(source) => response_json(goal_result_json(&goals_at_with_imports_and_hol_shadow(
            &source,
            Position { line, column },
            &standard_imports(),
        ))),
        Err(err) => response_json(error_json(&err)),
    }
}

/// Runs a named theorem through the given tactic index and returns JSON.
///
/// # Safety
///
/// `source_ptr` and `theorem_ptr` must point to readable UTF-8 memory ranges of
/// their corresponding lengths, allocated in this wasm instance.
#[no_mangle]
pub unsafe extern "C" fn cetacea_run_tactic(
    source_ptr: *const u8,
    source_len: usize,
    theorem_ptr: *const u8,
    theorem_len: usize,
    tactic_index: usize,
) -> *mut u8 {
    let source = match read_input(source_ptr, source_len) {
        Ok(source) => source,
        Err(err) => return response_json(error_json(&err)),
    };
    let theorem = match read_input(theorem_ptr, theorem_len) {
        Ok(theorem) => theorem,
        Err(err) => return response_json(error_json(&err)),
    };
    response_json(goal_result_json(&run_tactic_with_imports_and_hol_shadow(
        &source,
        &theorem,
        tactic_index,
        &standard_imports(),
    )))
}

/// Explains a named theorem's tactic script as a length-prefixed JSON response.
///
/// # Safety
///
/// `source_ptr` and `theorem_ptr` must point to readable UTF-8 memory ranges of
/// their corresponding lengths, allocated in this wasm instance.
#[no_mangle]
pub unsafe extern "C" fn cetacea_explain_theorem(
    source_ptr: *const u8,
    source_len: usize,
    theorem_ptr: *const u8,
    theorem_len: usize,
) -> *mut u8 {
    let source = match read_input(source_ptr, source_len) {
        Ok(source) => source,
        Err(err) => return response_json(error_json(&err)),
    };
    let theorem = match read_input(theorem_ptr, theorem_len) {
        Ok(theorem) => theorem,
        Err(err) => return response_json(error_json(&err)),
    };
    response_json(explanation_result_json(
        &explain_theorem_with_imports_and_hol_shadow(&source, &theorem, &standard_imports()),
    ))
}

fn standard_imports() -> Vec<VirtualFile> {
    [
        (
            "std/prelude.ctea",
            include_str!("../../../std/prelude.ctea"),
        ),
        (
            "std/qualified_prelude.ctea",
            include_str!("../../../std/qualified_prelude.ctea"),
        ),
        ("std/prop.ctea", include_str!("../../../std/prop.ctea")),
        ("std/fol.ctea", include_str!("../../../std/fol.ctea")),
        ("std/eq.ctea", include_str!("../../../std/eq.ctea")),
        ("std/nat.ctea", include_str!("../../../std/nat.ctea")),
        ("std/set.ctea", include_str!("../../../std/set.ctea")),
        ("std/list.ctea", include_str!("../../../std/list.ctea")),
        ("std/fun.ctea", include_str!("../../../std/fun.ctea")),
        (
            "std/modular.ctea",
            include_str!("../../../std/modular.ctea"),
        ),
    ]
    .into_iter()
    .map(|(path, source)| VirtualFile {
        path: path.to_string(),
        source: source.to_string(),
    })
    .collect()
}

unsafe fn read_input(ptr: *const u8, len: usize) -> Result<String, String> {
    if ptr.is_null() && len > 0 {
        return Err("input pointer was null".to_string());
    }
    let bytes = std::slice::from_raw_parts(ptr, len);
    String::from_utf8(bytes.to_vec()).map_err(|err| format!("input was not UTF-8: {err}"))
}

fn response_json(json: String) -> *mut u8 {
    let bytes = json.into_bytes();
    let len = bytes.len().min(u32::MAX as usize);
    let mut out = Vec::with_capacity(len + 4);
    out.extend_from_slice(&(len as u32).to_le_bytes());
    out.extend_from_slice(&bytes[..len]);
    let ptr = out.as_mut_ptr();
    std::mem::forget(out);
    ptr
}

fn error_json(message: &str) -> String {
    format!(
        r#"{{"ok":false,"error":{},"diagnostics":[]}}"#,
        json_string(message)
    )
}

fn hol_shadow_result_json(report: &HolShadowReport) -> String {
    let theorems = report
        .legacy
        .theorems
        .iter()
        .map(|theorem| {
            let axiom_deps = theorem
                .axiom_deps
                .iter()
                .map(|name| json_string(name))
                .collect::<Vec<_>>()
                .join(",");
            let hol = report
                .theorems
                .iter()
                .find(|candidate| candidate.name == theorem.name);
            let hol_fields = hol
                .map(|theorem| hol_theorem_fields_json(theorem, report))
                .unwrap_or_else(|| {
                    r#""hol_status":null,"signature":null,"statement_fragment":null,"required_fragment":null,"features":[],"dependencies":[],"hol_axiom_deps":[],"incomplete_deps":[],"receipt_id":null"#.to_string()
                });
            format!(
                r#"{{"name":{},"statement":{},"mode":{},"status":{},"is_axiom":{},"is_imported":{},"uses_sorry":{},"axiom_deps":[{}],{}}}"#,
                json_string(&theorem.name),
                json_string(&theorem.statement),
                json_string(&theorem.mode_used.to_string()),
                json_string(&theorem.status.to_string()),
                theorem.is_axiom,
                theorem.is_imported,
                theorem.uses_sorry,
                axiom_deps,
                hol_fields,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let diagnostics = diagnostics_json(&report.legacy.diagnostics);
    let mismatches = report
        .mismatches
        .iter()
        .map(hol_mismatch_diagnostic_json)
        .collect::<Vec<_>>()
        .join(",");
    let diagnostics = match (diagnostics.is_empty(), mismatches.is_empty()) {
        (true, _) => mismatches,
        (_, true) => diagnostics,
        (false, false) => format!("{diagnostics},{mismatches}"),
    };
    let imported_packages = report
        .imported_packages
        .iter()
        .map(|package| json_string(package))
        .collect::<Vec<_>>()
        .join(",");
    let certified = !diagnostics_have_errors(&report.legacy.diagnostics) && report.is_match();
    format!(
        r#"{{"ok":{},"hol_certified":{},"imported_packages":[{}],"theorems":[{}],"diagnostics":[{}]}}"#,
        certified, certified, imported_packages, theorems, diagnostics,
    )
}

fn hol_theorem_fields_json(theorem: &HolShadowTheorem, report: &HolShadowReport) -> String {
    let features = theorem
        .features
        .iter()
        .map(|feature| json_string(&feature.to_string()))
        .collect::<Vec<_>>()
        .join(",");
    let axiom_deps = theorem
        .axiom_deps
        .iter()
        .map(|name| json_string(name))
        .collect::<Vec<_>>()
        .join(",");
    let dependencies = theorem
        .receipt
        .proof()
        .direct_dependencies()
        .iter()
        .map(|dependency| {
            report
                .receipt_names
                .get(dependency)
                .cloned()
                .unwrap_or_else(|| format!("<declaration:{}>", dependency.0))
        })
        .map(|dependency| json_string(&dependency))
        .collect::<Vec<_>>()
        .join(",");
    let incomplete_deps = theorem
        .incomplete_deps
        .iter()
        .map(|name| json_string(name))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#""hol_status":{},"signature":{},"statement_fragment":{},"required_fragment":{},"features":[{}],"dependencies":[{}],"hol_axiom_deps":[{}],"incomplete_deps":[{}],"receipt_id":{}"#,
        json_string(evidence_status_label(theorem.hol_status)),
        json_string(&theorem.signature),
        json_string(&theorem.statement_fragment.to_string()),
        json_string(&theorem.required_fragment.to_string()),
        features,
        dependencies,
        axiom_deps,
        incomplete_deps,
        theorem.receipt.id().0,
    )
}

fn hol_mismatch_diagnostic_json(mismatch: &HolShadowMismatch) -> String {
    let path = mismatch
        .source_path
        .as_ref()
        .map(|path| json_string(&path.to_string_lossy()))
        .unwrap_or_else(|| "null".to_string());
    let location = format!(r#"{{"path":{},"line":{}}}"#, path, mismatch.line,);
    format!(
        r#"{{"severity":"error","message":{},"location":{},"span":null,"notes":[{}],"suggestions":[]}}"#,
        json_string(&format!(
            "HOL certification failed for {} `{}`",
            mismatch.kind, mismatch.declaration
        )),
        location,
        json_string(&mismatch.message),
    )
}

fn evidence_status_label(status: EvidenceStatus) -> &'static str {
    match status {
        EvidenceStatus::Checked => "checked",
        EvidenceStatus::Incomplete => "incomplete",
        EvidenceStatus::TrustedAxiom => "trusted_axiom",
    }
}

fn outline_json(outline: &SourceOutline) -> String {
    let theorems = outline
        .theorems
        .iter()
        .map(|theorem| {
            let tactics = theorem
                .tactics
                .iter()
                .map(|tactic| {
                    format!(
                        r#"{{"index":{},"line":{},"text":{}}}"#,
                        tactic.index,
                        tactic.line,
                        json_string(&tactic.text)
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            format!(
                r#"{{"name":{},"line":{},"tactic_count":{},"tactics":[{}]}}"#,
                json_string(&theorem.name),
                theorem.line,
                theorem.tactic_count,
                tactics
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"ok":{},"theorems":[{}],"diagnostics":[{}]}}"#,
        !diagnostics_have_errors(&outline.diagnostics),
        theorems,
        diagnostics_json(&outline.diagnostics)
    )
}

fn goal_result_json(result: &GoalStepResult) -> String {
    let goals = goals_json(&result.goals);
    format!(
        r#"{{"ok":{},"theorem":{},"mode":{},"statement_fragment":{},"next_tactic_index":{},"tactic_count":{},"completed":{},"goals":[{}],"diagnostics":[{}]}}"#,
        !diagnostics_have_errors(&result.diagnostics),
        option_string_json(result.theorem.as_deref()),
        mode_json(result.mode),
        fragment_json(result.statement_fragment),
        result.next_tactic_index,
        result.tactic_count,
        result.completed,
        goals,
        diagnostics_json(&result.diagnostics)
    )
}

fn explanation_result_json(result: &ExplanationResult) -> String {
    let steps = result
        .steps
        .iter()
        .map(|step| {
            let explanation = step
                .explanation
                .iter()
                .map(|line| json_string(line))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                r#"{{"index":{},"line":{},"tactic":{},"before":{},"after":[{}],"explanation":[{}]}}"#,
                step.index,
                step.line,
                json_string(&step.tactic),
                goal_json(&step.before),
                goals_json(&step.after),
                explanation
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"ok":{},"theorem":{},"statement":{},"mode":{},"statement_fragment":{},"completed":{},"steps":[{}],"diagnostics":[{}]}}"#,
        !diagnostics_have_errors(&result.diagnostics),
        option_string_json(result.theorem.as_deref()),
        option_string_json(result.statement.as_deref()),
        mode_json(result.mode),
        fragment_json(result.statement_fragment),
        result.completed,
        steps,
        diagnostics_json(&result.diagnostics)
    )
}

fn goals_json(goals: &[GoalSnapshot]) -> String {
    goals.iter().map(goal_json).collect::<Vec<_>>().join(",")
}

fn goal_json(goal: &GoalSnapshot) -> String {
    let context = goal
        .context
        .iter()
        .map(|entry| json_string(entry))
        .collect::<Vec<_>>()
        .join(",");
    let hints = goal
        .hints
        .iter()
        .map(|hint| {
            format!(
                r#"{{"title":{},"tactic":{},"detail":{}}}"#,
                json_string(&hint.title),
                json_string(&hint.tactic),
                json_string(&hint.detail)
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"id":{},"context":[{}],"target":{},"hints":[{}]}}"#,
        goal.id,
        context,
        json_string(&goal.target),
        hints
    )
}

fn diagnostics_json(diagnostics: &[Diagnostic]) -> String {
    diagnostics
        .iter()
        .map(diagnostic_json)
        .collect::<Vec<_>>()
        .join(",")
}

fn diagnostic_json(diagnostic: &Diagnostic) -> String {
    let location = diagnostic
        .location
        .as_ref()
        .map(|location| {
            format!(
                r#"{{"path":{},"line":{}}}"#,
                option_string_json(location.path.as_deref()),
                location.line
            )
        })
        .unwrap_or_else(|| "null".to_string());
    let span = diagnostic
        .span
        .as_ref()
        .map(|span| format!(r#"{{"start":{},"end":{}}}"#, span.start, span.end))
        .unwrap_or_else(|| "null".to_string());
    let notes = diagnostic
        .notes
        .iter()
        .map(|note| json_string(note))
        .collect::<Vec<_>>()
        .join(",");
    let suggestions = diagnostic
        .suggestions
        .iter()
        .map(|suggestion| {
            format!(
                r#"{{"title":{},"detail":{},"example":{}}}"#,
                json_string(&suggestion.title),
                json_string(&suggestion.detail),
                option_string_json(suggestion.example.as_deref())
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"severity":{},"message":{},"location":{},"span":{},"notes":[{}],"suggestions":[{}]}}"#,
        json_string(diagnostic_severity_label(diagnostic.severity)),
        json_string(&diagnostic.message),
        location,
        span,
        notes,
        suggestions
    )
}

fn diagnostic_severity_label(severity: DiagnosticSeverity) -> &'static str {
    match severity {
        DiagnosticSeverity::Error => "error",
        DiagnosticSeverity::Warning => "warning",
    }
}

fn diagnostics_have_errors(diagnostics: &[Diagnostic]) -> bool {
    diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
}

fn mode_json(mode: Option<LogicMode>) -> String {
    mode.map(|mode| json_string(&mode.to_string()))
        .unwrap_or_else(|| "null".to_string())
}

fn fragment_json(fragment: Option<cetacea_core::hol::StatementFragment>) -> String {
    fragment
        .map(|fragment| json_string(&fragment.to_string()))
        .unwrap_or_else(|| "null".to_string())
}

fn option_string_json(value: Option<&str>) -> String {
    value.map(json_string).unwrap_or_else(|| "null".to_string())
}

fn json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linked_hol_smoke_exercises_kernel_features_and_reports_trust() {
        let ptr = cetacea_hol_spike_smoke();
        assert!(!ptr.is_null());
        let (json, allocation_len) = unsafe {
            let prefix = std::slice::from_raw_parts(ptr, 4);
            let payload_len =
                u32::from_le_bytes(prefix.try_into().expect("four-byte length")) as usize;
            let payload = std::slice::from_raw_parts(ptr.add(4), payload_len);
            (
                std::str::from_utf8(payload)
                    .expect("smoke JSON is UTF-8")
                    .to_string(),
                payload_len + 4,
            )
        };
        unsafe { cetacea_free(ptr, allocation_len) };

        assert!(json.contains(r#""ok":true"#), "{json}");
        assert!(
            json.contains(r#""structural_required":"fol+induction""#),
            "{json}"
        );
        assert!(
            json.contains(r#""transparent_required":"fol+induction""#),
            "{json}"
        );
        assert!(
            json.contains(r#""facade_required":"fol+induction""#),
            "{json}"
        );
        assert!(json.contains(r#""polymorphic_required":"fol""#), "{json}");
        assert!(json.contains(r#""product_required":"fol""#), "{json}");
        assert!(json.contains(r#""set_required":"fol""#), "{json}");
        assert!(json.contains(r#""axioms":0"#), "{json}");
        assert!(json.contains(r#""incomplete":0"#), "{json}");
        assert!(json.contains(r#""trusted_deps":1"#), "{json}");
        assert!(json.contains(r#""incomplete_user_deps":1"#), "{json}");
        assert!(json.contains(r#""classical_features":1"#), "{json}");
    }

    #[test]
    fn browser_endpoints_accept_and_certify_a_logical_list_import() {
        let source = r#"import std/hol/list@1 as L

theorem length_append_use (A : Type) (xs ys : L.List A) :
  L.length(L.append(xs, ys)) = add(L.length(xs), L.length(ys)) := by
  exact L.length_append {A := A; xs := xs; ys := ys}
"#;
        let imports = standard_imports();
        let report = check_file_with_imports_and_hol_shadow(source, &imports);
        assert!(report.legacy.diagnostics.is_empty());
        assert!(report.is_match(), "mismatches: {:#?}", report.mismatches);
        let json = hol_shadow_result_json(&report);
        for expected in [
            r#""ok":true"#,
            r#""hol_certified":true"#,
            r#""imported_packages":["std/hol/list@1"]"#,
            r#""hol_status":"checked""#,
            r#""required_fragment":"fol+induction""#,
            r#"std/hol/list@1::length_append"#,
        ] {
            assert!(json.contains(expected), "missing {expected} in {json}");
        }

        let goals =
            goals_at_with_imports_and_hol_shadow(source, Position { line: 5, column: 1 }, &imports);
        assert!(goals.diagnostics.is_empty(), "{:#?}", goals.diagnostics);
        assert_eq!(goals.goals.len(), 1);
        assert_eq!(
            goals.statement_fragment,
            Some(cetacea_core::hol::StatementFragment::FirstOrderInductive)
        );
        assert!(goal_result_json(&goals).contains(r#""statement_fragment":"fol+induction""#));

        let stepped =
            run_tactic_with_imports_and_hol_shadow(source, "length_append_use", 0, &imports);
        assert!(stepped.diagnostics.is_empty(), "{:#?}", stepped.diagnostics);
        assert!(stepped.completed);

        let explanation =
            explain_theorem_with_imports_and_hol_shadow(source, "length_append_use", &imports);
        assert!(
            explanation.diagnostics.is_empty(),
            "{:#?}",
            explanation.diagnostics
        );
        assert!(explanation.completed);
        assert_eq!(explanation.steps.len(), 1);
        assert!(explanation_result_json(&explanation)
            .contains(r#""statement_fragment":"fol+induction""#));

        let rejected = check_file_with_imports_and_hol_shadow(
            "theorem bad : True := by\n  exact missing\n",
            &imports,
        );
        let rejected_json = hol_shadow_result_json(&rejected);
        assert!(rejected_json.contains(r#""ok":false"#), "{rejected_json}");
        assert!(
            rejected_json.contains(r#""hol_certified":false"#),
            "{rejected_json}"
        );
    }

    #[test]
    fn browser_check_certifies_the_finite_package_and_its_dependency() {
        let source = include_str!("../../../docs/hol/examples/finite_one.ctea");
        let report = check_file_with_imports_and_hol_shadow(source, &standard_imports());
        assert!(
            report.legacy.diagnostics.is_empty(),
            "{:#?}",
            report.legacy.diagnostics
        );
        assert!(report.is_match(), "mismatches: {:#?}", report.mismatches);
        let json = hol_shadow_result_json(&report);
        for expected in [
            r#""ok":true"#,
            r#""hol_certified":true"#,
            r#""imported_packages":["std/hol/finite@1","std/hol/list@1"]"#,
            r#""required_fragment":"fol+induction""#,
            r#""features":["induction","structural-recursion"]"#,
            r#"std/hol/finite@1::has_card_intro"#,
        ] {
            assert!(json.contains(expected), "missing {expected} in {json}");
        }
    }

    #[test]
    fn browser_check_certifies_cardinality_transport_and_its_dependency() {
        let source = include_str!("../../../docs/hol/examples/cardinality_map_length.ctea");
        let report = check_file_with_imports_and_hol_shadow(source, &standard_imports());
        assert!(
            report.legacy.diagnostics.is_empty(),
            "{:#?}",
            report.legacy.diagnostics
        );
        assert!(report.is_match(), "mismatches: {:#?}", report.mismatches);
        let json = hol_shadow_result_json(&report);
        for expected in [
            r#""ok":true"#,
            r#""hol_certified":true"#,
            r#""imported_packages":["std/hol/cardinality@1","std/hol/list@1"]"#,
            r#""required_fragment":"hol""#,
            r#"std/hol/cardinality@1::map_length_schema"#,
            r#"std/hol/cardinality@1::cardinality_transport_schema"#,
            r#"std/hol/cardinality@1::nodup_map_injective_schema"#,
            r#"std/hol/cardinality@1::map_coverage_surjective_schema"#,
        ] {
            assert!(json.contains(expected), "missing {expected} in {json}");
        }
    }

    #[test]
    fn browser_check_certifies_the_finite_vertical_pilot() {
        let traffic = include_str!("../../../docs/hol/examples/finite_traffic.ctea");
        let traffic_report = check_file_with_imports_and_hol_shadow(traffic, &standard_imports());
        assert!(
            traffic_report.legacy.diagnostics.is_empty(),
            "{:#?}",
            traffic_report.legacy.diagnostics
        );
        assert!(
            traffic_report.is_match(),
            "mismatches: {:#?}",
            traffic_report.mismatches
        );
        let traffic_json = hol_shadow_result_json(&traffic_report);
        for expected in [
            r#""hol_certified":true"#,
            r#""required_fragment":"fol+induction""#,
            r#""imported_packages":["std/hol/finite@1","std/hol/list@1"]"#,
        ] {
            assert!(
                traffic_json.contains(expected),
                "missing {expected} in {traffic_json}"
            );
        }

        let bijection = include_str!("../../../docs/hol/examples/finite_bijection.ctea");
        let bijection_report =
            check_file_with_imports_and_hol_shadow(bijection, &standard_imports());
        assert!(
            bijection_report.legacy.diagnostics.is_empty(),
            "{:#?}",
            bijection_report.legacy.diagnostics
        );
        assert!(
            bijection_report.is_match(),
            "mismatches: {:#?}",
            bijection_report.mismatches
        );
        let bijection_json = hol_shadow_result_json(&bijection_report);
        for expected in [
            r#""hol_certified":true"#,
            r#""required_fragment":"hol""#,
            r#""imported_packages":["std/hol/cardinality@1","std/hol/finite@1","std/hol/list@1"]"#,
            r#"std/hol/finite@1::has_card_nodup"#,
            r#"std/hol/finite@1::has_card_length"#,
            r#"std/hol/finite@1::has_card_coverage"#,
        ] {
            assert!(
                bijection_json.contains(expected),
                "missing {expected} in {bijection_json}"
            );
        }
    }

    #[test]
    fn browser_check_certifies_the_finite_textbook_extension() {
        let finite = include_str!("../../../docs/book/hol-code/ch13-solutions.ctea");
        let finite_report = check_file_with_imports_and_hol_shadow(finite, &standard_imports());
        assert!(
            finite_report.legacy.diagnostics.is_empty(),
            "{:#?}",
            finite_report.legacy.diagnostics
        );
        assert!(
            finite_report.is_match(),
            "mismatches: {:#?}",
            finite_report.mismatches
        );
        let finite_json = hol_shadow_result_json(&finite_report);
        for expected in [
            r#""hol_certified":true"#,
            r#""required_fragment":"fol+induction""#,
            r#""name":"ex13_4""#,
            r#""imported_packages":["std/hol/finite@1","std/hol/list@1"]"#,
        ] {
            assert!(
                finite_json.contains(expected),
                "missing {expected} in {finite_json}"
            );
        }

        let bijections = include_str!("../../../docs/book/hol-code/ch14-solutions.ctea");
        let bijection_report =
            check_file_with_imports_and_hol_shadow(bijections, &standard_imports());
        assert!(
            bijection_report.legacy.diagnostics.is_empty(),
            "{:#?}",
            bijection_report.legacy.diagnostics
        );
        assert!(
            bijection_report.is_match(),
            "mismatches: {:#?}",
            bijection_report.mismatches
        );
        let bijection_json = hol_shadow_result_json(&bijection_report);
        for expected in [
            r#""hol_certified":true"#,
            r#""required_fragment":"hol""#,
            r#""name":"ex14_7""#,
            r#""imported_packages":["std/hol/cardinality@1","std/hol/finite@1","std/hol/list@1"]"#,
        ] {
            assert!(
                bijection_json.contains(expected),
                "missing {expected} in {bijection_json}"
            );
        }

        let pigeonhole = include_str!("../../../docs/book/hol-code/ch15-solutions.ctea");
        let pigeonhole_report =
            check_file_with_imports_and_hol_shadow(pigeonhole, &standard_imports());
        assert!(
            pigeonhole_report.legacy.diagnostics.is_empty(),
            "{:#?}",
            pigeonhole_report.legacy.diagnostics
        );
        assert!(
            pigeonhole_report.is_match(),
            "mismatches: {:#?}",
            pigeonhole_report.mismatches
        );
        let pigeonhole_json = hol_shadow_result_json(&pigeonhole_report);
        for expected in [
            r#""hol_certified":true"#,
            r#""required_fragment":"hol""#,
            r#""name":"ex15_6""#,
            r#""imported_packages":["std/hol/cardinality@1","std/hol/finite@1","std/hol/list@1"]"#,
            r#"std/hol/cardinality@1::map_nil"#,
            r#"std/hol/cardinality@1::map_cons"#,
        ] {
            assert!(
                pigeonhole_json.contains(expected),
                "missing {expected} in {pigeonhole_json}"
            );
        }
    }
}
