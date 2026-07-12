mod assignment;

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{self, Command, Stdio};

use cetacea_core::hol::{
    run_linked_hol_smoke, DeclarationId, EvidenceStatus, LibraryPackageId,
    PolicyViolation as HolReceiptPolicyViolation, ReceiptPolicy, TeachingProfile,
};
use cetacea_core::{
    check_file_at_path, check_file_at_path_with_hol_shadow, check_source_at_path,
    check_source_at_path_with_hol_shadow, explain_theorem_at_path,
    explain_theorem_at_path_with_hol_shadow, explain_theorem_in_source_at_path,
    explain_theorem_in_source_at_path_with_hol_shadow, goals_at_path,
    goals_at_path_with_hol_shadow, goals_at_source_path, goals_at_source_path_with_hol_shadow,
    outline, run_tactic_at_path, run_tactic_at_path_with_hol_shadow, CheckResult, CheckedTheorem,
    DeclarationStatus, Diagnostic, DiagnosticSeverity, ExplanationResult, GoalSnapshot,
    GoalStepResult, HolShadowMismatch, HolShadowReport, HolShadowStatementClassification,
    HolShadowTheorem, Position, SourceLocation, SourceOutline,
};

use assignment::{parse_manifest, AssignmentManifest};

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args == ["--hol-smoke"] {
        match run_linked_hol_smoke() {
            Ok(report) => println!(
                "structural={} transparent={} facade={} polymorphic={} product={} set={} axioms={} incomplete={} trusted_deps={} incomplete_user_deps={} classical_features={}",
                report.structural_required,
                report.transparent_required,
                report.facade_required,
                report.polymorphic_required,
                report.product_required,
                report.set_required,
                report.axiom_dependencies,
                report.incomplete_dependencies,
                report.trusted_user_axiom_dependencies,
                report.incomplete_user_dependencies,
                report.classical_user_features,
            ),
            Err(error) => {
                eprintln!("error: HOL smoke failed: {error}");
                process::exit(1);
            }
        }
        return;
    }
    if args.iter().any(|arg| arg == "-h" || arg == "--help") {
        print_usage();
        return;
    }
    let Some(config) = parse_args(&args) else {
        print_usage();
        process::exit(2);
    };

    match config.mode {
        RunMode::Check => process::exit(run_check(
            &config.path,
            config.policy,
            config.output_format,
            config.hol_shadow,
            config.hol_policy,
            config.assignment_path.as_deref(),
        )),
        RunMode::LineInteractive => {
            if let Err(err) = run_interactive(config.path, config.hol_shadow) {
                eprintln!("error: {err}");
                process::exit(1);
            }
        }
        RunMode::Tui => {
            if let Err(err) = run_tui(config.path, config.hol_shadow) {
                eprintln!("error: {err}");
                process::exit(1);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RunMode {
    Check,
    LineInteractive,
    Tui,
}

struct CliConfig {
    mode: RunMode,
    path: PathBuf,
    policy: CheckPolicy,
    output_format: OutputFormat,
    hol_shadow: bool,
    hol_policy: Option<HolTeachingPolicy>,
    assignment_path: Option<PathBuf>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct CheckPolicy {
    deny_sorry: bool,
    deny_root_axioms: bool,
    deny_classical: bool,
}

impl CheckPolicy {
    fn strict() -> Self {
        Self {
            deny_sorry: true,
            deny_root_axioms: true,
            deny_classical: false,
        }
    }

    fn is_empty(self) -> bool {
        !self.deny_sorry && !self.deny_root_axioms && !self.deny_classical
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct HolTeachingPolicy {
    profile: TeachingProfile,
    allow_classical: bool,
    allow_extensionality: bool,
    allow_choice: bool,
    allow_axioms: bool,
    allow_incomplete: bool,
}

impl HolTeachingPolicy {
    fn profile_label(self) -> &'static str {
        match self.profile {
            TeachingProfile::Prop => "prop",
            TeachingProfile::FirstOrder => "fol",
            TeachingProfile::FirstOrderInductive => "fol+induction",
            TeachingProfile::HigherOrder => "hol",
        }
    }
}

#[derive(Clone, Debug)]
struct LoadedAssignment {
    path: PathBuf,
    manifest: AssignmentManifest,
    allowed_imports: BTreeSet<PathBuf>,
    allowed_package_imports: BTreeSet<String>,
}

impl LoadedAssignment {
    fn teaching_policy(&self) -> HolTeachingPolicy {
        HolTeachingPolicy {
            profile: self.manifest.profile,
            allow_classical: self.manifest.allow_classical,
            allow_extensionality: self.manifest.allow_extensionality,
            allow_choice: self.manifest.allow_choice,
            allow_axioms: self.manifest.allow_new_axioms,
            allow_incomplete: self.manifest.allow_incomplete,
        }
    }
}

fn parse_hol_profile(value: &str) -> Option<TeachingProfile> {
    match value {
        "prop" => Some(TeachingProfile::Prop),
        "fol" => Some(TeachingProfile::FirstOrder),
        "fol+induction" | "fol-induction" => Some(TeachingProfile::FirstOrderInductive),
        "hol" => Some(TeachingProfile::HigherOrder),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum OutputFormat {
    #[default]
    Text,
    Json,
}

fn parse_args(args: &[String]) -> Option<CliConfig> {
    let mut mode = RunMode::Check;
    let mut path = None;
    let mut policy = CheckPolicy::default();
    let mut output_format = OutputFormat::Text;
    let mut hol_shadow = false;
    let mut hol_profile = None;
    let mut allow_classical = false;
    let mut allow_axioms = false;
    let mut allow_incomplete = false;
    let mut assignment_path = None;
    let mut index = 0usize;
    while index < args.len() {
        let arg = &args[index];
        match arg.as_str() {
            "-i" | "--interactive" | "--tui" => mode = RunMode::Tui,
            "--line" | "--repl" => mode = RunMode::LineInteractive,
            "--strict" => {
                let strict = CheckPolicy::strict();
                policy.deny_sorry |= strict.deny_sorry;
                policy.deny_root_axioms |= strict.deny_root_axioms;
            }
            "--deny-sorry" => policy.deny_sorry = true,
            "--deny-axioms" => policy.deny_root_axioms = true,
            "--deny-classical" => policy.deny_classical = true,
            "--json" => output_format = OutputFormat::Json,
            "--hol-shadow" => hol_shadow = true,
            "--allow-classical" => allow_classical = true,
            "--allow-axioms" => allow_axioms = true,
            "--allow-incomplete" => allow_incomplete = true,
            "--hol-profile" => {
                index += 1;
                let profile = parse_hol_profile(args.get(index)?.as_str())?;
                if hol_profile.replace(profile).is_some() {
                    return None;
                }
            }
            value if value.starts_with("--hol-profile=") => {
                let profile = parse_hol_profile(value.split_once('=')?.1)?;
                if hol_profile.replace(profile).is_some() {
                    return None;
                }
            }
            "--assignment" => {
                index += 1;
                let path = PathBuf::from(args.get(index)?);
                if assignment_path.replace(path).is_some() {
                    return None;
                }
            }
            value if value.starts_with("--assignment=") => {
                let path = PathBuf::from(value.split_once('=')?.1);
                if path.as_os_str().is_empty() || assignment_path.replace(path).is_some() {
                    return None;
                }
            }
            _ if arg.starts_with('-') => return None,
            _ if path.is_none() => path = Some(PathBuf::from(arg)),
            _ => return None,
        }
        index += 1;
    }

    if hol_profile.is_none()
        && assignment_path.is_none()
        && (allow_classical || allow_axioms || allow_incomplete)
    {
        return None;
    }
    if assignment_path.is_some()
        && (hol_profile.is_some() || allow_classical || allow_axioms || allow_incomplete)
    {
        return None;
    }
    if (allow_classical && policy.deny_classical)
        || (allow_axioms && policy.deny_root_axioms)
        || (allow_incomplete && policy.deny_sorry)
    {
        return None;
    }
    let hol_policy = hol_profile.map(|profile| HolTeachingPolicy {
        profile,
        allow_classical,
        allow_extensionality: false,
        allow_choice: false,
        allow_axioms,
        allow_incomplete,
    });
    hol_shadow |= hol_policy.is_some() || assignment_path.is_some();

    if mode != RunMode::Check
        && (!policy.is_empty()
            || output_format != OutputFormat::Text
            || hol_policy.is_some()
            || assignment_path.is_some())
    {
        return None;
    }

    Some(CliConfig {
        mode,
        path: path?,
        policy,
        output_format,
        hol_shadow,
        hol_policy,
        assignment_path,
    })
}

fn print_usage() {
    eprintln!(
        "usage: cetacea [--tui|--interactive|-i|--line] [--strict|--deny-sorry|--deny-axioms|--deny-classical] [--json] [--hol-shadow] [--hol-profile prop|fol|fol+induction|hol [--allow-classical] [--allow-axioms] [--allow-incomplete] | --assignment manifest.ctea-assignment] <file.ctea>\n       cetacea --hol-smoke"
    );
}

fn load_assignment(path: &Path) -> Result<LoadedAssignment, String> {
    let canonical_path = path
        .canonicalize()
        .map_err(|error| format!("could not read `{}`: {error}", path.display()))?;
    let source = fs::read_to_string(&canonical_path)
        .map_err(|error| format!("could not read `{}`: {error}", canonical_path.display()))?;
    let manifest = parse_manifest(&source).map_err(|error| error.to_string())?;
    let base = canonical_path
        .parent()
        .expect("canonical manifest path should have a parent");
    let mut allowed_imports = BTreeSet::new();
    let mut allowed_package_imports = BTreeSet::new();
    for import in &manifest.allowed_imports {
        if let Some(package) = LibraryPackageId::from_logical_id(import) {
            let logical_id = package.to_string();
            if !allowed_package_imports.insert(logical_id.clone()) {
                return Err(format!("allowed package import `{logical_id}` is repeated"));
            }
            continue;
        }
        let raw = Path::new(import);
        let candidate = if raw.is_absolute() {
            raw.to_path_buf()
        } else {
            base.join(raw)
        };
        let resolved = candidate.canonicalize().map_err(|error| {
            format!(
                "allowed import `{import}` could not be resolved relative to `{}`: {error}",
                base.display()
            )
        })?;
        if !allowed_imports.insert(resolved) {
            return Err(format!(
                "allowed import `{import}` resolves to the same file as another entry"
            ));
        }
    }
    Ok(LoadedAssignment {
        path: canonical_path,
        manifest,
        allowed_imports,
        allowed_package_imports,
    })
}

fn print_assignment_load_error(format: OutputFormat, path: &Path, message: &str) {
    match format {
        OutputFormat::Text => eprintln!(
            "error: could not load assignment manifest `{}`: {message}",
            path.display()
        ),
        OutputFormat::Json => println!(
            r#"{{"ok":false,"assignment_error":{{"path":{},"message":{}}}}}"#,
            json_string(&path.to_string_lossy()),
            json_string(message),
        ),
    }
}

fn run_check(
    path: &Path,
    policy: CheckPolicy,
    output_format: OutputFormat,
    run_hol_shadow: bool,
    cli_hol_policy: Option<HolTeachingPolicy>,
    assignment_path: Option<&Path>,
) -> i32 {
    let assignment = match assignment_path.map(load_assignment).transpose() {
        Ok(assignment) => assignment,
        Err(error) => {
            print_assignment_load_error(
                output_format,
                assignment_path.expect("failed assignment must have a path"),
                &error,
            );
            return 2;
        }
    };
    let hol_policy =
        cli_hol_policy.or_else(|| assignment.as_ref().map(LoadedAssignment::teaching_policy));
    let requested_hol = run_hol_shadow || hol_policy.is_some();
    let mut automatic_hol = false;
    let mut standalone = None;
    let shadow = if requested_hol {
        Some(check_file_at_path_with_hol_shadow(path))
    } else {
        let checked = check_file_at_path(path);
        if checked.requires_hol_shadow {
            automatic_hol = true;
            Some(check_file_at_path_with_hol_shadow(path))
        } else {
            standalone = Some(checked);
            None
        }
    };
    let result = if let Some(shadow) = &shadow {
        &shadow.legacy
    } else {
        standalone
            .as_ref()
            .expect("a non-HOL check retains its standalone result")
    };
    let violations = check_policy_violations(&result, policy);
    let hol_violations = shadow
        .as_ref()
        .zip(hol_policy)
        .map(|(shadow, policy)| check_hol_policy_violations(shadow, policy, assignment.as_ref()))
        .unwrap_or_default();
    match output_format {
        OutputFormat::Text => {
            print_accepted(&result);
            if !result.diagnostics.is_empty() {
                print_diagnostics(&result.diagnostics);
            }
            print_policy_violations(&violations);
            if let Some(shadow) = &shadow {
                print_hol_shadow(shadow, automatic_hol);
            }
            print_hol_policy_violations(&hol_violations, hol_policy);
        }
        OutputFormat::Json => println!(
            "{}",
            check_result_json(
                result,
                policy,
                &violations,
                shadow.as_ref(),
                hol_policy,
                &hol_violations,
                assignment.as_ref(),
            )
        ),
    }
    if diagnostics_have_errors(&result.diagnostics)
        || !violations.is_empty()
        || !hol_violations.is_empty()
        || shadow.as_ref().is_some_and(|shadow| !shadow.is_match())
    {
        1
    } else {
        0
    }
}

fn print_hol_shadow(report: &HolShadowReport, automatic: bool) {
    let label = if automatic {
        "HOL package check"
    } else {
        "HOL shadow"
    };
    if report.is_match() {
        println!(
            "{label} matched {} accepted declarations ({} theorem receipts).",
            report.checked_declarations.len(),
            report.theorems.len()
        );
        return;
    }
    eprintln!(
        "error: {label} disagreed on {} of {} accepted declaration attempts",
        report.mismatches.len(),
        report.attempted_declarations
    );
    for mismatch in &report.mismatches {
        let path = mismatch
            .source_path
            .as_ref()
            .map(|path| display_diagnostic_path(&path.to_string_lossy()))
            .map(|path| format!("{path}:{}: ", mismatch.line))
            .unwrap_or_else(|| format!("line {}: ", mismatch.line));
        eprintln!(
            "  {path}{} `{}`: {}",
            mismatch.kind, mismatch.declaration, mismatch.message
        );
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct HolPolicyViolation {
    declaration: String,
    kind: &'static str,
    message: String,
}

fn check_hol_policy_violations(
    report: &HolShadowReport,
    config: HolTeachingPolicy,
    assignment: Option<&LoadedAssignment>,
) -> Vec<HolPolicyViolation> {
    let mut policy = ReceiptPolicy::new(config.profile);
    if config.allow_classical {
        policy.allow_classical();
    }
    if config.allow_extensionality {
        policy.allow_extensionality();
    }
    if config.allow_choice {
        policy.allow_choice();
    }
    if config.allow_axioms {
        policy.allow_any_axiom();
    }
    if config.allow_incomplete {
        policy.allow_incomplete();
    }

    let mut violations = Vec::new();
    if let Some(assignment) = assignment {
        for name in &assignment.manifest.allowed_axioms {
            match report.theorems.iter().find(|theorem| theorem.name == *name) {
                Some(theorem)
                    if theorem.hol_status == EvidenceStatus::TrustedAxiom
                        && theorem.is_imported =>
                {
                    policy.allow_axiom(theorem.receipt.id());
                }
                Some(theorem) if theorem.hol_status != EvidenceStatus::TrustedAxiom => {
                    violations.push(HolPolicyViolation {
                        declaration: name.clone(),
                        kind: "allowed_axiom",
                        message: "manifest entry does not name a trusted axiom".to_string(),
                    });
                }
                Some(_) => violations.push(HolPolicyViolation {
                    declaration: name.clone(),
                    kind: "allowed_axiom",
                    message: "manifest may allow only imported trusted axioms".to_string(),
                }),
                None => violations.push(HolPolicyViolation {
                    declaration: name.clone(),
                    kind: "allowed_axiom",
                    message: "manifest entry does not resolve to a checked declaration".to_string(),
                }),
            }
        }

        for path in &report.imported_files {
            if !assignment.allowed_imports.contains(path) {
                let displayed = display_diagnostic_path(&path.to_string_lossy());
                violations.push(HolPolicyViolation {
                    declaration: displayed.clone(),
                    kind: "import",
                    message: format!("resolved import `{displayed}` is not allowed"),
                });
            }
        }
        for path in &report.imported_virtual_files {
            violations.push(HolPolicyViolation {
                declaration: path.clone(),
                kind: "import",
                message: format!("virtual import `{path}` is not allowed by a native manifest"),
            });
        }
        for package in &report.imported_packages {
            if !assignment.allowed_package_imports.contains(package) {
                violations.push(HolPolicyViolation {
                    declaration: package.clone(),
                    kind: "import",
                    message: format!("logical package import `{package}` is not allowed"),
                });
            }
        }

        for required in &assignment.manifest.required_theorems {
            match report
                .theorems
                .iter()
                .find(|theorem| !theorem.is_imported && theorem.name == required.name)
            {
                None => violations.push(HolPolicyViolation {
                    declaration: required.name.clone(),
                    kind: "required_theorem",
                    message: "required root theorem is missing".to_string(),
                }),
                Some(theorem) if theorem.signature != required.signature => {
                    violations.push(HolPolicyViolation {
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
            HolPolicyViolation {
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

fn print_hol_policy_violations(
    violations: &[HolPolicyViolation],
    policy: Option<HolTeachingPolicy>,
) {
    let Some(policy) = policy else {
        return;
    };
    for violation in violations {
        eprintln!(
            "error: HOL policy `{}`: declaration `{}`: {}",
            policy.profile_label(),
            violation.declaration,
            violation.message
        );
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PolicyViolationKind {
    Sorry,
    RootAxiom,
    Classical,
}

impl PolicyViolationKind {
    fn label(self) -> &'static str {
        match self {
            Self::Sorry => "sorry",
            Self::RootAxiom => "root_axiom",
            Self::Classical => "classical",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PolicyViolation {
    kind: PolicyViolationKind,
    declaration: String,
    message: String,
}

fn check_policy_violations(result: &CheckResult, policy: CheckPolicy) -> Vec<PolicyViolation> {
    let mut violations = Vec::new();
    for theorem in result
        .theorems
        .iter()
        .filter(|theorem| !theorem.is_imported)
    {
        if policy.deny_sorry && theorem.uses_sorry {
            violations.push(PolicyViolation {
                kind: PolicyViolationKind::Sorry,
                declaration: theorem.name.clone(),
                message: format!(
                    "theorem `{}` is incomplete because it uses `sorry` directly or transitively",
                    theorem.name
                ),
            });
        }
        if policy.deny_root_axioms && theorem.is_axiom {
            violations.push(PolicyViolation {
                kind: PolicyViolationKind::RootAxiom,
                declaration: theorem.name.clone(),
                message: format!(
                    "root axiom `{}` is not allowed by the checking policy",
                    theorem.name
                ),
            });
        }
        if policy.deny_classical
            && !theorem.is_axiom
            && theorem.mode_used == cetacea_core::LogicMode::Classical
        {
            violations.push(PolicyViolation {
                kind: PolicyViolationKind::Classical,
                declaration: theorem.name.clone(),
                message: format!(
                    "theorem `{}` uses classical reasoning, which is not allowed by the checking policy",
                    theorem.name
                ),
            });
        }
    }
    violations
}

fn print_policy_violations(violations: &[PolicyViolation]) {
    for violation in violations {
        eprintln!("error: policy: {}", violation.message);
    }
}

fn run_tui(path: PathBuf, hol_shadow: bool) -> io::Result<()> {
    let mut app = TuiApp::open(path, hol_shadow)?;
    let _guard = TerminalGuard::enter()?;
    app.refresh_analysis();
    let mut stdout = io::stdout();
    let mut stdin = io::stdin();
    let mut needs_draw = true;

    loop {
        if needs_draw {
            let (rows, cols) = terminal_size();
            app.draw(&mut stdout, rows, cols)?;
            needs_draw = false;
        }
        if app.should_quit {
            break;
        }
        if let Some(key) = read_key(&mut stdin)? {
            app.handle_key(key);
            needs_draw = true;
        }
    }

    Ok(())
}

struct TerminalGuard {
    saved_stty: String,
}

impl TerminalGuard {
    fn enter() -> io::Result<Self> {
        let output = Command::new("stty")
            .arg("-g")
            .stdin(Stdio::inherit())
            .output()?;
        let saved_stty = String::from_utf8_lossy(&output.stdout).trim().to_string();
        let status = Command::new("stty")
            .args(["raw", "-echo", "min", "0", "time", "1"])
            .stdin(Stdio::inherit())
            .status()?;
        if !status.success() {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "failed to put terminal in raw mode",
            ));
        }
        print!("\x1b[?1049h\x1b[?25l\x1b[2J\x1b[H");
        io::stdout().flush()?;
        Ok(Self { saved_stty })
    }
}

impl Drop for TerminalGuard {
    fn drop(&mut self) {
        if !self.saved_stty.is_empty() {
            let _ = Command::new("stty")
                .arg(&self.saved_stty)
                .stdin(Stdio::inherit())
                .status();
        }
        print!("\x1b[0m\x1b[?25h\x1b[?1049l");
        let _ = io::stdout().flush();
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Key {
    Char(char),
    Ctrl(char),
    Backspace,
    Delete,
    Enter,
    Esc,
    Tab,
    Up,
    Down,
    Left,
    Right,
    PageUp,
    PageDown,
    Home,
    End,
    F(u8),
}

fn read_key(stdin: &mut io::Stdin) -> io::Result<Option<Key>> {
    let mut byte = [0_u8; 1];
    if stdin.read(&mut byte)? == 0 {
        return Ok(None);
    }
    match byte[0] {
        b'\r' | b'\n' => Ok(Some(Key::Enter)),
        b'\t' => Ok(Some(Key::Tab)),
        0x7f | 0x08 => Ok(Some(Key::Backspace)),
        0x01..=0x1a => Ok(Some(Key::Ctrl((byte[0] + b'a' - 1) as char))),
        0x1b => read_escape_key(stdin),
        byte if byte.is_ascii_graphic() || byte == b' ' => Ok(Some(Key::Char(byte as char))),
        _ => Ok(None),
    }
}

fn read_escape_key(stdin: &mut io::Stdin) -> io::Result<Option<Key>> {
    let mut seq = [0_u8; 6];
    let mut len = 0;
    while len < seq.len() {
        let read = stdin.read(&mut seq[len..len + 1])?;
        if read == 0 {
            break;
        }
        len += read;
        if len >= 2 && (seq[len - 1].is_ascii_alphabetic() || seq[len - 1] == b'~') {
            break;
        }
    }
    if len == 0 {
        return Ok(Some(Key::Esc));
    }
    let key = match &seq[..len] {
        b"[A" => Key::Up,
        b"[B" => Key::Down,
        b"[C" => Key::Right,
        b"[D" => Key::Left,
        b"[H" | b"OH" => Key::Home,
        b"[F" | b"OF" => Key::End,
        b"[3~" => Key::Delete,
        b"[5~" => Key::PageUp,
        b"[6~" => Key::PageDown,
        b"OP" => Key::F(1),
        b"OQ" => Key::F(2),
        b"OR" => Key::F(3),
        b"OS" => Key::F(4),
        b"[15~" => Key::F(5),
        b"[17~" => Key::F(6),
        b"[18~" => Key::F(7),
        b"[19~" => Key::F(8),
        _ => Key::Esc,
    };
    Ok(Some(key))
}

fn terminal_size() -> (usize, usize) {
    let Ok(output) = Command::new("stty")
        .arg("size")
        .stdin(Stdio::inherit())
        .output()
    else {
        return (24, 80);
    };
    if !output.status.success() {
        return (24, 80);
    }
    let text = String::from_utf8_lossy(&output.stdout);
    let mut parts = text.split_whitespace();
    let rows = parts
        .next()
        .and_then(|part| part.parse::<usize>().ok())
        .unwrap_or(24);
    let cols = parts
        .next()
        .and_then(|part| part.parse::<usize>().ok())
        .unwrap_or(80);
    (rows.max(10), cols.max(40))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TuiFocus {
    Editor,
    Panel,
    Menu,
    Search,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TuiPanel {
    Goals,
    Theorems,
    Search,
    Explain,
    Diagnostics,
    Help,
}

impl TuiPanel {
    fn title(self) -> &'static str {
        match self {
            TuiPanel::Goals => "Goals",
            TuiPanel::Theorems => "Theorems",
            TuiPanel::Search => "Search",
            TuiPanel::Explain => "Explain",
            TuiPanel::Diagnostics => "Diagnostics",
            TuiPanel::Help => "Help",
        }
    }
}

struct TextBuffer {
    lines: Vec<String>,
    dirty: bool,
}

impl TextBuffer {
    fn from_source(source: String) -> Self {
        let mut lines = source.lines().map(str::to_string).collect::<Vec<String>>();
        if lines.is_empty() {
            lines.push(String::new());
        }
        Self {
            lines,
            dirty: false,
        }
    }

    fn to_source(&self) -> String {
        let mut source = self.lines.join("\n");
        source.push('\n');
        source
    }

    fn line_count(&self) -> usize {
        self.lines.len()
    }

    fn line_len(&self, line: usize) -> usize {
        self.lines
            .get(line)
            .map(|line| line.chars().count())
            .unwrap_or_default()
    }

    fn clamp_cursor(&self, cursor_line: &mut usize, cursor_col: &mut usize) {
        *cursor_line = (*cursor_line).min(self.lines.len().saturating_sub(1));
        *cursor_col = (*cursor_col).min(self.line_len(*cursor_line));
    }

    fn insert_char(&mut self, line: usize, col: usize, ch: char) -> (usize, usize) {
        let byte_idx = char_to_byte_index(&self.lines[line], col);
        self.lines[line].insert(byte_idx, ch);
        self.dirty = true;
        (line, col + 1)
    }

    fn insert_newline(&mut self, line: usize, col: usize) -> (usize, usize) {
        let byte_idx = char_to_byte_index(&self.lines[line], col);
        let tail = self.lines[line].split_off(byte_idx);
        self.lines.insert(line + 1, tail);
        self.dirty = true;
        (line + 1, 0)
    }

    fn backspace(&mut self, line: usize, col: usize) -> (usize, usize) {
        if col > 0 {
            let prev = col - 1;
            let start = char_to_byte_index(&self.lines[line], prev);
            let end = char_to_byte_index(&self.lines[line], col);
            self.lines[line].replace_range(start..end, "");
            self.dirty = true;
            (line, prev)
        } else if line > 0 {
            let prev_len = self.line_len(line - 1);
            let current = self.lines.remove(line);
            self.lines[line - 1].push_str(&current);
            self.dirty = true;
            (line - 1, prev_len)
        } else {
            (line, col)
        }
    }

    fn delete(&mut self, line: usize, col: usize) -> (usize, usize) {
        let len = self.line_len(line);
        if col < len {
            let start = char_to_byte_index(&self.lines[line], col);
            let end = char_to_byte_index(&self.lines[line], col + 1);
            self.lines[line].replace_range(start..end, "");
            self.dirty = true;
        } else if line + 1 < self.lines.len() {
            let next = self.lines.remove(line + 1);
            self.lines[line].push_str(&next);
            self.dirty = true;
        }
        (line, col)
    }
}

const UNDO_LIMIT: usize = 200;

#[derive(Clone)]
struct EditSnapshot {
    lines: Vec<String>,
    cursor_line: usize,
    cursor_col: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EditKind {
    InsertChar,
    Backspace,
    Delete,
    Newline,
    Replace,
}

fn char_to_byte_index(text: &str, char_idx: usize) -> usize {
    text.char_indices()
        .nth(char_idx)
        .map(|(idx, _)| idx)
        .unwrap_or(text.len())
}

struct TuiApp {
    path: PathBuf,
    hol_shadow_forced: bool,
    hol_shadow: bool,
    buffer: TextBuffer,
    cursor_line: usize,
    cursor_col: usize,
    row_scroll: usize,
    col_scroll: usize,
    focus: TuiFocus,
    panel: TuiPanel,
    menu_index: usize,
    theorem_index: usize,
    search_index: usize,
    search_query: String,
    selected_theorem: Option<String>,
    quit_confirm: bool,
    undo_stack: Vec<EditSnapshot>,
    redo_stack: Vec<EditSnapshot>,
    last_edit: Option<(EditKind, usize, usize)>,
    saved_lines: Option<Vec<String>>,
    outline: SourceOutline,
    check_result: CheckResult,
    goals: GoalStepResult,
    explanation: ExplanationResult,
    status: String,
    should_quit: bool,
}

impl TuiApp {
    fn open(path: PathBuf, force_hol_shadow: bool) -> io::Result<Self> {
        let source = fs::read_to_string(&path)?;
        let initial_outline = outline(&source);
        let cursor_line = initial_outline
            .theorems
            .first()
            .map(|theorem| theorem.line.saturating_sub(1))
            .unwrap_or(0);
        let buffer = TextBuffer::from_source(source);
        let saved_lines = Some(buffer.lines.clone());
        Ok(Self {
            path,
            hol_shadow_forced: force_hol_shadow,
            hol_shadow: force_hol_shadow,
            buffer,
            cursor_line,
            cursor_col: 0,
            row_scroll: 0,
            col_scroll: 0,
            focus: TuiFocus::Editor,
            panel: TuiPanel::Goals,
            menu_index: 0,
            theorem_index: 0,
            search_index: 0,
            search_query: String::new(),
            selected_theorem: None,
            quit_confirm: false,
            undo_stack: Vec::new(),
            redo_stack: Vec::new(),
            last_edit: None,
            saved_lines,
            outline: initial_outline,
            check_result: CheckResult::default(),
            goals: GoalStepResult::default(),
            explanation: ExplanationResult::default(),
            status: if force_hol_shadow {
                "Loaded with HOL-certified goal hints. Ctrl-S saves, Ctrl-Q quits.".to_string()
            } else {
                "Loaded file. Ctrl-S saves, Ctrl-Q quits, m opens menu.".to_string()
            },
            should_quit: false,
        })
    }

    fn source(&self) -> String {
        self.buffer.to_source()
    }

    fn explain_in_source(&self, source: &str, theorem: &str) -> ExplanationResult {
        if self.hol_shadow {
            explain_theorem_in_source_at_path_with_hol_shadow(source, &self.path, theorem)
        } else {
            explain_theorem_in_source_at_path(source, &self.path, theorem)
        }
    }

    fn refresh_analysis(&mut self) {
        let source = self.source();
        self.outline = outline(&source);
        let (check_result, hol_shadow) =
            check_editor_source(&source, &self.path, self.hol_shadow_forced);
        if hol_shadow != self.hol_shadow {
            self.status = if hol_shadow {
                "Logical package import enabled HOL-certified analysis.".to_string()
            } else {
                "No logical package import; using ordinary analysis.".to_string()
            };
        }
        self.hol_shadow = hol_shadow;
        self.check_result = check_result;
        let position = Position {
            line: self.cursor_line + 1,
            column: self.cursor_col + 1,
        };
        self.goals = if self.hol_shadow {
            goals_at_source_path_with_hol_shadow(&source, &self.path, position)
        } else {
            goals_at_source_path(&source, &self.path, position)
        };
        if let Some(theorem) = &self.goals.theorem {
            self.selected_theorem = Some(theorem.clone());
            if let Some(index) = self
                .outline
                .theorems
                .iter()
                .position(|item| &item.name == theorem)
            {
                self.theorem_index = index;
            }
        } else if self.selected_theorem.is_none() {
            self.selected_theorem = self.outline.theorems.first().map(|item| item.name.clone());
        }
        if let Some(theorem) = &self.selected_theorem {
            self.explanation = self.explain_in_source(&source, theorem);
        } else {
            self.explanation = ExplanationResult::default();
        }
        self.search_index = self
            .search_index
            .min(self.search_results().len().saturating_sub(1));
    }

    fn snapshot(&self) -> EditSnapshot {
        EditSnapshot {
            lines: self.buffer.lines.clone(),
            cursor_line: self.cursor_line,
            cursor_col: self.cursor_col,
        }
    }

    fn push_undo_snapshot(&mut self) {
        if self.undo_stack.len() >= UNDO_LIMIT {
            self.undo_stack.remove(0);
        }
        self.undo_stack.push(self.snapshot());
    }

    /// Called before a mutating edit is applied. Pushes an undo snapshot of
    /// the pre-edit state unless this edit continues a run of consecutive
    /// single-character insertions at the position where the previous
    /// insertion left the cursor.
    fn record_edit(&mut self, kind: EditKind) {
        let coalesce = kind == EditKind::InsertChar
            && self.last_edit == Some((EditKind::InsertChar, self.cursor_line, self.cursor_col));
        if !coalesce {
            self.push_undo_snapshot();
        }
        self.redo_stack.clear();
    }

    fn undo(&mut self) {
        let Some(snapshot) = self.undo_stack.pop() else {
            self.status = "Nothing to undo.".to_string();
            return;
        };
        let current = self.snapshot();
        self.redo_stack.push(current);
        self.restore_snapshot(snapshot);
        self.status = "Undid last edit.".to_string();
    }

    fn redo(&mut self) {
        let Some(snapshot) = self.redo_stack.pop() else {
            self.status = "Nothing to redo.".to_string();
            return;
        };
        self.push_undo_snapshot();
        self.restore_snapshot(snapshot);
        self.status = "Redid last edit.".to_string();
    }

    fn restore_snapshot(&mut self, snapshot: EditSnapshot) {
        self.buffer.lines = snapshot.lines;
        self.cursor_line = snapshot.cursor_line;
        self.cursor_col = snapshot.cursor_col;
        self.buffer
            .clamp_cursor(&mut self.cursor_line, &mut self.cursor_col);
        self.buffer.dirty = match &self.saved_lines {
            Some(saved) => &self.buffer.lines != saved,
            None => true,
        };
        self.last_edit = None;
        self.quit_confirm = false;
        self.refresh_analysis();
    }

    fn handle_key(&mut self, key: Key) {
        match self.focus {
            TuiFocus::Menu => self.handle_menu_key(key),
            TuiFocus::Search => self.handle_search_key(key),
            TuiFocus::Panel => self.handle_panel_key(key),
            TuiFocus::Editor => self.handle_editor_key(key),
        }
    }

    fn handle_editor_key(&mut self, key: Key) {
        match key {
            Key::Ctrl('q') => self.request_quit(),
            Key::Ctrl('s') | Key::F(6) => self.save(),
            Key::Ctrl('r') | Key::F(7) => self.reload(),
            Key::Ctrl('z') => self.undo(),
            Key::Ctrl('y') => self.redo(),
            Key::F(8) => {
                self.refresh_analysis();
                self.status = "Checked current buffer.".to_string();
            }
            Key::F(1) => self.panel = TuiPanel::Help,
            Key::F(2) => {
                self.panel = TuiPanel::Theorems;
                self.focus = TuiFocus::Panel;
            }
            Key::F(3) | Key::Char('/') => {
                self.panel = TuiPanel::Search;
                self.focus = TuiFocus::Search;
            }
            Key::F(4) | Key::Char('e') => {
                self.panel = TuiPanel::Explain;
                self.refresh_analysis();
            }
            Key::F(5) => self.panel = TuiPanel::Diagnostics,
            Key::Char('m') => self.focus = TuiFocus::Menu,
            Key::Tab => self.focus = TuiFocus::Panel,
            Key::Up => self.move_cursor_up(1),
            Key::Down => self.move_cursor_down(1),
            Key::Left => self.move_cursor_left(),
            Key::Right => self.move_cursor_right(),
            Key::PageUp => self.move_cursor_up(10),
            Key::PageDown => self.move_cursor_down(10),
            Key::Home => self.cursor_col = 0,
            Key::End => self.cursor_col = self.buffer.line_len(self.cursor_line),
            Key::Enter => {
                self.record_edit(EditKind::Newline);
                let (line, col) = self
                    .buffer
                    .insert_newline(self.cursor_line, self.cursor_col);
                self.cursor_line = line;
                self.cursor_col = col;
                self.last_edit = Some((EditKind::Newline, line, col));
                self.quit_confirm = false;
                self.refresh_analysis();
            }
            Key::Backspace => {
                let is_noop = self.cursor_line == 0 && self.cursor_col == 0;
                if !is_noop {
                    self.record_edit(EditKind::Backspace);
                }
                let (line, col) = self.buffer.backspace(self.cursor_line, self.cursor_col);
                self.cursor_line = line;
                self.cursor_col = col;
                if !is_noop {
                    self.last_edit = Some((EditKind::Backspace, line, col));
                }
                self.quit_confirm = false;
                self.refresh_analysis();
            }
            Key::Delete => {
                let is_noop = self.cursor_col >= self.buffer.line_len(self.cursor_line)
                    && self.cursor_line + 1 >= self.buffer.line_count();
                if !is_noop {
                    self.record_edit(EditKind::Delete);
                }
                let (line, col) = self.buffer.delete(self.cursor_line, self.cursor_col);
                self.cursor_line = line;
                self.cursor_col = col;
                if !is_noop {
                    self.last_edit = Some((EditKind::Delete, line, col));
                }
                self.quit_confirm = false;
                self.refresh_analysis();
            }
            Key::Char(ch) => {
                self.record_edit(EditKind::InsertChar);
                let (line, col) = self
                    .buffer
                    .insert_char(self.cursor_line, self.cursor_col, ch);
                self.cursor_line = line;
                self.cursor_col = col;
                self.last_edit = Some((EditKind::InsertChar, line, col));
                self.quit_confirm = false;
                self.refresh_analysis();
            }
            _ => {}
        }
    }

    fn handle_panel_key(&mut self, key: Key) {
        match key {
            Key::Ctrl('q') => self.request_quit(),
            Key::Esc | Key::Tab => self.focus = TuiFocus::Editor,
            Key::Char('m') => self.focus = TuiFocus::Menu,
            Key::F(1) => self.panel = TuiPanel::Help,
            Key::F(2) => self.panel = TuiPanel::Theorems,
            Key::F(3) | Key::Char('/') => {
                self.panel = TuiPanel::Search;
                self.focus = TuiFocus::Search;
            }
            Key::F(4) | Key::Char('e') => self.panel = TuiPanel::Explain,
            Key::F(5) => self.panel = TuiPanel::Diagnostics,
            Key::Up => self.move_panel_selection(-1),
            Key::Down => self.move_panel_selection(1),
            Key::PageUp => self.move_panel_selection(-10),
            Key::PageDown => self.move_panel_selection(10),
            Key::Enter => self.activate_panel_selection(),
            Key::Ctrl('s') | Key::F(6) => self.save(),
            Key::Ctrl('r') | Key::F(7) => self.reload(),
            Key::F(8) => {
                self.refresh_analysis();
                self.status = "Checked current buffer.".to_string();
            }
            _ => {}
        }
    }

    fn handle_search_key(&mut self, key: Key) {
        match key {
            Key::Ctrl('q') => self.request_quit(),
            Key::Esc | Key::Tab => self.focus = TuiFocus::Editor,
            Key::Enter => {
                if let Some(name) = self
                    .search_results()
                    .get(self.search_index)
                    .map(|theorem| theorem.name.clone())
                {
                    self.selected_theorem = Some(name.clone());
                    self.explanation = self.explain_in_source(&self.source(), &name);
                    self.panel = TuiPanel::Explain;
                    self.focus = TuiFocus::Panel;
                }
            }
            Key::Up => self.move_search_selection(-1),
            Key::Down => self.move_search_selection(1),
            Key::Backspace => {
                self.search_query.pop();
                self.search_index = 0;
            }
            Key::Char(ch) => {
                self.search_query.push(ch);
                self.search_index = 0;
            }
            _ => {}
        }
    }

    fn handle_menu_key(&mut self, key: Key) {
        match key {
            Key::Ctrl('q') => self.request_quit(),
            Key::Esc | Key::Tab => self.focus = TuiFocus::Editor,
            Key::Up => {
                if self.menu_index > 0 {
                    self.menu_index -= 1;
                }
            }
            Key::Down => {
                self.menu_index = (self.menu_index + 1).min(MENU_ITEMS.len().saturating_sub(1));
            }
            Key::Enter => self.activate_menu_item(),
            _ => {}
        }
    }

    fn request_quit(&mut self) {
        if self.buffer.dirty && !self.quit_confirm {
            self.status =
                "Unsaved changes. Press Ctrl-Q again to quit without saving, or Ctrl-S to save."
                    .to_string();
            self.quit_confirm = true;
        } else {
            self.should_quit = true;
        }
    }

    fn save(&mut self) {
        match fs::write(&self.path, self.source()) {
            Ok(()) => {
                self.buffer.dirty = false;
                self.quit_confirm = false;
                self.saved_lines = Some(self.buffer.lines.clone());
                self.status = format!("Saved {}.", self.path.display());
                self.refresh_analysis();
            }
            Err(err) => self.status = format!("Could not save {}: {err}", self.path.display()),
        }
    }

    fn reload(&mut self) {
        match fs::read_to_string(&self.path) {
            Ok(source) => {
                self.record_edit(EditKind::Replace);
                self.last_edit = None;
                self.buffer = TextBuffer::from_source(source);
                self.saved_lines = Some(self.buffer.lines.clone());
                self.quit_confirm = false;
                self.cursor_line = self
                    .cursor_line
                    .min(self.buffer.line_count().saturating_sub(1));
                self.cursor_col = self.cursor_col.min(self.buffer.line_len(self.cursor_line));
                self.status = format!("Reloaded {}.", self.path.display());
                self.refresh_analysis();
            }
            Err(err) => self.status = format!("Could not reload {}: {err}", self.path.display()),
        }
    }

    fn move_cursor_up(&mut self, count: usize) {
        self.cursor_line = self.cursor_line.saturating_sub(count);
        self.buffer
            .clamp_cursor(&mut self.cursor_line, &mut self.cursor_col);
        self.refresh_analysis();
    }

    fn move_cursor_down(&mut self, count: usize) {
        self.cursor_line =
            (self.cursor_line + count).min(self.buffer.line_count().saturating_sub(1));
        self.buffer
            .clamp_cursor(&mut self.cursor_line, &mut self.cursor_col);
        self.refresh_analysis();
    }

    fn move_cursor_left(&mut self) {
        if self.cursor_col > 0 {
            self.cursor_col -= 1;
        } else if self.cursor_line > 0 {
            self.cursor_line -= 1;
            self.cursor_col = self.buffer.line_len(self.cursor_line);
        }
        self.refresh_analysis();
    }

    fn move_cursor_right(&mut self) {
        if self.cursor_col < self.buffer.line_len(self.cursor_line) {
            self.cursor_col += 1;
        } else if self.cursor_line + 1 < self.buffer.line_count() {
            self.cursor_line += 1;
            self.cursor_col = 0;
        }
        self.refresh_analysis();
    }

    fn move_panel_selection(&mut self, delta: isize) {
        match self.panel {
            TuiPanel::Theorems => {
                self.theorem_index = add_clamped(
                    self.theorem_index,
                    delta,
                    self.outline.theorems.len().saturating_sub(1),
                );
            }
            TuiPanel::Search => self.move_search_selection(delta),
            _ => {}
        }
    }

    fn move_search_selection(&mut self, delta: isize) {
        self.search_index = add_clamped(
            self.search_index,
            delta,
            self.search_results().len().saturating_sub(1),
        );
    }

    fn activate_panel_selection(&mut self) {
        match self.panel {
            TuiPanel::Theorems => {
                if let Some(theorem) = self.outline.theorems.get(self.theorem_index) {
                    self.cursor_line = theorem.line.saturating_sub(1);
                    self.cursor_col = 0;
                    self.selected_theorem = Some(theorem.name.clone());
                    self.panel = TuiPanel::Goals;
                    self.focus = TuiFocus::Editor;
                    self.refresh_analysis();
                }
            }
            TuiPanel::Search => {
                if let Some(name) = self
                    .search_results()
                    .get(self.search_index)
                    .map(|theorem| theorem.name.clone())
                {
                    self.selected_theorem = Some(name.clone());
                    self.explanation = self.explain_in_source(&self.source(), &name);
                    self.panel = TuiPanel::Explain;
                }
            }
            _ => {}
        }
    }

    fn activate_menu_item(&mut self) {
        match MENU_ITEMS[self.menu_index].action {
            MenuAction::Goals => self.panel = TuiPanel::Goals,
            MenuAction::Theorems => {
                self.panel = TuiPanel::Theorems;
                self.focus = TuiFocus::Panel;
                return;
            }
            MenuAction::Search => {
                self.panel = TuiPanel::Search;
                self.focus = TuiFocus::Search;
                return;
            }
            MenuAction::Explain => {
                self.panel = TuiPanel::Explain;
                self.refresh_analysis();
            }
            MenuAction::Diagnostics => self.panel = TuiPanel::Diagnostics,
            MenuAction::Help => self.panel = TuiPanel::Help,
            MenuAction::Save => self.save(),
            MenuAction::Reload => self.reload(),
            MenuAction::Check => {
                self.refresh_analysis();
                self.status = "Checked current buffer.".to_string();
            }
            MenuAction::Quit => self.request_quit(),
        }
        self.focus = TuiFocus::Editor;
    }

    fn search_results(&self) -> Vec<&cetacea_core::CheckedTheorem> {
        let query = self.search_query.to_lowercase();
        let mut matches = self
            .check_result
            .theorems
            .iter()
            .filter(|theorem| {
                query.is_empty()
                    || theorem.name.to_lowercase().contains(&query)
                    || theorem.statement.to_lowercase().contains(&query)
            })
            .collect::<Vec<_>>();
        matches.sort_by_key(|theorem| (theorem.is_imported, theorem.name.clone()));
        matches
    }

    fn draw(&mut self, stdout: &mut io::Stdout, rows: usize, cols: usize) -> io::Result<()> {
        let panel_min = 24.min(cols.saturating_sub(20)).max(12);
        let editor_max = cols.saturating_sub(panel_min + 1).max(1);
        let editor_target = if cols < 70 {
            (cols * 2) / 3
        } else {
            (cols * 62) / 100
        };
        let editor_width = editor_target.clamp(1, editor_max).max(1);
        let panel_width = cols.saturating_sub(editor_width + 1);
        let body_rows = rows.saturating_sub(3);
        self.keep_cursor_visible(body_rows, editor_width);

        write!(stdout, "\x1b[?25l\x1b[H")?;
        self.draw_top_bar(stdout, cols)?;
        for row in 0..body_rows {
            write!(stdout, "\x1b[{};1H", row + 2)?;
            self.draw_editor_row(stdout, row, editor_width)?;
            write!(stdout, "|")?;
            self.draw_panel_row(stdout, row, panel_width)?;
        }
        self.draw_status_bar(stdout, rows, cols)?;
        if self.focus == TuiFocus::Menu {
            self.draw_menu(stdout, rows, cols)?;
        }
        self.place_cursor(stdout, editor_width)?;
        stdout.flush()
    }

    fn keep_cursor_visible(&mut self, body_rows: usize, editor_width: usize) {
        if self.cursor_line < self.row_scroll {
            self.row_scroll = self.cursor_line;
        } else if self.cursor_line >= self.row_scroll + body_rows {
            self.row_scroll = self.cursor_line.saturating_sub(body_rows.saturating_sub(1));
        }

        let gutter = self.gutter_width();
        let text_width = editor_width.saturating_sub(gutter + 1).max(1);
        if self.cursor_col < self.col_scroll {
            self.col_scroll = self.cursor_col;
        } else if self.cursor_col >= self.col_scroll + text_width {
            self.col_scroll = self.cursor_col.saturating_sub(text_width.saturating_sub(1));
        }
    }

    fn gutter_width(&self) -> usize {
        self.buffer.line_count().to_string().len() + 3
    }

    fn draw_top_bar(&self, stdout: &mut io::Stdout, cols: usize) -> io::Result<()> {
        let dirty = if self.buffer.dirty { "*" } else { "" };
        let focus = match self.focus {
            TuiFocus::Editor => "editor",
            TuiFocus::Panel => "panel",
            TuiFocus::Menu => "menu",
            TuiFocus::Search => "search",
        };
        let title = format!(
            " Cetacea TUI{dirty}{}  {}  [{}]  F1 Help F2 Theorems F3 Search F4 Explain F5 Diagnostics ",
            if self.hol_shadow { " [HOL]" } else { "" },
            self.path.display(),
            focus
        );
        write!(stdout, "\x1b[7m{}\x1b[0m", fit_line(&title, cols))
    }

    fn draw_editor_row(&self, stdout: &mut io::Stdout, row: usize, width: usize) -> io::Result<()> {
        let line_idx = self.row_scroll + row;
        let gutter = self.gutter_width();
        if line_idx >= self.buffer.line_count() {
            write!(stdout, "{}", " ".repeat(width))?;
            return Ok(());
        }
        let marker = if line_idx == self.cursor_line {
            ">"
        } else {
            " "
        };
        let line_no = format!("{marker}{:>width$} ", line_idx + 1, width = gutter - 2);
        let text_width = width.saturating_sub(gutter);
        let text = visible_chars(&self.buffer.lines[line_idx], self.col_scroll, text_width);
        if line_idx == self.cursor_line {
            write!(
                stdout,
                "\x1b[48;5;236m{}{}\x1b[0m",
                line_no,
                fit_line(&text, text_width)
            )
        } else {
            write!(stdout, "{}{}", line_no, fit_line(&text, text_width))
        }
    }

    fn panel_lines(&self, width: usize) -> Vec<String> {
        let mut lines = Vec::new();
        lines.push(format!(" {} ", self.panel.title()));
        lines.push("".to_string());
        match self.panel {
            TuiPanel::Goals => self.goal_panel_lines(&mut lines, width),
            TuiPanel::Theorems => self.theorem_panel_lines(&mut lines),
            TuiPanel::Search => self.search_panel_lines(&mut lines),
            TuiPanel::Explain => self.explain_panel_lines(&mut lines, width),
            TuiPanel::Diagnostics => self.diagnostic_panel_lines(&mut lines, width),
            TuiPanel::Help => self.help_panel_lines(&mut lines),
        }
        lines
    }

    fn goal_panel_lines(&self, lines: &mut Vec<String>, width: usize) {
        if !self.goals.diagnostics.is_empty() {
            lines.push("Current proof state diagnostics:".to_string());
            for diagnostic in &self.goals.diagnostics {
                push_wrapped(
                    lines,
                    &format!("{}: {}", diagnostic_label(diagnostic), diagnostic.message),
                    width,
                );
            }
            return;
        }
        match &self.goals.theorem {
            Some(theorem) => lines.push(format!(
                "{theorem}: tactic {}/{}{}",
                self.goals.next_tactic_index,
                self.goals.tactic_count,
                if self.goals.completed {
                    " complete"
                } else {
                    ""
                }
            )),
            None => lines.push("No theorem at cursor.".to_string()),
        }
        if let Some(fragment) = self.goals.statement_fragment {
            lines.push(format!("Certified fragment: {fragment}"));
        }
        if self.goals.goals.is_empty() {
            lines.push(if self.goals.completed {
                "Complete.".to_string()
            } else {
                "No goals.".to_string()
            });
            return;
        }
        for (idx, goal) in self.goals.goals.iter().enumerate() {
            lines.push("".to_string());
            lines.push(format!("Goal {}", idx + 1));
            if goal.context.is_empty() {
                lines.push("  Context: empty".to_string());
            } else {
                lines.push("  Context:".to_string());
                for entry in &goal.context {
                    push_wrapped(lines, &format!("    {entry}"), width);
                }
            }
            push_wrapped(lines, &format!("  |- {}", goal.target), width);
            if !goal.hints.is_empty() {
                lines.push("  Hints:".to_string());
                for hint in goal.hints.iter().take(4) {
                    push_wrapped(
                        lines,
                        &format!("    {}: {}", hint.title, hint.tactic),
                        width,
                    );
                }
            }
        }
    }

    fn theorem_panel_lines(&self, lines: &mut Vec<String>) {
        if !self.outline.diagnostics.is_empty() {
            lines.push("Outline diagnostics:".to_string());
            for diagnostic in &self.outline.diagnostics {
                lines.push(format!(
                    "{}: {}",
                    diagnostic_label(diagnostic),
                    diagnostic.message
                ));
            }
            return;
        }
        if self.outline.theorems.is_empty() {
            lines.push("No source theorems.".to_string());
            return;
        }
        lines.push("Enter jumps to theorem. Tab returns.".to_string());
        for (idx, theorem) in self.outline.theorems.iter().enumerate() {
            let marker = if idx == self.theorem_index { ">" } else { " " };
            lines.push(format!(
                "{marker} {:>2}. {} line {} ({} tactics)",
                idx + 1,
                theorem.name,
                theorem.line,
                theorem.tactic_count
            ));
        }
    }

    fn search_panel_lines(&self, lines: &mut Vec<String>) {
        lines.push(format!("Query: {}", self.search_query));
        lines.push("Type to search. Enter explains result.".to_string());
        for (idx, theorem) in self.search_results().iter().take(40).enumerate() {
            let marker = if idx == self.search_index { ">" } else { " " };
            let origin = if theorem.is_imported {
                "import"
            } else {
                "local"
            };
            lines.push(format!(
                "{marker} {} [{}] {} : {}",
                idx + 1,
                origin,
                theorem.name,
                theorem.statement
            ));
        }
    }

    fn explain_panel_lines(&self, lines: &mut Vec<String>, width: usize) {
        if !self.explanation.diagnostics.is_empty() && self.explanation.steps.is_empty() {
            for diagnostic in &self.explanation.diagnostics {
                push_wrapped(
                    lines,
                    &format!("{}: {}", diagnostic_label(diagnostic), diagnostic.message),
                    width,
                );
            }
            return;
        }
        if let Some(theorem) = &self.explanation.theorem {
            lines.push(format!(
                "{}{}",
                theorem,
                if self.explanation.completed {
                    ""
                } else {
                    " (incomplete)"
                }
            ));
        } else {
            lines.push("No theorem selected.".to_string());
        }
        if let Some(statement) = &self.explanation.statement {
            push_wrapped(lines, &format!("Statement: {statement}"), width);
        }
        if let Some(fragment) = self.explanation.statement_fragment {
            lines.push(format!("Certified fragment: {fragment}"));
        }
        for step in self.explanation.steps.iter().take(30) {
            lines.push("".to_string());
            lines.push(format!("Line {}: {}", step.line, step.tactic));
            push_wrapped(lines, &format!("Before: |- {}", step.before.target), width);
            for sentence in &step.explanation {
                push_wrapped(lines, &format!("- {sentence}"), width);
            }
            if step.after.is_empty() {
                lines.push("After: current goal closed".to_string());
            } else {
                for (idx, goal) in step.after.iter().enumerate() {
                    push_wrapped(
                        lines,
                        &format!("After {}: |- {}", idx + 1, goal.target),
                        width,
                    );
                }
            }
        }
    }

    fn diagnostic_panel_lines(&self, lines: &mut Vec<String>, width: usize) {
        if self.check_result.diagnostics.is_empty() {
            lines.push("No diagnostics in current buffer.".to_string());
            return;
        }
        for diagnostic in &self.check_result.diagnostics {
            let location = diagnostic
                .location
                .as_ref()
                .map(|loc| format!("line {}: ", loc.line))
                .unwrap_or_default();
            push_wrapped(
                lines,
                &format!(
                    "{}: {location}{}",
                    diagnostic_label(diagnostic),
                    diagnostic.message
                ),
                width,
            );
            for note in &diagnostic.notes {
                push_wrapped(lines, &format!("  note: {note}"), width);
            }
            for suggestion in &diagnostic.suggestions {
                push_wrapped(lines, &format!("  help: {}", suggestion.title), width);
                push_wrapped(lines, &format!("    {}", suggestion.detail), width);
            }
            lines.push("".to_string());
        }
    }

    fn help_panel_lines(&self, lines: &mut Vec<String>) {
        lines.extend([
            "Editor keys".to_string(),
            "  arrows/PageUp/PageDown move cursor".to_string(),
            "  typing edits the proof buffer".to_string(),
            "  Ctrl-S saves".to_string(),
            "  Ctrl-Z undoes, Ctrl-Y redoes".to_string(),
            "  Ctrl-R reloads from disk".to_string(),
            "  Ctrl-Q quits".to_string(),
            "".to_string(),
            "Menus and panels".to_string(),
            "  m opens the command menu".to_string(),
            "  Tab switches between editor and panel".to_string(),
            "  F2 theorem outline".to_string(),
            "  F3 theorem search".to_string(),
            "  F4 proof explainer".to_string(),
            "  F5 diagnostics".to_string(),
            "  F8 re-checks current buffer".to_string(),
        ]);
    }

    fn draw_panel_row(&self, stdout: &mut io::Stdout, row: usize, width: usize) -> io::Result<()> {
        let lines = self.panel_lines(width);
        let line = lines.get(row).map(String::as_str).unwrap_or("");
        if row == 0 {
            write!(stdout, "\x1b[1m{}\x1b[0m", fit_line(line, width))
        } else {
            write!(stdout, "{}", fit_line(line, width))
        }
    }

    fn draw_status_bar(&self, stdout: &mut io::Stdout, rows: usize, cols: usize) -> io::Result<()> {
        let diag_count = self.check_result.diagnostics.len();
        let dirty = if self.buffer.dirty {
            "modified"
        } else {
            "saved"
        };
        let status = format!(
            " {} | {} | line {}, col {} | {} diagnostic(s) | {} ",
            dirty,
            self.selected_theorem.as_deref().unwrap_or("no theorem"),
            self.cursor_line + 1,
            self.cursor_col + 1,
            diag_count,
            self.status
        );
        write!(
            stdout,
            "\x1b[{};1H\x1b[7m{}\x1b[0m",
            rows.saturating_sub(1),
            fit_line(&status, cols)
        )?;
        write!(
            stdout,
            "\x1b[{};1H{}",
            rows,
            fit_line(
                " Ctrl-S save  Ctrl-Z undo  Ctrl-Y redo  Ctrl-R reload  Ctrl-Q quit  m menu  Tab panel  / search ",
                cols
            )
        )
    }

    fn draw_menu(&self, stdout: &mut io::Stdout, rows: usize, cols: usize) -> io::Result<()> {
        let width = 32.min(cols.saturating_sub(4)).max(20);
        let height = MENU_ITEMS.len() + 2;
        let top = rows.saturating_sub(height) / 2;
        let left = cols.saturating_sub(width) / 2;
        write!(stdout, "\x1b[{};{}H+{}+", top, left, "-".repeat(width - 2))?;
        for (idx, item) in MENU_ITEMS.iter().enumerate() {
            write!(stdout, "\x1b[{};{}H|", top + idx + 1, left)?;
            let label = format!(
                " {} {}",
                if idx == self.menu_index { ">" } else { " " },
                item.label
            );
            if idx == self.menu_index {
                write!(stdout, "\x1b[7m{}\x1b[0m", fit_line(&label, width - 2))?;
            } else {
                write!(stdout, "{}", fit_line(&label, width - 2))?;
            }
            write!(stdout, "|")?;
        }
        write!(
            stdout,
            "\x1b[{};{}H+{}+",
            top + height - 1,
            left,
            "-".repeat(width - 2)
        )
    }

    fn place_cursor(&self, stdout: &mut io::Stdout, editor_width: usize) -> io::Result<()> {
        if self.focus != TuiFocus::Editor {
            return write!(stdout, "\x1b[?25l");
        }
        let gutter = self.gutter_width();
        let row = self.cursor_line.saturating_sub(self.row_scroll) + 2;
        let col = gutter + self.cursor_col.saturating_sub(self.col_scroll) + 1;
        if col <= editor_width {
            write!(stdout, "\x1b[?25h\x1b[{row};{col}H")
        } else {
            write!(stdout, "\x1b[?25l")
        }
    }
}

#[derive(Clone, Copy)]
enum MenuAction {
    Goals,
    Theorems,
    Search,
    Explain,
    Diagnostics,
    Help,
    Save,
    Reload,
    Check,
    Quit,
}

struct MenuItem {
    label: &'static str,
    action: MenuAction,
}

const MENU_ITEMS: &[MenuItem] = &[
    MenuItem {
        label: "Goals",
        action: MenuAction::Goals,
    },
    MenuItem {
        label: "Theorems",
        action: MenuAction::Theorems,
    },
    MenuItem {
        label: "Search",
        action: MenuAction::Search,
    },
    MenuItem {
        label: "Explain",
        action: MenuAction::Explain,
    },
    MenuItem {
        label: "Diagnostics",
        action: MenuAction::Diagnostics,
    },
    MenuItem {
        label: "Help",
        action: MenuAction::Help,
    },
    MenuItem {
        label: "Save",
        action: MenuAction::Save,
    },
    MenuItem {
        label: "Reload",
        action: MenuAction::Reload,
    },
    MenuItem {
        label: "Check",
        action: MenuAction::Check,
    },
    MenuItem {
        label: "Quit",
        action: MenuAction::Quit,
    },
];

fn add_clamped(current: usize, delta: isize, max: usize) -> usize {
    if delta.is_negative() {
        current.saturating_sub(delta.unsigned_abs()).min(max)
    } else {
        current.saturating_add(delta as usize).min(max)
    }
}

fn visible_chars(text: &str, start: usize, width: usize) -> String {
    text.chars().skip(start).take(width).collect()
}

fn fit_line(text: &str, width: usize) -> String {
    let mut result = text.chars().take(width).collect::<String>();
    let len = result.chars().count();
    if len < width {
        result.push_str(&" ".repeat(width - len));
    }
    result
}

fn push_wrapped(lines: &mut Vec<String>, text: &str, width: usize) {
    let wrap_width = width.max(8);
    let mut remaining = text.trim_end();
    while remaining.chars().count() > wrap_width {
        let mut split_at = 0;
        let mut count = 0;
        for (idx, ch) in remaining.char_indices() {
            if count >= wrap_width {
                break;
            }
            if ch.is_whitespace() {
                split_at = idx;
            }
            count += 1;
        }
        if split_at == 0 {
            split_at = char_to_byte_index(remaining, wrap_width);
        }
        lines.push(remaining[..split_at].trim_end().to_string());
        remaining = remaining[split_at..].trim_start();
    }
    lines.push(remaining.to_string());
}

struct InteractiveState {
    path: PathBuf,
    hol_shadow_forced: bool,
    hol_shadow: bool,
    outline: SourceOutline,
    last_check: CheckResult,
    selected_theorem: Option<String>,
    next_tactic_index: usize,
    current_goals: Option<GoalStepResult>,
}

impl InteractiveState {
    fn new(path: PathBuf, force_hol_shadow: bool) -> Self {
        Self {
            path,
            hol_shadow_forced: force_hol_shadow,
            hol_shadow: force_hol_shadow,
            outline: SourceOutline::default(),
            last_check: CheckResult::default(),
            selected_theorem: None,
            next_tactic_index: 0,
            current_goals: None,
        }
    }

    fn reload(&mut self) {
        self.outline = load_outline(&self.path);
        let (last_check, hol_shadow) = check_editor_path(&self.path, self.hol_shadow_forced);
        self.last_check = last_check;
        self.hol_shadow = hol_shadow;
        if self
            .selected_theorem
            .as_ref()
            .is_none_or(|name| !self.outline.theorems.iter().any(|item| &item.name == name))
        {
            self.selected_theorem = self
                .outline
                .theorems
                .first()
                .map(|theorem| theorem.name.clone());
        }
        self.next_tactic_index = 0;
        self.current_goals = None;
    }

    fn selected_outline_index(&self) -> Option<usize> {
        let selected = self.selected_theorem.as_ref()?;
        self.outline
            .theorems
            .iter()
            .position(|theorem| &theorem.name == selected)
    }
}

fn run_interactive(path: PathBuf, hol_shadow: bool) -> io::Result<()> {
    let mut state = InteractiveState::new(path, hol_shadow);
    state.reload();

    println!("Cetacea interactive mode");
    println!("File: {}", state.path.display());
    if state.hol_shadow {
        println!("HOL-certified goal hints: enabled");
    }
    println!("Type `help` for commands.");
    if !diagnostics_have_errors(&state.last_check.diagnostics) {
        print_accepted_summary(&state.last_check);
    }
    if !state.last_check.diagnostics.is_empty() {
        print_diagnostics(&state.last_check.diagnostics);
    }
    if let Some(name) = &state.selected_theorem {
        println!("Selected theorem: {name}");
    }

    let stdin = io::stdin();
    loop {
        print!("cetacea> ");
        io::stdout().flush()?;

        let mut line = String::new();
        if stdin.read_line(&mut line)? == 0 {
            println!();
            break;
        }
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if !handle_interactive_command(&mut state, line) {
            break;
        }
    }

    Ok(())
}

fn handle_interactive_command(state: &mut InteractiveState, line: &str) -> bool {
    let (command, rest) = split_command(line);
    match command {
        "q" | "quit" | "exit" => false,
        "h" | "help" | "menu" => {
            print_interactive_help();
            true
        }
        "r" | "reload" => {
            state.reload();
            println!("Reloaded {}", state.path.display());
            if !diagnostics_have_errors(&state.last_check.diagnostics) {
                print_accepted_summary(&state.last_check);
            }
            if !state.last_check.diagnostics.is_empty() {
                print_diagnostics(&state.last_check.diagnostics);
            }
            true
        }
        "c" | "check" => {
            let (last_check, hol_shadow) = check_editor_path(&state.path, state.hol_shadow_forced);
            state.last_check = last_check;
            state.hol_shadow = hol_shadow;
            if !diagnostics_have_errors(&state.last_check.diagnostics) {
                print_accepted(&state.last_check);
            }
            if !state.last_check.diagnostics.is_empty() {
                print_diagnostics(&state.last_check.diagnostics);
            }
            true
        }
        "t" | "theorems" | "outline" => {
            print_outline(state);
            true
        }
        "select" | "s" => {
            select_theorem(state, rest);
            true
        }
        "reset" => {
            reset_selected_theorem(state);
            true
        }
        "step" | "n" | "next" => {
            step_selected_theorem(state, rest);
            true
        }
        "goals" | "g" => {
            show_goals_at_position(state, rest);
            true
        }
        "hints" => {
            print_current_hints(state);
            true
        }
        "search" | "library" | "find" => {
            search_theorems(state, rest);
            true
        }
        "explain" | "interpret" | "why" => {
            explain_selected_or_named_theorem(state, rest);
            true
        }
        "accepted" => {
            print_accepted(&state.last_check);
            true
        }
        "diagnostics" | "errors" => {
            if state.last_check.diagnostics.is_empty() {
                println!("No diagnostics from the last check.");
            } else {
                print_diagnostics(&state.last_check.diagnostics);
            }
            true
        }
        "status" => {
            println!("File: {}", state.path.display());
            println!(
                "Selected theorem: {}",
                state.selected_theorem.as_deref().unwrap_or("(none)")
            );
            println!("Next tactic index: {}", state.next_tactic_index);
            true
        }
        other => {
            println!("Unknown command `{other}`. Type `help` for commands.");
            true
        }
    }
}

fn split_command(line: &str) -> (&str, &str) {
    line.split_once(char::is_whitespace)
        .map(|(command, rest)| (command, rest.trim()))
        .unwrap_or((line, ""))
}

fn print_interactive_help() {
    println!("Commands:");
    println!("  check | c                  check the file");
    println!("  reload | r                 reload file, outline, and check result");
    println!("  theorems | t               list source theorems");
    println!("  select <name|number>       select a theorem from the outline");
    println!("  reset                      show the selected theorem's initial goal");
    println!("  step [count] | n [count]   run one or more tactics in the selected theorem");
    println!("  goals <line> [column]      show goals at a source position");
    println!("  hints                      show hints for the current goals");
    println!("  search <text>              search checked local and imported theorems");
    println!("  explain [theorem]          explain a checked tactic script");
    println!("  accepted                   list accepted root declarations");
    println!("  diagnostics                show diagnostics from the last check");
    println!("  status                     show current interactive state");
    println!("  quit | q                   exit");
}

fn load_outline(path: &Path) -> SourceOutline {
    match fs::read_to_string(path) {
        Ok(source) => outline(&source),
        Err(err) => SourceOutline {
            theorems: Vec::new(),
            diagnostics: vec![Diagnostic {
                severity: DiagnosticSeverity::Error,
                span: None,
                location: None,
                message: format!("could not read `{}`", path.display()),
                notes: vec![err.to_string()],
                suggestions: Vec::new(),
            }],
        },
    }
}

fn print_outline(state: &InteractiveState) {
    if !state.outline.diagnostics.is_empty() {
        print_diagnostics(&state.outline.diagnostics);
        return;
    }
    if state.outline.theorems.is_empty() {
        println!("No source theorems.");
        return;
    }
    for (idx, theorem) in state.outline.theorems.iter().enumerate() {
        let marker = if state.selected_theorem.as_ref() == Some(&theorem.name) {
            "*"
        } else {
            " "
        };
        println!(
            "{marker} {:>2}. {} (line {}, {} tactics)",
            idx + 1,
            theorem.name,
            theorem.line,
            theorem.tactic_count
        );
    }
}

fn select_theorem(state: &mut InteractiveState, selector: &str) {
    if selector.is_empty() {
        print_outline(state);
        return;
    }

    let selected = if let Ok(index) = selector.parse::<usize>() {
        state
            .outline
            .theorems
            .get(index.saturating_sub(1))
            .map(|theorem| theorem.name.clone())
    } else {
        state
            .outline
            .theorems
            .iter()
            .find(|theorem| theorem.name == selector)
            .map(|theorem| theorem.name.clone())
    };

    match selected {
        Some(name) => {
            state.selected_theorem = Some(name.clone());
            state.next_tactic_index = 0;
            state.current_goals = None;
            println!("Selected theorem: {name}");
            reset_selected_theorem(state);
        }
        None => println!("No theorem matched `{selector}`."),
    }
}

fn reset_selected_theorem(state: &mut InteractiveState) {
    let Some(index) = state.selected_outline_index() else {
        println!("No theorem selected.");
        return;
    };
    let theorem = &state.outline.theorems[index];
    let position = Position {
        line: theorem.line,
        column: 1,
    };
    let result = if state.hol_shadow {
        goals_at_path_with_hol_shadow(&state.path, position)
    } else {
        goals_at_path(&state.path, position)
    };
    state.next_tactic_index = result.next_tactic_index;
    state.current_goals = Some(result.clone());
    print_goal_result(&result);
}

fn step_selected_theorem(state: &mut InteractiveState, rest: &str) {
    let Some(theorem) = state.selected_theorem.clone() else {
        println!("No theorem selected.");
        return;
    };
    let count = if rest.is_empty() {
        1
    } else {
        match rest.parse::<usize>() {
            Ok(count) if count > 0 => count,
            _ => {
                println!("step count must be a positive integer");
                return;
            }
        }
    };

    let mut result = None;
    for _ in 0..count {
        let step = if state.hol_shadow {
            run_tactic_at_path_with_hol_shadow(&state.path, &theorem, state.next_tactic_index)
        } else {
            run_tactic_at_path(&state.path, &theorem, state.next_tactic_index)
        };
        state.next_tactic_index = step.next_tactic_index;
        let should_stop = step.completed || diagnostics_have_errors(&step.diagnostics);
        result = Some(step);
        if should_stop {
            break;
        }
    }

    if let Some(step) = result {
        state.current_goals = Some(step.clone());
        print_goal_result(&step);
    }
}

fn show_goals_at_position(state: &mut InteractiveState, rest: &str) {
    let mut parts = rest.split_whitespace();
    let Some(line) = parts.next().and_then(|part| part.parse::<usize>().ok()) else {
        println!("usage: goals <line> [column]");
        return;
    };
    let column = parts
        .next()
        .and_then(|part| part.parse::<usize>().ok())
        .unwrap_or(1);
    let position = Position { line, column };
    let result = if state.hol_shadow {
        goals_at_path_with_hol_shadow(&state.path, position)
    } else {
        goals_at_path(&state.path, position)
    };
    state.next_tactic_index = result.next_tactic_index;
    if let Some(theorem) = &result.theorem {
        state.selected_theorem = Some(theorem.clone());
    }
    state.current_goals = Some(result.clone());
    print_goal_result(&result);
}

fn print_goal_result(result: &GoalStepResult) {
    if !result.diagnostics.is_empty() {
        print_diagnostics(&result.diagnostics);
    }
    match &result.theorem {
        Some(theorem) => println!(
            "{}: tactic {}/{}{}",
            theorem,
            result.next_tactic_index,
            result.tactic_count,
            if result.completed { " (complete)" } else { "" }
        ),
        None => println!("No theorem selected by this proof state."),
    }
    if let Some(fragment) = result.statement_fragment {
        println!("Certified statement fragment: {fragment}");
    }
    if result.goals.is_empty() {
        println!(
            "{}",
            if result.completed {
                "Complete."
            } else {
                "No goals."
            }
        );
        return;
    }
    for (idx, goal) in result.goals.iter().enumerate() {
        print_goal(idx + 1, goal);
    }
}

fn print_goal(index: usize, goal: &GoalSnapshot) {
    println!("Goal {index}:");
    if goal.context.is_empty() {
        println!("  Context: (empty)");
    } else {
        println!("  Context:");
        for entry in &goal.context {
            println!("    {entry}");
        }
    }
    println!("  Target:");
    println!("    |- {}", goal.target);
    if !goal.hints.is_empty() {
        println!("  Hints:");
        for hint in goal.hints.iter().take(6) {
            println!("    {}: `{}`", hint.title, hint.tactic);
            println!("      {}", hint.detail);
        }
    }
}

fn print_current_hints(state: &InteractiveState) {
    let Some(result) = &state.current_goals else {
        println!("No current goals. Use `reset`, `step`, or `goals <line>` first.");
        return;
    };
    for (idx, goal) in result.goals.iter().enumerate() {
        println!("Goal {} hints:", idx + 1);
        if goal.hints.is_empty() {
            println!("  (none)");
        } else {
            for hint in &goal.hints {
                println!("  {}: `{}`", hint.title, hint.tactic);
                println!("    {}", hint.detail);
            }
        }
    }
}

fn search_theorems(state: &mut InteractiveState, query: &str) {
    if query.is_empty() {
        println!("usage: search <text>");
        return;
    }
    if diagnostics_have_errors(&state.last_check.diagnostics) {
        println!("The last check had diagnostics; search results may be incomplete.");
    }
    let query = query.to_lowercase();
    let mut matches = state
        .last_check
        .theorems
        .iter()
        .filter(|theorem| {
            theorem.name.to_lowercase().contains(&query)
                || theorem.statement.to_lowercase().contains(&query)
        })
        .collect::<Vec<_>>();
    matches.sort_by_key(|theorem| (theorem.is_imported, theorem.name.clone()));

    if matches.is_empty() {
        println!("No matching theorems.");
        return;
    }
    for (idx, theorem) in matches.iter().take(25).enumerate() {
        let origin = if theorem.is_imported {
            "imported"
        } else {
            "local"
        };
        let kind = if theorem.is_axiom { "axiom" } else { "theorem" };
        println!(
            "{:>2}. [{} {kind} {}] {} : {}",
            idx + 1,
            origin,
            theorem_display_label(theorem),
            theorem.name,
            theorem.statement
        );
    }
    if matches.len() > 25 {
        println!("Showing 25 of {} matches.", matches.len());
    }
}

fn explain_selected_or_named_theorem(state: &InteractiveState, name: &str) {
    let theorem = if name.is_empty() {
        match &state.selected_theorem {
            Some(name) => name.as_str(),
            None => {
                println!("No theorem selected.");
                return;
            }
        }
    } else {
        name
    };
    let result = if state.hol_shadow {
        explain_theorem_at_path_with_hol_shadow(&state.path, theorem)
    } else {
        explain_theorem_at_path(&state.path, theorem)
    };
    print_explanation(&result);
}

fn print_explanation(result: &ExplanationResult) {
    if diagnostics_have_errors(&result.diagnostics) && result.steps.is_empty() {
        print_diagnostics(&result.diagnostics);
        return;
    }
    println!(
        "{}{}",
        result.theorem.as_deref().unwrap_or("(unknown theorem)"),
        if result.completed {
            ""
        } else {
            " (incomplete)"
        }
    );
    if let Some(statement) = &result.statement {
        println!("Statement: {statement}");
    }
    if let Some(fragment) = result.statement_fragment {
        println!("Certified statement fragment: {fragment}");
    }
    for step in &result.steps {
        println!();
        println!("Line {}: {}", step.line, step.tactic);
        println!("  Before: |- {}", step.before.target);
        for sentence in &step.explanation {
            println!("  - {sentence}");
        }
        if step.after.is_empty() {
            println!("  After: current goal closed");
        } else {
            println!("  After:");
            for (idx, goal) in step.after.iter().enumerate() {
                println!("    {}. |- {}", idx + 1, goal.target);
            }
        }
    }
    if !result.diagnostics.is_empty() {
        println!();
        println!("Explanation stopped with diagnostics:");
        print_diagnostics(&result.diagnostics);
    }
}

fn print_accepted_summary(result: &CheckResult) {
    let count = result
        .theorems
        .iter()
        .filter(|theorem| !theorem.is_imported)
        .count();
    println!("Accepted {count} root declarations.");
}

fn print_accepted(result: &CheckResult) {
    let mut accepted = false;
    for theorem in result
        .theorems
        .iter()
        .filter(|theorem| !theorem.is_imported)
    {
        accepted = true;
        let kind = if theorem.is_axiom { "axiom" } else { "theorem" };
        let disposition = match theorem.status {
            DeclarationStatus::Accepted => "accepted",
            DeclarationStatus::Incomplete => "incomplete",
            DeclarationStatus::TrustedAxiom => "trusted",
        };
        let mut notes = if theorem.is_axiom {
            Vec::new()
        } else {
            vec![theorem_display_label(theorem)]
        };
        if theorem.uses_sorry {
            notes.push("uses sorry".to_string());
        }
        if !theorem.is_axiom && !theorem.axiom_deps.is_empty() {
            notes.push(format!("axioms: {}", theorem.axiom_deps.join(", ")));
        }
        if notes.is_empty() {
            println!("{disposition} {kind} {}", theorem.name);
        } else {
            println!(
                "{disposition} {kind} {} ({})",
                theorem.name,
                notes.join("; ")
            );
        }
    }
    if !accepted && !diagnostics_have_errors(&result.diagnostics) {
        println!("accepted file");
    }
}

fn check_result_json(
    result: &CheckResult,
    policy: CheckPolicy,
    violations: &[PolicyViolation],
    shadow: Option<&HolShadowReport>,
    hol_policy: Option<HolTeachingPolicy>,
    hol_violations: &[HolPolicyViolation],
    assignment: Option<&LoadedAssignment>,
) -> String {
    let theorems = result
        .theorems
        .iter()
        .map(checked_theorem_json)
        .collect::<Vec<_>>()
        .join(",");
    let diagnostics = result
        .diagnostics
        .iter()
        .map(diagnostic_json)
        .collect::<Vec<_>>()
        .join(",");
    let violations = violations
        .iter()
        .map(policy_violation_json)
        .collect::<Vec<_>>()
        .join(",");
    let ok = !diagnostics_have_errors(&result.diagnostics)
        && violations.is_empty()
        && hol_violations.is_empty()
        && shadow.is_none_or(HolShadowReport::is_match);
    let shadow = shadow
        .map(|shadow| format!(r#","hol_shadow":{}"#, hol_shadow_json(shadow)))
        .unwrap_or_default();
    let hol_policy = hol_policy
        .map(|policy| {
            let violations = hol_violations
                .iter()
                .map(hol_policy_violation_json)
                .collect::<Vec<_>>()
                .join(",");
            format!(
                r#","hol_policy":{},"hol_policy_violations":[{}]"#,
                hol_teaching_policy_json(policy),
                violations,
            )
        })
        .unwrap_or_default();
    let assignment = assignment
        .map(|assignment| {
            format!(
                r#","assignment_manifest":{}"#,
                assignment_manifest_json(assignment)
            )
        })
        .unwrap_or_default();
    format!(
        r#"{{"ok":{ok},"policy":{{"deny_sorry":{},"deny_root_axioms":{},"deny_classical":{}}},"theorems":[{theorems}],"diagnostics":[{diagnostics}],"policy_violations":[{violations}]{shadow}{hol_policy}{assignment}}}"#,
        policy.deny_sorry, policy.deny_root_axioms, policy.deny_classical,
    )
}

fn hol_teaching_policy_json(policy: HolTeachingPolicy) -> String {
    format!(
        r#"{{"profile":{},"allow_classical":{},"allow_extensionality":{},"allow_choice":{},"allow_axioms":{},"allow_incomplete":{}}}"#,
        json_string(policy.profile_label()),
        policy.allow_classical,
        policy.allow_extensionality,
        policy.allow_choice,
        policy.allow_axioms,
        policy.allow_incomplete,
    )
}

fn assignment_manifest_json(assignment: &LoadedAssignment) -> String {
    let imports = assignment
        .manifest
        .allowed_imports
        .iter()
        .map(|path| json_string(path))
        .collect::<Vec<_>>()
        .join(",");
    let axioms = assignment
        .manifest
        .allowed_axioms
        .iter()
        .map(|name| json_string(name))
        .collect::<Vec<_>>()
        .join(",");
    let required = assignment
        .manifest
        .required_theorems
        .iter()
        .map(|theorem| {
            format!(
                r#"{{"name":{},"signature":{}}}"#,
                json_string(&theorem.name),
                json_string(&theorem.signature)
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let path = display_diagnostic_path(&assignment.path.to_string_lossy());
    format!(
        r#"{{"path":{},"version":{},"allowed_imports":[{}],"allowed_axioms":[{}],"required_theorems":[{}]}}"#,
        json_string(&path),
        assignment.manifest.version,
        imports,
        axioms,
        required,
    )
}

fn hol_policy_violation_json(violation: &HolPolicyViolation) -> String {
    format!(
        r#"{{"kind":{},"declaration":{},"message":{}}}"#,
        json_string(violation.kind),
        json_string(&violation.declaration),
        json_string(&violation.message),
    )
}

fn hol_shadow_json(report: &HolShadowReport) -> String {
    let statement_classifications = report
        .statement_classifications
        .iter()
        .map(hol_shadow_statement_classification_json)
        .collect::<Vec<_>>()
        .join(",");
    let theorems = report
        .theorems
        .iter()
        .map(hol_shadow_theorem_json)
        .collect::<Vec<_>>()
        .join(",");
    let mismatches = report
        .mismatches
        .iter()
        .map(hol_shadow_mismatch_json)
        .collect::<Vec<_>>()
        .join(",");
    let imported_files = report
        .imported_files
        .iter()
        .map(|path| {
            let path = display_diagnostic_path(&path.to_string_lossy());
            json_string(&path)
        })
        .collect::<Vec<_>>()
        .join(",");
    let imported_virtual_files = report
        .imported_virtual_files
        .iter()
        .map(|path| json_string(path))
        .collect::<Vec<_>>()
        .join(",");
    let imported_packages = report
        .imported_packages
        .iter()
        .map(|package| json_string(package))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"matches":{},"attempted_declarations":{},"checked_declarations":{},"imported_files":[{}],"imported_virtual_files":[{}],"imported_packages":[{}],"statement_classifications":[{}],"theorems":[{}],"mismatches":[{}]}}"#,
        report.is_match(),
        report.attempted_declarations,
        report.checked_declarations.len(),
        imported_files,
        imported_virtual_files,
        imported_packages,
        statement_classifications,
        theorems,
        mismatches,
    )
}

fn hol_shadow_statement_classification_json(
    classification: &HolShadowStatementClassification,
) -> String {
    let source_path = classification.source_path.as_ref().map(|path| {
        let path = display_diagnostic_path(&path.to_string_lossy());
        json_string(&path)
    });
    format!(
        r#"{{"name":{},"signature":{},"fragment":{},"line":{},"source_path":{},"is_imported":{}}}"#,
        json_string(&classification.name),
        json_string(&classification.signature),
        json_string(&classification.fragment.to_string()),
        classification.line,
        source_path.unwrap_or_else(|| "null".to_string()),
        classification.is_imported,
    )
}

fn hol_shadow_theorem_json(theorem: &HolShadowTheorem) -> String {
    let axiom_deps = theorem
        .axiom_deps
        .iter()
        .map(|name| json_string(name))
        .collect::<Vec<_>>()
        .join(",");
    let incomplete_deps = theorem
        .incomplete_deps
        .iter()
        .map(|name| json_string(name))
        .collect::<Vec<_>>()
        .join(",");
    let features = theorem
        .features
        .iter()
        .map(|feature| json_string(&feature.to_string()))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"name":{},"statement":{},"signature":{},"legacy_status":{},"hol_status":{},"legacy_mode":{},"hol_mode":{},"statement_fragment":{},"required_fragment":{},"axiom_deps":[{}],"incomplete_deps":[{}],"features":[{}],"is_imported":{}}}"#,
        json_string(&theorem.name),
        json_string(&theorem.statement),
        json_string(&theorem.signature),
        json_string(&theorem.legacy_status.to_string()),
        json_string(hol_evidence_status_label(theorem.hol_status)),
        json_string(&theorem.legacy_mode_used.to_string()),
        json_string(&theorem.hol_mode_used.to_string()),
        json_string(&theorem.statement_fragment.to_string()),
        json_string(&theorem.required_fragment.to_string()),
        axiom_deps,
        incomplete_deps,
        features,
        theorem.is_imported,
    )
}

fn hol_shadow_mismatch_json(mismatch: &HolShadowMismatch) -> String {
    let source_path = mismatch.source_path.as_ref().map(|path| {
        let path = display_diagnostic_path(&path.to_string_lossy());
        json_string(&path)
    });
    format!(
        r#"{{"declaration":{},"kind":{},"line":{},"source_path":{},"is_imported":{},"message":{}}}"#,
        json_string(&mismatch.declaration),
        json_string(&mismatch.kind.to_string()),
        mismatch.line,
        source_path.unwrap_or_else(|| "null".to_string()),
        mismatch.is_imported,
        json_string(&mismatch.message),
    )
}

fn hol_evidence_status_label(status: cetacea_core::hol::EvidenceStatus) -> &'static str {
    match status {
        cetacea_core::hol::EvidenceStatus::Checked => "accepted",
        cetacea_core::hol::EvidenceStatus::Incomplete => "incomplete",
        cetacea_core::hol::EvidenceStatus::TrustedAxiom => "trusted_axiom",
    }
}

fn checked_theorem_json(theorem: &CheckedTheorem) -> String {
    let axiom_deps = theorem
        .axiom_deps
        .iter()
        .map(|name| json_string(name))
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"name":{},"statement":{},"mode":{},"status":{},"is_axiom":{},"is_imported":{},"uses_sorry":{},"axiom_deps":[{}]}}"#,
        json_string(&theorem.name),
        json_string(&theorem.statement),
        json_string(&theorem.mode_used.to_string()),
        json_string(&theorem.status.to_string()),
        theorem.is_axiom,
        theorem.is_imported,
        theorem.uses_sorry,
        axiom_deps,
    )
}

fn diagnostic_json(diagnostic: &Diagnostic) -> String {
    let location = diagnostic
        .location
        .as_ref()
        .map(|location| {
            format!(
                r#"{{"path":{},"line":{}}}"#,
                optional_json_string(
                    location
                        .path
                        .as_deref()
                        .map(display_diagnostic_path)
                        .as_deref()
                ),
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
                optional_json_string(suggestion.example.as_deref()),
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    format!(
        r#"{{"severity":{},"message":{},"location":{},"span":{},"notes":[{}],"suggestions":[{}]}}"#,
        json_string(diagnostic_label(diagnostic)),
        json_string(&diagnostic.message),
        location,
        span,
        notes,
        suggestions,
    )
}

fn policy_violation_json(violation: &PolicyViolation) -> String {
    format!(
        r#"{{"kind":{},"declaration":{},"message":{}}}"#,
        json_string(violation.kind.label()),
        json_string(&violation.declaration),
        json_string(&violation.message),
    )
}

fn optional_json_string(value: Option<&str>) -> String {
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

fn theorem_display_label(theorem: &CheckedTheorem) -> String {
    if theorem.is_axiom {
        "trusted".to_string()
    } else {
        theorem.mode_used.to_string()
    }
}

fn print_diagnostics(diagnostics: &[Diagnostic]) {
    for diagnostic in diagnostics {
        let label = diagnostic_label(diagnostic);
        match &diagnostic.location {
            Some(location) => match &location.path {
                Some(path) => {
                    let path = display_diagnostic_path(path);
                    eprintln!("{label}: {path}:{}: {}", location.line, diagnostic.message)
                }
                None => eprintln!("{label}: line {}: {}", location.line, diagnostic.message),
            },
            None => eprintln!("{label}: {}", diagnostic.message),
        }
        for note in &diagnostic.notes {
            eprintln!("  note: {note}");
        }
        for suggestion in &diagnostic.suggestions {
            eprintln!("  help: {}", suggestion.title);
            eprintln!("    {}", suggestion.detail);
            if let Some(example) = &suggestion.example {
                eprintln!("    try:\n{}", indent_block(example, "      "));
            }
        }
    }
}

fn display_diagnostic_path(path: &str) -> String {
    let path = Path::new(path);
    if let Ok(current_dir) = env::current_dir() {
        if let Ok(relative) = path.strip_prefix(current_dir) {
            return relative.display().to_string();
        }
    }
    path.display().to_string()
}

fn diagnostic_label(diagnostic: &Diagnostic) -> &'static str {
    match diagnostic.severity {
        DiagnosticSeverity::Error => "error",
        DiagnosticSeverity::Warning => "warning",
    }
}

fn fail_closed_hol_result(report: HolShadowReport) -> CheckResult {
    let matches = report.is_match();
    let attempted = report.attempted_declarations;
    let checked = report.checked_declarations.len();
    let mut result = report.legacy;
    for mismatch in report.mismatches {
        result.diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Error,
            span: None,
            location: Some(SourceLocation {
                path: mismatch
                    .source_path
                    .as_ref()
                    .map(|path| path.display().to_string()),
                line: mismatch.line,
            }),
            message: format!(
                "HOL replay rejected {} `{}`: {}",
                mismatch.kind, mismatch.declaration, mismatch.message
            ),
            notes: Vec::new(),
            suggestions: Vec::new(),
        });
    }
    if !matches && result.diagnostics.is_empty() {
        result.diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Error,
            span: None,
            location: None,
            message: format!(
                "HOL replay checked {checked} of {attempted} accepted declaration attempts"
            ),
            notes: Vec::new(),
            suggestions: Vec::new(),
        });
    }
    result
}

fn check_editor_path(path: &Path, force_hol: bool) -> (CheckResult, bool) {
    if force_hol {
        return (
            fail_closed_hol_result(check_file_at_path_with_hol_shadow(path)),
            true,
        );
    }
    let legacy = check_file_at_path(path);
    if legacy.requires_hol_shadow {
        (
            fail_closed_hol_result(check_file_at_path_with_hol_shadow(path)),
            true,
        )
    } else {
        (legacy, false)
    }
}

fn check_editor_source(source: &str, path: &Path, force_hol: bool) -> (CheckResult, bool) {
    if force_hol {
        return (
            fail_closed_hol_result(check_source_at_path_with_hol_shadow(source, path)),
            true,
        );
    }
    let legacy = check_source_at_path(source, path);
    if legacy.requires_hol_shadow {
        (
            fail_closed_hol_result(check_source_at_path_with_hol_shadow(source, path)),
            true,
        )
    } else {
        (legacy, false)
    }
}

fn diagnostics_have_errors(diagnostics: &[Diagnostic]) -> bool {
    diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == DiagnosticSeverity::Error)
}

fn indent_block(text: &str, prefix: &str) -> String {
    text.lines()
        .map(|line| format!("{prefix}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| value.to_string()).collect()
    }

    #[test]
    fn parse_args_accepts_strict_json_policy_flags() {
        let config = parse_args(&args(&[
            "--strict",
            "--deny-classical",
            "--json",
            "submission.ctea",
        ]))
        .expect("arguments should parse");
        assert_eq!(config.mode, RunMode::Check);
        assert_eq!(config.path, PathBuf::from("submission.ctea"));
        assert_eq!(config.output_format, OutputFormat::Json);
        assert!(!config.hol_shadow);
        assert!(config.hol_policy.is_none());
        assert!(config.assignment_path.is_none());
        assert_eq!(
            config.policy,
            CheckPolicy {
                deny_sorry: true,
                deny_root_axioms: true,
                deny_classical: true,
            }
        );
        let reversed = parse_args(&args(&["--deny-classical", "--strict", "submission.ctea"]))
            .expect("policy flags should compose in any order");
        assert_eq!(reversed.policy, config.policy);
    }

    #[test]
    fn parse_args_rejects_check_policy_in_interactive_modes() {
        assert!(parse_args(&args(&["--tui", "--strict", "submission.ctea"])).is_none());
        assert!(parse_args(&args(&["--line", "--json", "submission.ctea"])).is_none());
        assert!(parse_args(&args(
            &["--tui", "--hol-profile", "fol", "submission.ctea",]
        ))
        .is_none());
        assert!(parse_args(&args(&[
            "--line",
            "--hol-shadow",
            "--json",
            "submission.ctea",
        ]))
        .is_none());
        let tui = parse_args(&args(&["--tui", "--hol-shadow", "submission.ctea"]))
            .expect("TUI should accept opt-in HOL-certified editor analysis");
        assert_eq!(tui.mode, RunMode::Tui);
        assert!(tui.hol_shadow);
        let line = parse_args(&args(&["--hol-shadow", "--line", "submission.ctea"]))
            .expect("line mode should accept opt-in HOL-certified editor analysis");
        assert_eq!(line.mode, RunMode::LineInteractive);
        assert!(line.hol_shadow);
    }

    #[test]
    fn parse_args_accepts_hol_shadow_in_check_mode() {
        let config = parse_args(&args(&["--hol-shadow", "--json", "submission.ctea"]))
            .expect("HOL shadow arguments should parse");
        assert!(config.hol_shadow);
        assert_eq!(config.output_format, OutputFormat::Json);
    }

    #[test]
    fn parse_args_accepts_hol_profiles_and_rejects_conflicting_permissions() {
        let config = parse_args(&args(&[
            "--hol-profile",
            "fol+induction",
            "--allow-classical",
            "--allow-axioms",
            "submission.ctea",
        ]))
        .expect("HOL teaching profile should parse");
        assert!(config.hol_shadow);
        assert_eq!(
            config.hol_policy,
            Some(HolTeachingPolicy {
                profile: TeachingProfile::FirstOrderInductive,
                allow_classical: true,
                allow_extensionality: false,
                allow_choice: false,
                allow_axioms: true,
                allow_incomplete: false,
            })
        );

        let inline = parse_args(&args(&["--hol-profile=fol", "submission.ctea"]))
            .expect("inline HOL profile should parse");
        assert_eq!(
            inline.hol_policy.expect("profile").profile,
            TeachingProfile::FirstOrder
        );
        assert!(parse_args(&args(&["--allow-classical", "submission.ctea"])).is_none());
        assert!(parse_args(&args(&[
            "--hol-profile",
            "hol",
            "--allow-incomplete",
            "--deny-sorry",
            "submission.ctea",
        ]))
        .is_none());
        assert!(parse_args(&args(&[
            "--hol-profile",
            "fol",
            "--hol-profile",
            "hol",
            "submission.ctea",
        ]))
        .is_none());
    }

    #[test]
    fn parse_args_accepts_assignment_manifest_as_an_exclusive_policy_source() {
        let config = parse_args(&args(&[
            "--assignment",
            "homework.ctea-assignment",
            "--json",
            "submission.ctea",
        ]))
        .expect("assignment manifest arguments should parse");
        assert_eq!(
            config.assignment_path,
            Some(PathBuf::from("homework.ctea-assignment"))
        );
        assert!(config.hol_shadow);
        assert!(config.hol_policy.is_none());
        assert!(parse_args(&args(&[
            "--assignment=homework.ctea-assignment",
            "--hol-profile",
            "fol",
            "submission.ctea",
        ]))
        .is_none());
        assert!(parse_args(&args(&[
            "--assignment",
            "homework.ctea-assignment",
            "--allow-axioms",
            "submission.ctea",
        ]))
        .is_none());
        assert!(parse_args(&args(&[
            "--tui",
            "--assignment",
            "homework.ctea-assignment",
            "submission.ctea",
        ]))
        .is_none());
    }

    fn hol_policy(profile: TeachingProfile) -> HolTeachingPolicy {
        HolTeachingPolicy {
            profile,
            allow_classical: false,
            allow_extensionality: false,
            allow_choice: false,
            allow_axioms: false,
            allow_incomplete: false,
        }
    }

    #[test]
    fn hol_profiles_enforce_fragment_boundaries() {
        let report = cetacea_core::check_file_with_hol_shadow(
            r#"
mode constructive
sort Person

theorem prop_id (P : Prop) : P -> P := by
  intro h
  exact h

theorem person_refl (x : Person) : x = x := by
  refl

theorem nat_refl (n : Nat) : n = n := by
  refl
"#,
        );
        assert!(report.is_match());

        let prop = check_hol_policy_violations(&report, hol_policy(TeachingProfile::Prop), None);
        assert_eq!(prop.len(), 2);
        assert!(prop
            .iter()
            .any(|violation| violation.declaration == "person_refl"));
        assert!(prop
            .iter()
            .any(|violation| violation.declaration == "nat_refl"));

        let fol =
            check_hol_policy_violations(&report, hol_policy(TeachingProfile::FirstOrder), None);
        assert_eq!(fol.len(), 1);
        assert_eq!(fol[0].declaration, "nat_refl");
        assert_eq!(fol[0].kind, "statement_fragment");

        let induction = check_hol_policy_violations(
            &report,
            hol_policy(TeachingProfile::FirstOrderInductive),
            None,
        );
        assert!(induction.is_empty());
    }

    #[test]
    fn hol_profiles_separate_fragment_from_classical_trust_and_incompleteness() {
        let report = cetacea_core::check_file_with_hol_shadow(
            r#"
mode classical

axiom trusted : True

theorem excluded_middle (P : Prop) : P \/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h

theorem unfinished : True := by
  sorry
"#,
        );
        assert!(report.is_match());
        let strict =
            check_hol_policy_violations(&report, hol_policy(TeachingProfile::HigherOrder), None);
        assert_eq!(strict.len(), 3);
        assert!(strict.iter().any(|violation| violation.kind == "feature"));
        assert!(strict
            .iter()
            .any(|violation| violation.message.contains("trusted")));
        assert!(strict
            .iter()
            .any(|violation| violation.message.contains("unfinished")));

        let permissive = check_hol_policy_violations(
            &report,
            HolTeachingPolicy {
                profile: TeachingProfile::HigherOrder,
                allow_classical: true,
                allow_extensionality: true,
                allow_choice: true,
                allow_axioms: true,
                allow_incomplete: true,
            },
            None,
        );
        assert!(permissive.is_empty());
    }

    #[test]
    fn hol_profile_checks_only_root_receipts_but_follows_used_imports() {
        let imports = vec![cetacea_core::VirtualFile {
            path: "trusted.ctea".to_string(),
            source: "axiom imported_trust : True\n".to_string(),
        }];
        let report = cetacea_core::check_file_with_imports_and_hol_shadow(
            r#"
import trusted.ctea

theorem independent (P : Prop) : P -> P := by
  intro h
  exact h

theorem uses_imported_trust : True := by
  exact imported_trust
"#,
            &imports,
        );
        assert!(report.is_match());
        assert_eq!(report.imported_virtual_files, ["trusted.ctea"]);
        let violations =
            check_hol_policy_violations(&report, hol_policy(TeachingProfile::Prop), None);
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].declaration, "uses_imported_trust");
        assert!(violations[0].message.contains("imported_trust"));
    }

    #[test]
    fn check_mode_automatically_certifies_a_transitive_logical_package_import() {
        let unique = format!(
            "cetacea-auto-hol-{}-{:?}",
            process::id(),
            std::thread::current().id()
        );
        let dir = env::temp_dir().join(unique);
        fs::create_dir_all(&dir).expect("create automatic HOL fixture");
        let library_path = dir.join("library.ctea");
        let root_path = dir.join("root.ctea");
        fs::write(
            &library_path,
            r#"import std/hol/list@1 as L

theorem imported_right (A : Type) (xs : L.List A) :
  L.append(xs, (L.nil : L.List A)) = xs := by
  exact L.append_nil_right {A := A; xs := xs}
"#,
        )
        .expect("write automatic HOL library");
        fs::write(
            &root_path,
            r#"import library.ctea

theorem root_right (A : Type) (xs : L.List A) :
  L.append(xs, (L.nil : L.List A)) = xs := by
  exact imported_right {A := A; xs := xs}
"#,
        )
        .expect("write automatic HOL root");

        let legacy = check_file_at_path(&root_path);
        assert!(legacy.requires_hol_shadow);
        let (editor_check, editor_hol) = check_editor_path(&root_path, false);
        assert!(editor_hol);
        assert!(editor_check.diagnostics.is_empty());

        let mut line = InteractiveState::new(root_path.clone(), false);
        line.reload();
        assert!(line.hol_shadow);
        assert!(line.last_check.diagnostics.is_empty());

        let mut tui = TuiApp::open(root_path.clone(), false).expect("open automatic HOL TUI");
        tui.refresh_analysis();
        assert!(tui.hol_shadow);
        assert!(tui.check_result.diagnostics.is_empty());
        tui.buffer = TextBuffer::from_source(
            "theorem plain (P : Prop) : P -> P := by\n  intro h\n  exact h\n".to_string(),
        );
        tui.refresh_analysis();
        assert!(!tui.hol_shadow);
        assert!(tui.check_result.diagnostics.is_empty());

        assert_eq!(
            run_check(
                &root_path,
                CheckPolicy::default(),
                OutputFormat::Text,
                false,
                None,
                None,
            ),
            0
        );

        fs::remove_dir_all(dir).expect("remove automatic HOL fixture");
    }

    #[test]
    fn assignment_manifest_pins_import_axiom_and_required_signature_independently() {
        let unique = format!(
            "cetacea-assignment-{}-{:?}",
            process::id(),
            std::thread::current().id()
        );
        let dir = env::temp_dir().join(unique);
        fs::create_dir_all(&dir).expect("create assignment fixture");
        let library_path = dir.join("library.ctea");
        let submission_path = dir.join("submission.ctea");
        let manifest_path = dir.join("homework.ctea-assignment");
        fs::write(&library_path, "axiom imported_trust : True\n")
            .expect("write assignment library");
        fs::write(
            &submission_path,
            "import library.ctea\n\nsort Person\n\ntheorem exercise_3 : True := by\n  exact imported_trust\n\ntheorem typed_refl (x : Person) : x = x := by\n  refl\n",
        )
        .expect("write assignment submission");
        fs::write(
            &manifest_path,
            r#"
version = 1
profile = "fol"
allow_new_axioms = false
allowed_imports = ["library.ctea"]
allowed_axioms = ["imported_trust"]
required_theorem.exercise_3 = "True"
required_theorem.typed_refl = "(x : Person) : x = x"
"#,
        )
        .expect("write assignment manifest");

        let assignment = load_assignment(&manifest_path).expect("load assignment manifest");
        let report = check_file_at_path_with_hol_shadow(&submission_path);
        assert!(report.is_match());
        assert_eq!(
            report.imported_files,
            [library_path.canonicalize().expect("canonical library")]
        );
        let policy = assignment.teaching_policy();
        assert!(report
            .theorems
            .iter()
            .any(|theorem| theorem.name == "typed_refl"
                && theorem.signature == "(x : Person) : x = x"));
        let accepted = check_hol_policy_violations(&report, policy, Some(&assignment));
        assert!(accepted.is_empty(), "{accepted:?}");

        let mut unallowed_import = assignment.clone();
        unallowed_import.allowed_imports.clear();
        let import_violations =
            check_hol_policy_violations(&report, policy, Some(&unallowed_import));
        assert!(import_violations
            .iter()
            .any(|violation| violation.kind == "import"));

        let mut unallowed_axiom = assignment.clone();
        unallowed_axiom.manifest.allowed_axioms.clear();
        let axiom_violations = check_hol_policy_violations(&report, policy, Some(&unallowed_axiom));
        assert!(axiom_violations
            .iter()
            .any(|violation| violation.kind == "trusted_axiom"));

        let mut weakened_signature = assignment.clone();
        weakened_signature.manifest.required_theorems[0].signature = "False".to_string();
        let signature_violations =
            check_hol_policy_violations(&report, policy, Some(&weakened_signature));
        assert!(signature_violations
            .iter()
            .any(|violation| violation.kind == "theorem_signature"));

        let mut missing_theorem = assignment.clone();
        missing_theorem.manifest.required_theorems[0].name = "missing".to_string();
        let missing_violations =
            check_hol_policy_violations(&report, policy, Some(&missing_theorem));
        assert!(missing_violations
            .iter()
            .any(|violation| violation.kind == "required_theorem"));

        let json = check_result_json(
            &report.legacy,
            CheckPolicy::default(),
            &[],
            Some(&report),
            Some(policy),
            &accepted,
            Some(&assignment),
        );
        assert!(json.contains(r#""assignment_manifest":{"path":"#));
        assert!(json.contains(r#""allowed_imports":["library.ctea"]"#));
        assert!(json.contains(r#""required_theorems":[{"name":"exercise_3""#));
        assert!(json.contains(r#""signature":"True""#));

        fs::remove_dir_all(&dir).expect("remove assignment fixture");
    }

    #[test]
    fn assignment_manifest_allows_exact_versioned_hol_package_imports() {
        let unique = format!(
            "cetacea-package-assignment-{}-{:?}",
            process::id(),
            std::thread::current().id()
        );
        let dir = env::temp_dir().join(unique);
        fs::create_dir_all(&dir).expect("create package assignment fixture");
        let manifest_path = dir.join("package.ctea-assignment");
        fs::write(
            &manifest_path,
            r#"
version = 1
profile = "fol+induction"
allowed_imports = ["std/hol/list@1"]
"#,
        )
        .expect("write package assignment manifest");
        let assignment = load_assignment(&manifest_path).expect("load package assignment");
        assert_eq!(
            assignment.allowed_package_imports,
            BTreeSet::from(["std/hol/list@1".to_string()])
        );
        let report = cetacea_core::check_file_with_hol_shadow(
            r#"
import std/hol/list@1 as L
theorem list_refl (xs : L.List Nat) : xs = xs := by
  refl
"#,
        );
        assert!(report.is_match());
        assert_eq!(report.imported_packages, ["std/hol/list@1"]);
        let policy = assignment.teaching_policy();
        assert!(check_hol_policy_violations(&report, policy, Some(&assignment)).is_empty());

        let mut denied = assignment.clone();
        denied.allowed_package_imports.clear();
        let violations = check_hol_policy_violations(&report, policy, Some(&denied));
        assert!(violations.iter().any(|violation| {
            violation.kind == "import" && violation.message.contains("std/hol/list@1")
        }));
        let json = hol_shadow_json(&report);
        assert!(json.contains(r#""imported_packages":["std/hol/list@1"]"#));

        let finite_report = cetacea_core::check_file_with_hol_shadow(
            r#"
import std/hol/finite@1 as F
theorem finite_refl (xs : F.List Nat) (n : Nat) :
  F.HasCard(xs, n) -> F.HasCard(xs, n) := by
  intro h
  exact h
"#,
        );
        assert!(finite_report.is_match());
        assert_eq!(
            finite_report.imported_packages,
            ["std/hol/finite@1", "std/hol/list@1"]
        );
        let mut finite_assignment = assignment.clone();
        finite_assignment.allowed_package_imports =
            BTreeSet::from(["std/hol/finite@1".to_string()]);
        let violations =
            check_hol_policy_violations(&finite_report, policy, Some(&finite_assignment));
        assert!(violations.iter().any(|violation| {
            violation.kind == "import" && violation.message.contains("std/hol/list@1")
        }));
        finite_assignment
            .allowed_package_imports
            .insert("std/hol/list@1".to_string());
        assert!(
            check_hol_policy_violations(&finite_report, policy, Some(&finite_assignment))
                .is_empty()
        );

        fs::remove_dir_all(&dir).expect("remove package assignment fixture");
    }

    #[test]
    fn assignment_manifest_cannot_whitelist_a_student_local_axiom_by_name() {
        let report = cetacea_core::check_file_with_hol_shadow(
            r#"
axiom local_trust : True

theorem exploit : True := by
  exact local_trust
"#,
        );
        assert!(report.is_match());
        let manifest = parse_manifest(
            r#"
version = 1
profile = "prop"
allowed_imports = []
allowed_axioms = ["local_trust"]
"#,
        )
        .expect("manifest should parse");
        let assignment = LoadedAssignment {
            path: PathBuf::from("assignment.ctea-assignment"),
            manifest,
            allowed_imports: BTreeSet::new(),
            allowed_package_imports: BTreeSet::new(),
        };
        let violations =
            check_hol_policy_violations(&report, assignment.teaching_policy(), Some(&assignment));
        assert!(violations.iter().any(|violation| {
            violation.kind == "allowed_axiom"
                && violation.message.contains("only imported trusted axioms")
        }));
        assert!(violations
            .iter()
            .any(|violation| violation.kind == "trusted_axiom"));
    }

    #[test]
    fn strict_policy_rejects_root_axioms_and_transitive_sorry() {
        let result = cetacea_core::check_file(
            r#"
mode constructive

axiom trusted : True

theorem incomplete : True := by
  sorry

theorem depends_on_incomplete : True := by
  exact incomplete
"#,
        );
        assert!(!diagnostics_have_errors(&result.diagnostics));
        let violations = check_policy_violations(&result, CheckPolicy::strict());
        assert_eq!(violations.len(), 3);
        assert_eq!(
            violations
                .iter()
                .filter(|violation| violation.kind == PolicyViolationKind::Sorry)
                .count(),
            2
        );
        assert!(violations
            .iter()
            .any(|violation| violation.kind == PolicyViolationKind::RootAxiom));
    }

    #[test]
    fn deny_classical_rejects_only_classical_root_theorems() {
        let result = cetacea_core::check_file(
            r#"
mode classical

theorem constructive_id (P : Prop) : P -> P := by
  intro h
  exact h

theorem excluded_middle (P : Prop) : P \/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h
"#,
        );
        assert!(!diagnostics_have_errors(&result.diagnostics));
        let violations = check_policy_violations(
            &result,
            CheckPolicy {
                deny_classical: true,
                ..CheckPolicy::default()
            },
        );
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].declaration, "excluded_middle");
        assert_eq!(violations[0].kind, PolicyViolationKind::Classical);
    }

    #[test]
    fn strict_policy_ignores_unused_imported_axioms() {
        let result = CheckResult {
            theorems: vec![CheckedTheorem {
                name: "set.set_ext".to_string(),
                statement: "True".to_string(),
                mode_used: cetacea_core::LogicMode::Constructive,
                is_axiom: true,
                is_imported: true,
                uses_sorry: false,
                axiom_deps: vec!["set.set_ext".to_string()],
                status: DeclarationStatus::TrustedAxiom,
            }],
            diagnostics: Vec::new(),
            requires_hol_shadow: false,
        };
        assert!(check_policy_violations(&result, CheckPolicy::strict()).is_empty());
    }

    #[test]
    fn json_output_includes_policy_violations_and_escapes_strings() {
        let result = cetacea_core::check_file(
            r#"
mode constructive
theorem unfinished : True := by
  sorry
"#,
        );
        let policy = CheckPolicy::strict();
        let violations = check_policy_violations(&result, policy);
        let json = check_result_json(&result, policy, &violations, None, None, &[], None);
        assert!(json.contains(r#""ok":false"#));
        assert!(json.contains(r#""kind":"sorry""#));
        assert!(json.contains(r#""declaration":"unfinished""#));
        assert!(json.contains(r#""status":"incomplete""#));
        assert_eq!(json_string("a\"b\\c\n"), r#""a\"b\\c\n""#);
    }

    #[test]
    fn json_output_includes_opt_in_hol_shadow_receipts() {
        let report = cetacea_core::check_file_with_hol_shadow(
            r#"
mode constructive
theorem identity (P : Prop) : P -> P := by
  intro h
  exact h
"#,
        );
        assert!(report.is_match());
        let json = check_result_json(
            &report.legacy,
            CheckPolicy::default(),
            &[],
            Some(&report),
            None,
            &[],
            None,
        );
        assert!(json.contains(r#""hol_shadow":{"matches":true"#));
        assert!(json.contains(r#""statement_classifications":[{"name":"identity""#));
        assert!(json.contains(r#""required_fragment":"prop""#));
        assert!(json.contains(r#""name":"identity""#));
    }

    #[test]
    fn json_output_includes_named_hol_profile_violations() {
        let report = cetacea_core::check_file_with_hol_shadow(
            r#"
mode constructive
theorem nat_refl (n : Nat) : n = n := by
  refl
"#,
        );
        let policy = hol_policy(TeachingProfile::FirstOrder);
        let violations = check_hol_policy_violations(&report, policy, None);
        let json = check_result_json(
            &report.legacy,
            CheckPolicy::default(),
            &[],
            Some(&report),
            Some(policy),
            &violations,
            None,
        );
        assert!(json.contains(r#""ok":false"#));
        assert!(json.contains(r#""hol_policy":{"profile":"fol""#));
        assert!(json.contains(r#""kind":"statement_fragment""#));
        assert!(json.contains(r#""declaration":"nat_refl""#));
    }

    #[test]
    fn diagnostic_paths_are_relative_inside_the_working_directory() {
        let current_dir = env::current_dir().expect("working directory should be available");
        let absolute = current_dir.join("docs/book/code/example.ctea");
        assert_eq!(
            display_diagnostic_path(absolute.to_str().expect("test path should be UTF-8")),
            Path::new("docs/book/code/example.ctea")
                .display()
                .to_string()
        );
        assert_eq!(
            display_diagnostic_path("already/relative.ctea"),
            Path::new("already/relative.ctea").display().to_string()
        );
    }
}
