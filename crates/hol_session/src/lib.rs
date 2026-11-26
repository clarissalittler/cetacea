//! The session API: whole-file checking with imports, per-declaration
//! status, diagnostics, course policies, and goal lookup at a cursor.
//! The CLI and the Wasm binding are thin wrappers over this crate.

use std::collections::{BTreeMap, BTreeSet};

pub mod analysis;
pub mod arith;
pub mod assignment;
pub mod fol;
pub mod prelude;
pub use analysis::{analyze, hints, Analysis, Hint, LibraryEntry, StepView, TheoremView};
pub use assignment::{check_manifest, manifest_from_result, AssignmentReport, Manifest};

use hol_elab::{
    elab_command, elab_theorem_header, print_term, Diagnostic, Env, Status, TheoremInfo,
};
use hol_kernel::{sorry, Name};
use hol_syntax::{parse_file, Command, Mode, Span, Tier};
use hol_tactics::{prove, Goal, StepRecord};
use serde::Serialize;

/// Where files come from: the real file system for the CLI, a virtual
/// one for the browser and tests.
pub trait FileSystem {
    fn read_file(&self, path: &str) -> Option<String>;
}

pub struct RealFs;

impl FileSystem for RealFs {
    fn read_file(&self, path: &str) -> Option<String> {
        std::fs::read_to_string(path).ok()
    }
}

#[derive(Default, Clone)]
pub struct VirtualFs {
    pub files: BTreeMap<String, String>,
}

impl VirtualFs {
    pub fn add(&mut self, path: &str, source: &str) {
        self.files.insert(normalize_path(path), source.to_string());
    }
}

impl FileSystem for VirtualFs {
    fn read_file(&self, path: &str) -> Option<String> {
        self.files.get(&normalize_path(path)).cloned()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
pub struct Policy {
    #[serde(default)]
    pub deny_sorry: bool,
    #[serde(default)]
    pub deny_axioms: bool,
    #[serde(default)]
    pub deny_classical: bool,
    /// Tactics an assignment forbids, such as `simp` or `decide`.
    #[serde(default)]
    pub deny_tactics: Vec<String>,
}

#[derive(Clone, Debug, Default)]
pub struct Options {
    /// Overrides the tier when the file has no `logic` line.
    pub tier: Option<Tier>,
    pub policy: Policy,
    /// Directory that replaces `std/` in import paths during the
    /// transition from the old standard library.
    pub std_dir: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Severity {
    Error,
    Warning,
    Note,
}

#[derive(Clone, Debug, Serialize)]
pub struct Diag {
    pub severity: Severity,
    pub file: Option<String>,
    pub line: u32,
    pub col: u32,
    pub end_line: u32,
    pub end_col: u32,
    pub message: String,
    pub notes: Vec<String>,
    pub suggestion: Option<String>,
}

impl Diag {
    fn from_diagnostic(severity: Severity, file: Option<&str>, diag: Diagnostic) -> Diag {
        Diag {
            severity,
            file: file.map(str::to_string),
            line: diag.span.line,
            col: diag.span.col,
            end_line: diag.span.end_line,
            end_col: diag.span.end_col,
            message: diag.message,
            notes: diag.notes,
            suggestion: diag.suggestion,
        }
    }

    /// The old CLI's text rendering.
    pub fn render(&self) -> String {
        let prefix = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Note => "note",
        };
        let mut out = match &self.file {
            Some(file) if self.line > 0 => {
                format!("{prefix}: {file}:{}: {}", self.line, self.message)
            }
            _ if self.line > 0 => format!("{prefix}: {}: {}", self.line, self.message),
            _ => format!("{prefix}: {}", self.message),
        };
        for note in &self.notes {
            out.push_str(&format!("\n  note: {note}"));
        }
        if let Some(suggestion) = &self.suggestion {
            out.push_str(&format!("\n  try: {suggestion}"));
        }
        out
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DeclStatus {
    Accepted,
    Incomplete,
    TrustedAxiom,
    Failed,
}

#[derive(Clone, Debug, Serialize)]
pub struct Decl {
    pub name: String,
    pub kind: String,
    pub status: DeclStatus,
    pub mode: String,
    pub axioms: Vec<String>,
    pub uses_sorry: bool,
    pub datatypes: Vec<String>,
    pub is_imported: bool,
    pub line: u32,
    pub statement: String,
    /// Tactic names used anywhere in the proof.
    pub tactics: Vec<String>,
}

impl Decl {
    /// `accepted theorem foo (constructive; axioms: set_ext)`.
    pub fn render(&self) -> String {
        match self.status {
            DeclStatus::TrustedAxiom => format!("trusted axiom {}", self.name),
            DeclStatus::Failed => format!("failed {} {}", self.kind, self.name),
            _ => {
                let mut details = vec![self.mode.clone()];
                if self.uses_sorry {
                    details.push("uses sorry".to_string());
                }
                if !self.axioms.is_empty() {
                    details.push(format!("axioms: {}", self.axioms.join(", ")));
                }
                let label = match self.status {
                    DeclStatus::Accepted => "accepted",
                    DeclStatus::Incomplete => "incomplete",
                    DeclStatus::Failed => "failed",
                    DeclStatus::TrustedAxiom => unreachable!(),
                };
                format!(
                    "{label} {} {} ({})",
                    self.kind,
                    self.name,
                    details.join("; ")
                )
            }
        }
    }
}

#[derive(Serialize)]
pub struct JsonReport<'a> {
    pub declarations: &'a [Decl],
    pub diagnostics: &'a [Diag],
    pub policy: Policy,
    pub violations: &'a [String],
    pub ok: bool,
}

/// A goal rendered for display.
#[derive(Clone, Debug, Serialize)]
pub struct GoalView {
    pub vars: Vec<String>,
    pub hyps: Vec<(String, String)>,
    pub target: String,
}

pub struct CheckResult {
    /// Import paths written in the root file, in order.
    pub root_imports: Vec<String>,
    pub decls: Vec<Decl>,
    pub diagnostics: Vec<Diag>,
    pub violations: Vec<String>,
    pub env: Env,
    /// Tactic steps per root theorem, in source order.
    pub steps: BTreeMap<String, (Span, Vec<StepRecord>)>,
    pub root_path: Option<String>,
}

impl CheckResult {
    pub fn has_errors(&self) -> bool {
        self.diagnostics
            .iter()
            .any(|d| d.severity == Severity::Error)
    }

    pub fn ok(&self) -> bool {
        !self.has_errors() && self.violations.is_empty()
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string(&JsonReport {
            declarations: &self.decls,
            diagnostics: &self.diagnostics,
            policy: Policy::default(),
            violations: &self.violations,
            ok: self.ok(),
        })
        .expect("serializable")
    }

    pub fn render_goal(&self, goal: &Goal) -> GoalView {
        GoalView {
            vars: goal
                .vars
                .iter()
                .map(|v| {
                    let (name, ty) = v.as_free().expect("free");
                    format!("{name} : {ty}")
                })
                .collect(),
            hyps: goal
                .hyps
                .iter()
                .map(|(n, t)| (n.to_string(), print_term(&self.env, t)))
                .collect(),
            target: print_term(&self.env, &goal.target),
        }
    }

    /// The goals after the last tactic at or before `line` inside the
    /// theorem containing that line.
    pub fn goals_at(&self, line: u32) -> Option<(String, Vec<GoalView>)> {
        for (name, (span, steps)) in &self.steps {
            if line < span.line || line > span.end_line {
                continue;
            }
            let mut goals: Option<&Vec<Goal>> = steps.first().map(|s| &s.before);
            for step in steps {
                if step.span.line <= line {
                    goals = Some(&step.after);
                }
            }
            let goals = goals
                .map(|gs| gs.iter().map(|g| self.render_goal(g)).collect())
                .unwrap_or_default();
            return Some((name.clone(), goals));
        }
        None
    }
}

/// Collapses `a/b/../c` to `a/c`.
pub fn normalize_path(path: &str) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for part in path.split('/') {
        match part {
            "" | "." => {
                if parts.is_empty() && path.starts_with('/') {
                    parts.push("");
                }
            }
            ".." => {
                if matches!(parts.last(), Some(p) if *p != ".." && !p.is_empty()) {
                    parts.pop();
                } else {
                    parts.push("..");
                }
            }
            other => parts.push(other),
        }
    }
    let joined = parts.join("/");
    if joined.is_empty() {
        ".".to_string()
    } else {
        joined
    }
}

fn directory_of(path: &str) -> String {
    match path.rfind('/') {
        Some(index) => path[..index].to_string(),
        None => ".".to_string(),
    }
}

pub struct Session<'f> {
    fs: &'f dyn FileSystem,
    opts: Options,
    env: Env,
    loaded: BTreeSet<String>,
    decls: Vec<Decl>,
    diagnostics: Vec<Diag>,
    steps: BTreeMap<String, (Span, Vec<StepRecord>)>,
}

impl<'f> Session<'f> {
    pub fn new(fs: &'f dyn FileSystem, opts: Options) -> Session<'f> {
        let env = prelude::base_env();
        Session::with_env(fs, opts, env)
    }

    /// A session over a given environment (used while building the
    /// prelude itself).
    pub fn with_env(fs: &'f dyn FileSystem, opts: Options, mut env: Env) -> Session<'f> {
        if let Some(tier) = opts.tier {
            env.tier = tier;
        }
        Session {
            fs,
            opts,
            env,
            loaded: BTreeSet::new(),
            decls: Vec::new(),
            diagnostics: Vec::new(),
            steps: BTreeMap::new(),
        }
    }

    /// Checks a root source. `path` is used for diagnostics and import
    /// resolution.
    pub fn check(mut self, path: Option<&str>, source: &str) -> CheckResult {
        if let Some(path) = path {
            self.loaded.insert(normalize_path(path));
        }
        let parsed = parse_file(source);
        for error in &parsed.errors {
            self.diagnostics.push(Diag::from_diagnostic(
                Severity::Error,
                path,
                Diagnostic::new(error.span, error.message.clone()),
            ));
        }
        // Leading imports are memoized per thread: the environment after
        // loading the same library files is reused, which keeps re-checks
        // (live editing, speculative hints) fast.
        let leading = parsed
            .file
            .commands
            .iter()
            .take_while(|c| matches!(c, Command::Import { .. }))
            .count();
        let mut cache_key = String::new();
        let mut cacheable = true;
        for command in &parsed.file.commands[..leading] {
            let Command::Import {
                path: import,
                alias,
                ..
            } = command
            else {
                unreachable!();
            };
            match self.resolve_import(path, import) {
                Some((resolved, content)) => {
                    cache_key.push_str(&format!(
                        "{resolved}@{}:{}|",
                        content.len(),
                        alias.as_ref().map(|a| a.name.as_str()).unwrap_or("")
                    ));
                    cache_key.push_str(&hash_hex(&content));
                    cache_key.push(';');
                }
                None => cacheable = false,
            }
        }
        let tier_override = self.opts.tier;
        let cached = if cacheable && leading > 0 {
            IMPORT_CACHE.with(|cell| cell.borrow().get(&cache_key).cloned())
        } else {
            None
        };
        let start = if let Some((env, loaded, decls)) = cached {
            self.env = env;
            self.loaded.extend(loaded);
            self.decls.extend(decls);
            leading
        } else {
            let before = self.diagnostics.len();
            self.check_commands(path, &parsed.file.commands[..leading], false);
            if cacheable && leading > 0 && self.diagnostics.len() == before {
                IMPORT_CACHE.with(|cell| {
                    cell.borrow_mut().insert(
                        cache_key,
                        (self.env.clone(), self.loaded.clone(), self.decls.clone()),
                    );
                });
            }
            leading
        };
        if let Some(tier) = tier_override {
            self.env.tier = tier;
        }
        self.check_commands(path, &parsed.file.commands[start..], false);
        let violations = self.policy_violations();
        let root_imports = parsed
            .file
            .commands
            .iter()
            .filter_map(|c| match c {
                Command::Import { path, .. } => Some(path.clone()),
                _ => None,
            })
            .collect();
        CheckResult {
            root_imports,
            decls: self.decls,
            diagnostics: self.diagnostics,
            violations,
            env: self.env,
            steps: self.steps,
            root_path: path.map(str::to_string),
        }
    }

    fn policy_violations(&self) -> Vec<String> {
        let mut out = Vec::new();
        for decl in &self.decls {
            if decl.is_imported {
                continue;
            }
            if self.opts.policy.deny_sorry && decl.uses_sorry {
                out.push(format!("theorem `{}` uses sorry", decl.name));
            }
            if self.opts.policy.deny_axioms && decl.status == DeclStatus::TrustedAxiom {
                out.push(format!(
                    "axiom `{}` is declared in the root file",
                    decl.name
                ));
            }
            if self.opts.policy.deny_classical && decl.mode == "classical" {
                out.push(format!("theorem `{}` uses classical reasoning", decl.name));
            }
            for tactic in &decl.tactics {
                if self.opts.policy.deny_tactics.iter().any(|t| t == tactic) {
                    out.push(format!(
                        "theorem `{}` uses `{tactic}`, which this assignment does not allow",
                        decl.name
                    ));
                }
            }
        }
        out
    }

    fn resolve_import(&self, from: Option<&str>, import: &str) -> Option<(String, String)> {
        let mut candidates = Vec::new();
        if let Some(from) = from {
            candidates.push(normalize_path(&format!("{}/{import}", directory_of(from))));
        }
        candidates.push(normalize_path(import));
        if let Some(std_dir) = &self.opts.std_dir {
            let mapped: Vec<String> = candidates
                .iter()
                .filter_map(|c| {
                    let index = c.rfind("std/")?;
                    let prefix_ok = index == 0 || c[..index].ends_with('/');
                    prefix_ok.then(|| normalize_path(&format!("{std_dir}/{}", &c[index + 4..])))
                })
                .collect();
            candidates.splice(0..0, mapped);
        }
        for candidate in candidates {
            if let Some(source) = self.fs.read_file(&candidate) {
                return Some((candidate, source));
            }
        }
        None
    }

    /// The environment and diagnostics after checking, for callers that
    /// extend the environment rather than report on a file.
    pub fn into_parts(self) -> (Env, Vec<Diag>) {
        (self.env, self.diagnostics)
    }

    pub(crate) fn check_source(&mut self, path: Option<&str>, source: &str, importing: bool) {
        let parsed = parse_file(source);
        for error in parsed.errors {
            self.diagnostics.push(Diag::from_diagnostic(
                Severity::Error,
                path,
                Diagnostic::new(error.span, error.message),
            ));
        }
        self.check_commands(path, &parsed.file.commands, importing);
    }

    fn check_commands(&mut self, path: Option<&str>, commands: &[Command], importing: bool) {
        for command in commands {
            match command {
                Command::Import {
                    path: import,
                    alias,
                    span,
                } => {
                    self.import(path, import, alias.as_ref().map(|a| a.name.clone()), *span);
                }
                Command::Theorem {
                    name,
                    params,
                    statement,
                    proof,
                    span,
                    header_span,
                } => {
                    self.theorem(
                        path,
                        name,
                        params,
                        statement,
                        proof,
                        *span,
                        *header_span,
                        importing,
                    );
                }
                other => match elab_command(&mut self.env, other) {
                    Ok(names) => {
                        for declared in names {
                            self.record_declaration(other, &declared, importing);
                        }
                    }
                    Err(diag) => {
                        self.diagnostics
                            .push(Diag::from_diagnostic(Severity::Error, path, diag));
                    }
                },
            }
        }
    }

    fn record_declaration(&mut self, command: &Command, name: &Name, importing: bool) {
        if let Command::Axiom { span, .. } = command {
            if let Some(info) = self.env.theorem(name.as_str()) {
                self.decls.push(Decl {
                    name: name.to_string(),
                    kind: "axiom".to_string(),
                    status: DeclStatus::TrustedAxiom,
                    mode: "constructive".to_string(),
                    axioms: vec![name.to_string()],
                    uses_sorry: false,
                    datatypes: vec![],
                    is_imported: importing,
                    line: span.line,
                    statement: print_term(&self.env, &info.statement),
                    tactics: vec![],
                });
            }
        }
    }

    fn import(&mut self, from: Option<&str>, import: &str, alias: Option<String>, span: Span) {
        let Some((resolved, source)) = self.resolve_import(from, import) else {
            self.diagnostics.push(Diag::from_diagnostic(
                Severity::Error,
                from,
                Diagnostic::new(span, format!("cannot find the imported file `{import}`")),
            ));
            return;
        };
        if !self.loaded.insert(resolved.clone()) {
            return;
        }
        let saved_mode = self.env.mode;
        let saved_tier = self.env.tier;
        let saved_importing = self.env.importing;
        self.env.importing = true;
        self.env.mode = Mode::Constructive;
        self.env.tier = Tier::Hol;
        if let Some(alias) = &alias {
            self.env.push_namespace(alias);
        }
        let before = self.diagnostics.len();
        self.check_source(Some(&resolved), &source, true);
        if alias.is_some() {
            self.env.pop_namespace();
        }
        self.env.mode = saved_mode;
        self.env.tier = saved_tier;
        self.env.importing = saved_importing;
        if self.diagnostics.len() > before {
            let count = self.diagnostics.len() - before;
            self.diagnostics.push(Diag::from_diagnostic(
                Severity::Error,
                from,
                Diagnostic::new(
                    span,
                    format!(
                        "the imported file `{resolved}` has {count} error{}",
                        if count == 1 { "" } else { "s" }
                    ),
                ),
            ));
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn theorem(
        &mut self,
        path: Option<&str>,
        name: &hol_syntax::Ident,
        params: &[hol_syntax::Param],
        statement: &hol_syntax::Expr,
        proof: &[hol_syntax::Tactic],
        span: Span,
        header_span: Span,
        importing: bool,
    ) {
        let header = match elab_theorem_header(&self.env, name, params, statement, header_span) {
            Ok(header) => header,
            Err(diag) => {
                self.diagnostics
                    .push(Diag::from_diagnostic(Severity::Error, path, diag));
                return;
            }
        };
        let statement_text = print_term(&self.env, &header.statement);
        match prove(&self.env, &header, proof) {
            Ok(outcome) => {
                for note in outcome.notes {
                    self.diagnostics
                        .push(Diag::from_diagnostic(Severity::Warning, path, note));
                }
                let tags = outcome.thm.tags().clone();
                let status = if tags.sorry {
                    Status::Incomplete
                } else {
                    Status::Accepted
                };
                self.env.add_theorem(TheoremInfo {
                    name: header.name.clone(),
                    params: header.params.clone(),
                    statement: header.statement.clone(),
                    thm: outcome.thm,
                    status,
                    is_imported: importing,
                    span: Some(span),
                });
                self.env.note_declaration(header.name.clone());
                if !importing {
                    self.steps
                        .insert(header.name.to_string(), (span, outcome.steps));
                }
                self.decls.push(Decl {
                    name: header.name.to_string(),
                    kind: "theorem".to_string(),
                    status: if tags.sorry {
                        DeclStatus::Incomplete
                    } else {
                        DeclStatus::Accepted
                    },
                    mode: if tags.classical {
                        "classical"
                    } else {
                        "constructive"
                    }
                    .to_string(),
                    axioms: tags.axioms.iter().map(|a| a.to_string()).collect(),
                    uses_sorry: tags.sorry,
                    datatypes: tags.datatypes.iter().map(|d| d.to_string()).collect(),
                    is_imported: importing,
                    line: span.line,
                    statement: statement_text,
                    tactics: tactic_names(proof),
                });
            }
            Err(failure) => {
                let mut diag = failure.diagnostic;
                diag.message = format!("theorem `{}` failed: {}", name.name, diag.message);
                if let Some(model) = fol::propositional_countermodel(&self.env, &header.statement) {
                    diag = diag.note(format!(
                        "the statement is not a tautology: it is false when {}. No proof can close it; check the statement itself.",
                        model.describe()
                    ));
                } else if let Some(model) =
                    fol::first_order_countermodel(&self.env, &header.statement)
                {
                    diag = diag.note(format!(
                        "the first-order statement is false in this finite world: {}. No proof can close it; check the statement itself.",
                        model.describe()
                    ));
                } else if let Some(model) =
                    arith::arithmetic_countermodel(&self.env, &header.statement)
                {
                    diag = diag.note(format!(
                        "the statement is false when {model}. No proof can close it; check the statement itself."
                    ));
                } else if let Some(goal) = &failure.goal {
                    let hyps = goal.hyp_formulas();
                    let mut formula = goal.target.clone();
                    for hyp in hyps.iter().rev() {
                        if let Ok(next) = hol_kernel::Term::imp(hyp, &formula) {
                            formula = next;
                        }
                    }
                    if let Some(model) = fol::propositional_countermodel(&self.env, &formula) {
                        diag = diag.note(format!(
                            "the open goal does not follow from the current hypotheses: it is false when {}. Reconsider the earlier proof steps.",
                            model.describe()
                        ));
                    } else if let Some(model) = fol::first_order_countermodel(&self.env, &formula) {
                        diag = diag.note(format!(
                            "the open goal does not follow from the current hypotheses in this finite world: {}. Reconsider the earlier proof steps.",
                            model.describe()
                        ));
                    } else {
                        if let Some(model) = arith::arithmetic_countermodel(&self.env, &formula) {
                            diag = diag.note(format!(
                                "the open goal does not follow from the current hypotheses: it is false when {model}. Reconsider the earlier proof steps."
                            ));
                        }
                    }
                }
                self.diagnostics
                    .push(Diag::from_diagnostic(Severity::Error, path, diag));
                for note in failure.notes {
                    self.diagnostics
                        .push(Diag::from_diagnostic(Severity::Warning, path, note));
                }
                if !importing {
                    self.steps
                        .insert(header.name.to_string(), (span, failure.steps));
                }
                // Retain the statement with a hole so later theorems can
                // still be checked; anything depending on it is incomplete.
                if let Ok(thm) = sorry(&header.statement) {
                    self.env.add_theorem(TheoremInfo {
                        name: header.name.clone(),
                        params: header.params.clone(),
                        statement: header.statement.clone(),
                        thm,
                        status: Status::Incomplete,
                        is_imported: importing,
                        span: Some(span),
                    });
                }
                self.decls.push(Decl {
                    name: header.name.to_string(),
                    kind: "theorem".to_string(),
                    status: DeclStatus::Failed,
                    mode: "constructive".to_string(),
                    axioms: vec![],
                    uses_sorry: true,
                    datatypes: vec![],
                    is_imported: importing,
                    line: span.line,
                    statement: statement_text,
                    tactics: tactic_names(proof),
                });
            }
        }
    }
}

/// Distinct tactic names used in a script, including nested blocks.
pub fn tactic_names(tactics: &[hol_syntax::Tactic]) -> Vec<String> {
    use hol_syntax::{HaveProof, TacticKind};
    fn walk(tactics: &[hol_syntax::Tactic], out: &mut BTreeSet<String>) {
        for tactic in tactics {
            let name = match &tactic.kind {
                TacticKind::Intro(_) => "intro",
                TacticKind::Revert(_) => "revert",
                TacticKind::Exact(_) => "exact",
                TacticKind::Trivial => "trivial",
                TacticKind::Assumption => "assumption",
                TacticKind::Apply(_) => "apply",
                TacticKind::Split => "split",
                TacticKind::Left => "left",
                TacticKind::Right => "right",
                TacticKind::Cases { arms, .. } => {
                    for arm in arms {
                        walk(&arm.body, out);
                    }
                    "cases"
                }
                TacticKind::Exists(_) => "exists",
                TacticKind::Refl => "refl",
                TacticKind::Rewrite { .. } => "rewrite",
                TacticKind::Unfold(..) => "unfold",
                TacticKind::Simp { .. } => "simp",
                TacticKind::Induction { arms, .. } => {
                    for arm in arms {
                        walk(&arm.body, out);
                    }
                    "induction"
                }
                TacticKind::Exfalso => "exfalso",
                TacticKind::Contradiction => "contradiction",
                TacticKind::ByCases { .. } => "by_cases",
                TacticKind::ByContra(_) => "by_contra",
                TacticKind::ShowGoal => "show_goal",
                TacticKind::Sorry => "sorry",
                TacticKind::Have { proof, .. } => {
                    if let HaveProof::Block(body) = proof {
                        walk(body, out);
                    }
                    "have"
                }
                TacticKind::Show(_) => "show",
                TacticKind::Funext(_) => "funext",
                TacticKind::Obtain { .. } => "obtain",
                TacticKind::Calc { steps, .. } => {
                    for step in steps {
                        if let hol_syntax::CalcProof::Block(body) = &step.proof {
                            walk(body, out);
                        }
                    }
                    "calc"
                }
            };
            out.insert(name.to_string());
        }
    }
    let mut out = BTreeSet::new();
    walk(tactics, &mut out);
    out.into_iter().collect()
}

type ImportCacheEntry = (Env, BTreeSet<String>, Vec<Decl>);

thread_local! {
    static IMPORT_CACHE: std::cell::RefCell<BTreeMap<String, ImportCacheEntry>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

fn hash_hex(text: &str) -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    text.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

/// Convenience: check a root file from the real file system.
pub fn check_path(path: &str, opts: Options) -> Option<CheckResult> {
    let source = std::fs::read_to_string(path).ok()?;
    let fs = RealFs;
    Some(Session::new(&fs, opts).check(Some(path), &source))
}
