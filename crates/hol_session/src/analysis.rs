//! The browser-facing analysis: one call that returns declarations,
//! diagnostics, per-theorem goal snapshots with explanations, and the
//! theorem library; plus speculative tactic hints for a cursor line.

use serde::Serialize;

use hol_elab::{print_term, Status};
use hol_syntax::{parse_file, Command, Tactic, TacticKind};

use crate::{CheckResult, Decl, Diag, FileSystem, GoalView, Options, Session, Severity};

#[derive(Clone, Debug, Serialize)]
pub struct StepView {
    pub line: u32,
    pub end_line: u32,
    pub text: String,
    pub explanation: String,
    pub after: Vec<GoalView>,
    /// The kernel rules this tactic ran, once the proof is finished:
    /// `imp_intro`, or `and_left ×2` when a rule ran more than once.
    pub rules: Vec<String>,
    /// How many equational and bookkeeping kernel rules ran as well.
    pub equational_rules: u64,
    /// Trust that entered the proof at this step: `classical`, `sorry`,
    /// or `axiom name`.
    pub introduces: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct TheoremView {
    pub name: String,
    pub line: u32,
    pub end_line: u32,
    pub initial: Vec<GoalView>,
    pub steps: Vec<StepView>,
}

#[derive(Clone, Debug, Serialize)]
pub struct LibraryEntry {
    pub name: String,
    pub statement: String,
    pub status: String,
    pub is_imported: bool,
    /// False when the active policy forbids citing this theorem.
    pub allowed: bool,
}

/// The course rules in force, for the UI to show next to the editor.
#[derive(Clone, Debug, Serialize)]
pub struct RulesView {
    /// The section the rules came from, when they came from one.
    pub section: Option<String>,
    /// The only tactics available, when the policy lists them.
    pub tactics_available: Option<Vec<String>>,
    pub tactics_denied: Vec<String>,
    pub restricts_theorems: bool,
    pub deny_sorry: bool,
    pub deny_classical: bool,
    pub advisory: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct Analysis {
    pub ok: bool,
    pub tier: String,
    pub mode: String,
    pub declarations: Vec<Decl>,
    pub diagnostics: Vec<Diag>,
    pub violations: Vec<String>,
    pub theorems: Vec<TheoremView>,
    pub library: Vec<LibraryEntry>,
    pub assignment: Option<crate::AssignmentReport>,
    /// Present when the active policy restricts anything.
    pub rules: Option<RulesView>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Hint {
    pub tactic: String,
    pub description: String,
    pub closes_goal: bool,
}

fn source_lines(source: &str, span_line: u32, end_line: u32) -> String {
    source
        .lines()
        .skip(span_line.saturating_sub(1) as usize)
        .take((end_line.saturating_sub(span_line) + 1) as usize)
        .map(str::trim)
        .collect::<Vec<_>>()
        .join(" ")
}

/// Runs a check and packages everything the UI needs.
pub fn analyze(
    fs: &dyn FileSystem,
    opts: Options,
    path: Option<&str>,
    source: &str,
    manifest: Option<&crate::Manifest>,
) -> Analysis {
    let policy = opts.policy.clone();
    let result = Session::new(fs, opts).check(path, source);
    let assignment = manifest.map(|m| crate::check_manifest(&result, m));
    let rules = policy.has_rules().then(|| RulesView {
        section: policy.section.clone(),
        tactics_available: policy.available_tactics(),
        tactics_denied: policy.deny_tactics.clone(),
        restricts_theorems: policy.restricts_theorems(),
        deny_sorry: policy.deny_sorry,
        deny_classical: policy.deny_classical,
        advisory: policy.advisory,
    });
    let mut theorems = Vec::new();
    for (name, (span, steps)) in &result.steps {
        let initial = steps
            .first()
            .map(|s| s.before.iter().map(|g| result.render_goal(g)).collect())
            .unwrap_or_default();
        let mut views = Vec::new();
        for step in steps {
            let text = source_lines(source, step.span.line, step.span.line);
            let after: Vec<GoalView> = step.after.iter().map(|g| result.render_goal(g)).collect();
            let before: Vec<GoalView> = step.before.iter().map(|g| result.render_goal(g)).collect();
            let explanation = explain_step(&text, &before, &after);
            let kernel = result
                .derivations
                .get(name)
                .map(|derivation| kernel_view(derivation, step.span))
                .unwrap_or_default();
            views.push(StepView {
                line: step.span.line,
                end_line: step.span.end_line,
                text,
                explanation,
                after,
                rules: kernel.rules,
                equational_rules: kernel.equational,
                introduces: kernel.introduces,
            });
        }
        theorems.push(TheoremView {
            name: name.clone(),
            line: span.line,
            end_line: span.end_line,
            initial,
            steps: views,
        });
    }
    theorems.sort_by_key(|t| t.line);
    let library = result
        .env
        .theorems()
        // The prelude's internal computation lemmas are not for browsing.
        .filter(|info| !info.name.as_str().starts_with("Nat."))
        .map(|info| LibraryEntry {
            name: info.name.to_string(),
            statement: print_term(&result.env, &info.statement),
            status: match info.status {
                Status::Accepted => "accepted",
                Status::Incomplete => "incomplete",
                Status::Axiom => "axiom",
            }
            .to_string(),
            is_imported: info.is_imported,
            allowed: !info.is_imported || policy.theorem_problem(info.name.as_str()).is_none(),
        })
        .collect();
    Analysis {
        ok: result.ok(),
        tier: result.env.tier.name().to_string(),
        mode: match result.env.mode {
            hol_syntax::Mode::Constructive => "constructive",
            hol_syntax::Mode::Classical => "classical",
        }
        .to_string(),
        declarations: result.decls,
        diagnostics: result.diagnostics,
        violations: result.violations,
        theorems,
        library,
        assignment,
        rules,
    }
}

/// Kernel rules that only move equations and hypotheses around. They
/// are real rules, but not the ones a logic course teaches by name, so
/// views list them separately from the introduction and elimination
/// rules.
const EQUATIONAL_RULES: &[&str] = &[
    "assume",
    "add_hyp",
    "refl",
    "sym",
    "trans",
    "mk_comb",
    "abs",
    "beta",
    "eta",
    "eq_mp",
    "inst",
    "inst_type",
];

/// What the kernel did for one tactic, for display.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KernelView {
    /// Logical rules, with repeats counted: `imp_intro`, `and_left ×2`.
    pub rules: Vec<String>,
    /// How many equational and bookkeeping rules ran as well.
    pub equational: u64,
    /// Trust that entered the proof here: `classical`, `sorry`,
    /// `axiom name`.
    pub introduces: Vec<String>,
}

/// The kernel's recording for the tactic at `span`.
pub fn kernel_view(
    derivation: &[hol_tactics::DerivationStep],
    span: hol_syntax::Span,
) -> KernelView {
    let mut counts: Vec<(&'static str, u64)> = Vec::new();
    let mut view = KernelView::default();
    for step in derivation.iter().filter(|step| step.span == span) {
        for (rule, times) in step.rules.iter() {
            if EQUATIONAL_RULES.contains(&rule) {
                view.equational += times;
                continue;
            }
            match counts.iter_mut().find(|(name, _)| *name == rule) {
                Some((_, count)) => *count += times,
                None => counts.push((rule, times)),
            }
        }
        if step.introduced.classical {
            view.introduces.push("classical".to_string());
        }
        if step.introduced.sorry {
            view.introduces.push("sorry".to_string());
        }
        for axiom in &step.introduced.axioms {
            view.introduces.push(format!("axiom {axiom}"));
        }
    }
    view.introduces.dedup();
    view.rules = counts
        .into_iter()
        .map(|(rule, count)| {
            if count == 1 {
                rule.to_string()
            } else {
                format!("{rule} ×{count}")
            }
        })
        .collect();
    view
}

/// One sentence about what a tactic did, from the goals before and after.
fn explain_step(text: &str, before: &[GoalView], after: &[GoalView]) -> String {
    let head = text.split_whitespace().next().unwrap_or("");
    let rest = text
        .split_whitespace()
        .skip(1)
        .collect::<Vec<_>>()
        .join(" ");
    let target = before.first().map(|g| g.target.as_str()).unwrap_or("");
    let next = after.first().map(|g| g.target.as_str()).unwrap_or("");
    let closed = after.len() < before.len();
    match head {
        "intro" | "intros" => {
            if let Some(goal) = after.first() {
                if let Some((name, hyp)) = goal
                    .hyps
                    .last()
                    .filter(|(n, _)| rest.split_whitespace().any(|r| r == n))
                {
                    return format!(
                        "Assume `{hyp}` as `{name}`; the goal is now `{}`.",
                        goal.target
                    );
                }
                if let Some(var) = goal.vars.last() {
                    return format!(
                        "Fix an arbitrary `{var}`; the goal is now `{}`.",
                        goal.target
                    );
                }
            }
            format!("Introduce `{rest}`.")
        }
        "exact" => format!("`{rest}` proves `{target}` exactly, so this goal is done."),
        "apply" => {
            if closed {
                format!("`{rest}` proves `{target}` outright.")
            } else {
                let premises: Vec<String> = after
                    .iter()
                    .take(after.len() + 1 - before.len())
                    .map(|g| format!("`{}`", g.target))
                    .collect();
                format!(
                    "To prove `{target}` with `{rest}`, it suffices to prove {}.",
                    premises.join(" and ")
                )
            }
        }
        "split" => {
            let parts: Vec<String> = after
                .iter()
                .take(2)
                .map(|g| format!("`{}`", g.target))
                .collect();
            format!("Prove both parts separately: {}.", parts.join(" and "))
        }
        "left" => format!("Choose the left side of the disjunction and prove `{next}`."),
        "right" => format!("Choose the right side of the disjunction and prove `{next}`."),
        "cases" => format!("Case analysis on `{}`.", rest.trim_end_matches(" with")),
        "obtain" => format!("Unpack `{}` into its parts.", rest),
        "exists" | "use" => format!("Use `{rest}` as the witness; now prove `{next}`."),
        "refl" | "rfl" => {
            "Both sides are equal after computation, so this goal is done.".to_string()
        }
        "rewrite" | "rw" => format!("Rewrite with `{rest}`; the goal becomes `{next}`."),
        "unfold" => format!("Unfold `{rest}`; the goal becomes `{next}`."),
        "simp" => format!("Simplify by computing definitions; the goal becomes `{next}`."),
        "trivial" => "The goal is `True`, which holds outright.".to_string(),
        "assumption" => format!("A hypothesis already states `{target}`."),
        "contradiction" => "The hypotheses are contradictory, so anything follows.".to_string(),
        "exfalso" => "It suffices to derive a contradiction: the goal becomes `False`.".to_string(),
        "by_cases" => format!(
            "Classically, consider both the case where {} holds and the case where it fails.",
            rest.split(':').nth(1).map(str::trim).unwrap_or(&rest)
        ),
        "by_contra" => format!("Suppose `{target}` is false and derive a contradiction."),
        "have" => format!("Establish the intermediate fact `{}`.", rest),
        "show" => format!("Restate the goal as `{rest}`."),
        "sorry" | "admit" => "This goal is left unproved.".to_string(),
        "revert" => format!("Move `{rest}` back into the goal as a premise."),
        _ => format!("The goal becomes `{next}`."),
    }
}

/// Finds the theorem and tactic index at a line: the number of tactics
/// at or before the line, and the indentation to use for an insertion.
fn locate(source: &str, line: u32) -> Option<(String, usize, usize)> {
    let parsed = parse_file(source);
    for command in &parsed.file.commands {
        if let Command::Theorem {
            name, proof, span, ..
        } = command
        {
            if line < span.line || line > span.end_line {
                continue;
            }
            let flat = flatten(proof);
            let mut index = 0;
            let mut indent = 2;
            for (i, tactic) in flat.iter().enumerate() {
                if tactic.span.line <= line {
                    index = i + 1;
                    let text = source
                        .lines()
                        .nth(tactic.span.line as usize - 1)
                        .unwrap_or("");
                    indent = text.chars().take_while(|c| c.is_whitespace()).count();
                }
            }
            return Some((name.name.clone(), index, indent));
        }
    }
    None
}

fn flatten(tactics: &[Tactic]) -> Vec<&Tactic> {
    let mut out = Vec::new();
    for tactic in tactics {
        out.push(tactic);
        match &tactic.kind {
            TacticKind::Cases { arms, .. } | TacticKind::Induction { arms, .. } => {
                for arm in arms {
                    out.extend(flatten(&arm.body));
                }
            }
            TacticKind::Have {
                proof: hol_syntax::HaveProof::Block(body),
                ..
            } => out.extend(flatten(body)),
            _ => {}
        }
    }
    out
}

/// Candidate tactics from the shape of a goal.
fn candidates(goal: &GoalView, result: &CheckResult) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = Vec::new();
    let target = goal.target.as_str();
    let fresh = |base: &str| -> String {
        let taken: Vec<&str> = goal.hyps.iter().map(|(n, _)| n.as_str()).collect();
        let mut name = base.to_string();
        let mut i = 1;
        while taken.contains(&name.as_str())
            || goal
                .vars
                .iter()
                .any(|v| v.starts_with(&format!("{name} :")))
        {
            i += 1;
            name = format!("{base}{i}");
        }
        name
    };
    if target.starts_with("forall ") {
        let var = target
            .trim_start_matches("forall ")
            .split_whitespace()
            .next()
            .unwrap_or("x")
            .to_string();
        out.push((
            format!("intro {}", fresh(&var)),
            "fix an arbitrary element".to_string(),
        ));
    } else if target.contains(" -> ") || target.starts_with("not ") {
        out.push((
            format!("intro {}", fresh("h")),
            "assume the premise".to_string(),
        ));
    }
    out.push(("split".to_string(), "prove both parts".to_string()));
    out.push(("left".to_string(), "prove the left side".to_string()));
    out.push(("right".to_string(), "prove the right side".to_string()));
    out.push((
        "refl".to_string(),
        "both sides compute to the same term".to_string(),
    ));
    out.push(("trivial".to_string(), "the goal holds outright".to_string()));
    out.push((
        "assumption".to_string(),
        "a hypothesis matches the goal".to_string(),
    ));
    out.push((
        "contradiction".to_string(),
        "the hypotheses contradict each other".to_string(),
    ));
    if target.starts_with("exists ") {
        for var in &goal.vars {
            if let Some(name) = var.split(" : ").next() {
                out.push((
                    format!("exists {name}"),
                    format!("use `{name}` as the witness"),
                ));
            }
        }
    }
    for (name, hyp) in &goal.hyps {
        out.push((format!("exact {name}"), format!("`{name}` proves the goal")));
        out.push((
            format!("apply {name}"),
            format!("reduce the goal through `{name}`"),
        ));
        if hyp.contains(" /\\ ") || hyp.contains(" <-> ") {
            out.push((
                format!("exact {name}.left"),
                format!("the left part of `{name}`"),
            ));
            out.push((
                format!("exact {name}.right"),
                format!("the right part of `{name}`"),
            ));
            out.push((
                format!(
                    "cases {name} with\n| intro {} {} =>\n    sorry",
                    fresh("hl"),
                    fresh("hr")
                ),
                format!("split `{name}` into its parts"),
            ));
        }
        if hyp.contains(" \\/ ") {
            out.push((
                format!(
                    "cases {name} with\n| left {} =>\n    sorry\n| right {} =>\n    sorry",
                    fresh("hl"),
                    fresh("hr")
                ),
                format!("case analysis on `{name}`"),
            ));
        }
        if hyp.starts_with("exists ") {
            out.push((
                format!(
                    "cases {name} with\n| intro {} {} =>\n    sorry",
                    fresh("w"),
                    fresh("hw")
                ),
                format!("name the witness in `{name}`"),
            ));
        }
    }
    // Library theorems whose conclusion looks like the goal: cheap textual
    // prefilter on the outermost connective; speculation verifies.
    let goal_head = connective_head(target);
    for info in result.env.theorems() {
        let statement = print_term(&result.env, &info.statement);
        let conclusion = statement.rsplit(" -> ").next().unwrap_or(&statement);
        if connective_head(conclusion) == goal_head && goal_head != "atom" {
            let description = if info.is_imported {
                format!("use the library theorem `{}`", info.name)
            } else {
                format!("use `{}`, proved earlier in this file", info.name)
            };
            out.push((format!("apply {}", info.name), description));
        }
        if out.len() > 40 {
            break;
        }
    }
    out
}

fn connective_head(text: &str) -> &'static str {
    if text.starts_with("forall ") {
        "forall"
    } else if text.starts_with("exists ") {
        "exists"
    } else if text.contains(" <-> ") {
        "iff"
    } else if text.contains(" -> ") {
        "imp"
    } else if text.contains(" \\/ ") {
        "or"
    } else if text.contains(" /\\ ") {
        "and"
    } else if text.contains(" subset ") {
        "subset"
    } else if text.contains(" in ") {
        "mem"
    } else if text.contains(" = ") {
        "eq"
    } else {
        "atom"
    }
}

/// True when two printed formulas are made of the same symbols, so one
/// is at most a rearrangement of the other.
fn same_symbols(a: &str, b: &str) -> bool {
    let sorted = |text: &str| {
        let mut chars: Vec<char> = text.chars().filter(|c| !c.is_whitespace()).collect();
        chars.sort_unstable();
        chars
    };
    sorted(a) == sorted(b)
}

/// Tactic hints for the goal at `line`, verified by running each
/// candidate on the actual proof state: a candidate is offered only if
/// inserting it after the line makes progress without an error.
pub fn hints(
    fs: &dyn FileSystem,
    opts: Options,
    path: Option<&str>,
    source: &str,
    line: u32,
) -> Vec<Hint> {
    let result = Session::new(fs, opts.clone()).check(path, source);
    let Some((theorem, goals)) = result.goals_at(line) else {
        return Vec::new();
    };
    let Some(goal) = goals.first() else {
        return Vec::new();
    };
    let Some((_, _, indent)) = locate(source, line) else {
        return Vec::new();
    };
    let mut hints = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for (tactic, description) in candidates(goal, &result) {
        if !seen.insert(tactic.clone()) {
            continue;
        }
        let padding = " ".repeat(indent);
        let inserted: Vec<String> = tactic.lines().map(|l| format!("{padding}{l}")).collect();
        let mut lines: Vec<String> = source.lines().map(str::to_string).collect();
        let at = (line as usize).min(lines.len());
        for (offset, text) in inserted.iter().enumerate() {
            lines.insert(at + offset, text.clone());
        }
        let candidate_source = lines.join("\n") + "\n";
        let trial = Session::new(fs, opts.clone()).check(path, &candidate_source);
        let first_inserted = line + 1;
        let last_inserted = line + inserted.len() as u32;
        let errors_at_insert = trial.diagnostics.iter().any(|d| {
            d.severity == Severity::Error && d.line >= first_inserted && d.line <= last_inserted
        });
        if errors_at_insert {
            continue;
        }
        // The tactic must have run: the theorem's steps must include it.
        let ran = trial
            .steps
            .get(&theorem)
            .map(|(_, steps)| steps.iter().any(|s| s.span.line == first_inserted))
            .unwrap_or(false);
        if !ran {
            continue;
        }
        let step = trial
            .steps
            .get(&theorem)
            .and_then(|(_, steps)| steps.iter().find(|s| s.span.line == first_inserted));
        // A step that only reorders the goal (commutativity, symmetry) is
        // worth suggesting when the reordered goal is a hypothesis, and
        // is a detour otherwise.
        let detour = step
            .filter(|s| s.after.len() == s.before.len())
            .and_then(|s| s.after.first())
            .map(|g| trial.render_goal(g))
            .is_some_and(|after| {
                after.target != goal.target
                    && same_symbols(&after.target, &goal.target)
                    && !after.hyps.iter().any(|(_, hyp)| *hyp == after.target)
            });
        if detour {
            continue;
        }
        let closes_goal = step
            .map(|s| s.after.len() < s.before.len())
            .unwrap_or(false);
        hints.push(Hint {
            tactic: tactic.clone(),
            description,
            closes_goal,
        });
        if hints.len() >= 8 {
            break;
        }
    }
    hints
}
