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
    let result = Session::new(fs, opts).check(path, source);
    let assignment = manifest.map(|m| crate::check_manifest(&result, m));
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
            views.push(StepView {
                line: step.span.line,
                end_line: step.span.end_line,
                text,
                explanation,
                after,
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
    }
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
            out.push((
                format!("apply {}", info.name),
                format!("use the library theorem `{}`", info.name),
            ));
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
        let closes_goal = trial
            .steps
            .get(&theorem)
            .and_then(|(_, steps)| steps.iter().find(|s| s.span.line == first_inserted))
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
