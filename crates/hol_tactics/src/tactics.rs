//! The tactic interpreter.
//!
//! Each tactic inspects the current goal, produces subgoals, and hands
//! the proof state a justification built from kernel rules. Structured
//! tactics (`cases ... with`, `have ... := by`) run their blocks on the
//! subgoals they create and insist that each block closes exactly its
//! own goal.

use std::collections::BTreeSet;

use hol_elab::{print_term, Diagnostic, Env, Scope, TheoremHeader};
use hol_kernel::{
    and_intro, and_left, and_right, assume, eq_mp, excluded_middle, exists_elim, exists_intro,
    false_elim, forall_elim, forall_intro, iff_intro, iff_left, iff_right, imp_elim, imp_intro,
    or_elim, or_left, or_right, refl, sorry, sym, trans, true_intro, Name, Term, TermView, Thm,
};
use hol_syntax::{
    CaseArm, Expr, HaveProof, Ident, Mode, ProofExpr, RewriteDir, SimpTarget, Span, Tactic,
    TacticKind, Tier,
};

use crate::conv::{head_unfold, normalize, rhs, Rule, Rules};
use crate::pexpr::ProofCtx;
use crate::proof::{Goal, Justification, ProofState};
use crate::unify::{Subst, TermNorm};

pub type Result<T> = std::result::Result<T, Diagnostic>;

/// The goals before and after one tactic, for goal display at a cursor.
#[derive(Clone, Debug)]
pub struct StepRecord {
    pub span: Span,
    pub before: Vec<Goal>,
    pub after: Vec<Goal>,
}

#[derive(Clone, Debug)]
pub struct Outcome {
    pub thm: Thm,
    pub steps: Vec<StepRecord>,
    pub notes: Vec<Diagnostic>,
}

pub struct Failure {
    pub diagnostic: Diagnostic,
    pub steps: Vec<StepRecord>,
    pub notes: Vec<Diagnostic>,
    /// The goal the failing tactic was applied to, or the first
    /// unsolved goal when the script ran out.
    pub goal: Option<Goal>,
}

struct Runner<'a> {
    env: &'a Env,
    base_scope: Scope,
    steps: Vec<StepRecord>,
    notes: Vec<Diagnostic>,
    failing_goal: Option<Goal>,
}

fn kernel(span: Span) -> impl Fn(hol_kernel::KernelError) -> Diagnostic {
    move |e| {
        Diagnostic::new(
            span,
            format!("the kernel rejected this step: {}", e.message),
        )
    }
}

/// Proves a theorem header with a tactic script.
pub fn prove(
    env: &Env,
    header: &TheoremHeader,
    tactics: &[Tactic],
) -> std::result::Result<Outcome, Box<Failure>> {
    let mut runner = Runner {
        env,
        base_scope: header.scope.clone(),
        steps: Vec::new(),
        notes: Vec::new(),
        failing_goal: None,
    };
    let goal = Goal {
        id: 0,
        vars: Vec::new(),
        hyps: header.hyps.clone(),
        target: header.body.clone(),
    };
    let mut state = ProofState::new(goal);
    let mut failing_goal: Option<Goal> = None;
    let result = runner.run_block(&mut state, tactics).and_then(|_| {
        if let Some(goal) = state.current() {
            let remaining = state.open_count();
            let span = tactics.last().map(|t| t.span).unwrap_or(header.span);
            return Err(runner.with_goal(
                Diagnostic::new(
                    span,
                    format!(
                        "the proof is incomplete: {remaining} goal{} remain{}",
                        if remaining == 1 { "" } else { "s" },
                        if remaining == 1 { "s" } else { "" }
                    ),
                ),
                goal,
            ));
        }
        let thm = match state.finish() {
            Ok(thm) => thm,
            Err(_) => {
                return Err(Diagnostic::new(
                    header.span,
                    format!(
                        "the kernel rejected the finished proof: {}",
                        state.last_kernel_error.clone().unwrap_or_default()
                    ),
                ))
            }
        };
        let mut thm = thm;
        for (_, premise) in header.hyps.iter().rev() {
            thm = imp_intro(premise, &thm).map_err(kernel(header.span))?;
        }
        if let Some(extra) = thm.hyps().first() {
            return Err(Diagnostic::new(
                header.span,
                format!(
                    "the finished proof still depends on the assumption `{}`",
                    print_term(env, extra)
                ),
            ));
        }
        if thm.concl() != &header.statement {
            return Err(Diagnostic::new(
                header.span,
                format!(
                    "the proof establishes `{}` rather than the stated `{}`",
                    print_term(env, thm.concl()),
                    print_term(env, &header.statement)
                ),
            ));
        }
        if thm.tags().classical && env.mode == Mode::Constructive {
            return Err(Diagnostic::new(
                header.span,
                "this proof uses classical reasoning, but the file is in constructive mode".to_string(),
            )
            .note("add `mode classical` above the theorem to allow `by_cases`, `by_contra`, and classical theorems such as `em`"));
        }
        Ok(thm)
    });
    match result {
        Ok(thm) => Ok(Outcome {
            thm,
            steps: runner.steps,
            notes: runner.notes,
        }),
        Err(diagnostic) => {
            if failing_goal.is_none() {
                failing_goal = runner
                    .failing_goal
                    .take()
                    .or_else(|| state.current().cloned());
            }
            Err(Box::new(Failure {
                diagnostic,
                steps: runner.steps,
                notes: runner.notes,
                goal: failing_goal,
            }))
        }
    }
}

impl<'a> Runner<'a> {
    fn show(&self, t: &Term) -> String {
        print_term(self.env, t)
    }

    /// Attaches the goal to a diagnostic as notes.
    fn with_goal(&self, mut diag: Diagnostic, goal: &Goal) -> Diagnostic {
        for (name, hyp) in &goal.hyps {
            diag = diag.note(format!("{name} : {}", self.show(hyp)));
        }
        diag.note(format!("target: {}", self.show(&goal.target)))
    }

    fn run_block(&mut self, state: &mut ProofState, tactics: &[Tactic]) -> Result<()> {
        for tactic in tactics {
            let before = state.goals.clone();
            let Some(goal) = state.current().cloned() else {
                return Err(Diagnostic::new(
                    tactic.span,
                    "there are no goals left to prove; remove this tactic".to_string(),
                ));
            };
            if let Err(diag) = self.step(state, &goal, tactic) {
                let diag = if diag.span == Span::default() {
                    diag.with_span(tactic.span)
                } else {
                    diag
                };
                let has_goal_notes = diag.notes.iter().any(|n| n.starts_with("target:"));
                let diag = if has_goal_notes {
                    diag
                } else {
                    self.with_goal(diag, &goal)
                };
                self.steps.push(StepRecord {
                    span: tactic.span,
                    before: before.clone(),
                    after: before,
                });
                if self.failing_goal.is_none() {
                    self.failing_goal = Some(goal.clone());
                }
                return Err(diag);
            }
            self.steps.push(StepRecord {
                span: tactic.span,
                before,
                after: state.goals.clone(),
            });
        }
        Ok(())
    }

    /// Runs a block that must close exactly the goal at the front.
    fn run_block_closing(
        &mut self,
        state: &mut ProofState,
        tactics: &[Tactic],
        what: &str,
        span: Span,
    ) -> Result<()> {
        let goal_id = state.current().map(|g| g.id).expect("a goal to close");
        let expected_after = state.open_count() - 1;
        self.run_block(state, tactics)?;
        if state.is_open(goal_id) || state.open_count() > expected_after {
            let goal = state.current().cloned().expect("open goal");
            let remaining = state.open_count() - expected_after;
            return Err(self.with_goal(
                Diagnostic::new(
                    span,
                    format!(
                        "{what} is not finished: {remaining} goal{} remain{}",
                        if remaining == 1 { "" } else { "s" },
                        if remaining == 1 { "s" } else { "" }
                    ),
                ),
                &goal,
            ));
        }
        if state.open_count() < expected_after {
            return Err(Diagnostic::new(
                span,
                format!("{what} closed its goal and then kept going; move the extra tactics after the block"),
            ));
        }
        Ok(())
    }

    fn ctx<'g>(&self, goal: &'g Goal) -> ProofCtx<'g>
    where
        'a: 'g,
    {
        ProofCtx::new(self.env, &self.base_scope, goal, Subst::new())
    }

    /// `|- target = unfolded`, unfolding definitions at the head.
    fn whnf(&self, goal: &Goal) -> Result<(Thm, Term)> {
        let mut subst = Subst::new();
        let rules = Rules::definitional(self.env, &mut subst);
        let conv = head_unfold(&subst, &rules, &goal.target).map_err(kernel(Span::default()))?;
        let unfolded = rhs(&conv);
        Ok((conv, unfolded))
    }

    fn check_fresh(&self, goal: &Goal, name: &Ident) -> Result<()> {
        if goal.name_in_use(&name.name) || self.base_scope.lookup(&name.name).is_some() {
            return Err(Diagnostic::new(
                name.span,
                format!("the name `{}` is already in use; choose another", name.name),
            ));
        }
        Ok(())
    }

    fn elab_formula(&self, goal: &Goal, expr: &Expr) -> Result<Term> {
        let mut ctx = self.ctx(goal);
        let term = ctx.elab_term(expr, Some(&hol_kernel::Type::prop()))?;
        let unsolved = ctx.subst.unsolved_in(&term);
        if !unsolved.is_empty() {
            return Err(Diagnostic::new(
                expr.span(),
                "could not infer every type in this formula".to_string(),
            ));
        }
        Ok(ctx.subst.apply(&term))
    }

    fn step(&mut self, state: &mut ProofState, goal: &Goal, tactic: &Tactic) -> Result<()> {
        let span = tactic.span;
        match &tactic.kind {
            TacticKind::Intro(names) => {
                for name in names {
                    let current = state.current().cloned().expect("goal");
                    self.intro(state, &current, name)?;
                }
                Ok(())
            }
            TacticKind::Revert(name) => self.revert(state, goal, name),
            TacticKind::Exact(expr) => self.exact(state, goal, expr, span),
            TacticKind::Apply(expr) => self.apply(state, goal, expr, span),
            TacticKind::Trivial => self.trivial(state, goal, span),
            TacticKind::Assumption => self.assumption(state, goal, span),
            TacticKind::Split => self.split(state, goal, span),
            TacticKind::Left => self.left_right(state, goal, true, span),
            TacticKind::Right => self.left_right(state, goal, false, span),
            TacticKind::Cases { scrutinee, arms } => self.cases(state, goal, scrutinee, arms, span),
            TacticKind::Exists(witness) => self.exists(state, goal, witness, span),
            TacticKind::Refl => self.refl(state, goal, span),
            TacticKind::Rewrite {
                dir,
                all,
                proof,
                at,
            } => self.rewrite(state, goal, *dir, *all, proof, at.as_ref(), span),
            TacticKind::Unfold(name, at) => self.unfold(state, goal, name, at.as_ref(), span),
            TacticKind::Simp { rules, target } => self.simp(state, goal, rules, target, span),
            TacticKind::Induction { .. } => {
                let message = if self.env.tier < Tier::FolNat {
                    "induction needs natural numbers or data types; add `logic fol_nat` or `logic hol`"
                } else {
                    "induction is not available yet in this build"
                };
                Err(Diagnostic::new(span, message.to_string()))
            }
            TacticKind::Exfalso => {
                let target = goal.target.clone();
                let subgoal = Goal {
                    target: Term::false_(),
                    ..goal.clone()
                };
                state.close(
                    goal.id,
                    vec![subgoal],
                    Box::new(move |thms| false_elim(&thms[0], &target)),
                );
                Ok(())
            }
            TacticKind::Contradiction => self.contradiction(state, goal, span),
            TacticKind::ByCases { name, prop } => self.by_cases(state, goal, name, prop, span),
            TacticKind::ByContra(name) => self.by_contra(state, goal, name, span),
            TacticKind::ShowGoal => Err(self.with_goal(
                Diagnostic::new(
                    span,
                    "show_goal: the proof stops here so you can read the goal".to_string(),
                ),
                goal,
            )),
            TacticKind::Sorry => {
                let thm = sorry(&goal.target).map_err(kernel(span))?;
                state.close(goal.id, vec![], Box::new(move |_| Ok(thm.clone())));
                Ok(())
            }
            TacticKind::Have {
                name,
                stated,
                proof,
            } => self.have(state, goal, name, stated.as_ref(), proof, span),
            TacticKind::Show(expr) => self.show_tactic(state, goal, expr, span),
            TacticKind::Obtain { names, proof } => self.obtain(state, goal, names, proof, span),
        }
    }

    // ---- individual tactics ----

    fn intro(&mut self, state: &mut ProofState, goal: &Goal, name: &Ident) -> Result<()> {
        self.check_fresh(goal, name)?;
        let (conv, unfolded) = self.whnf(goal)?;
        if let Some((premise, conclusion)) = unfolded.dest_imp() {
            let premise = premise.clone();
            let subgoal = Goal {
                hyps: {
                    let mut hyps = goal.hyps.clone();
                    hyps.push((Name::new(&name.name), premise.clone()));
                    hyps
                },
                target: conclusion.clone(),
                ..goal.clone()
            };
            let just: Justification = Box::new(move |thms| {
                let discharged = imp_intro(&premise, &thms[0])?;
                eq_mp(&sym(&conv)?, &discharged)
            });
            state.close(goal.id, vec![subgoal], just);
            return Ok(());
        }
        if let Some(pred) = unfolded.dest_forall() {
            let TermView::Lam(_, ty, _) = pred.view() else {
                unreachable!();
            };
            if goal.taken_names().contains(&Name::new(&name.name)) {
                return Err(Diagnostic::new(
                    name.span,
                    format!(
                        "the name `{}` already occurs in the goal; choose another",
                        name.name
                    ),
                ));
            }
            let var = Term::free(name.name.as_str(), ty.clone());
            let body = pred.beta_apply(&var).map_err(kernel(name.span))?;
            let subgoal = Goal {
                vars: {
                    let mut vars = goal.vars.clone();
                    vars.push(var.clone());
                    vars
                },
                target: body,
                ..goal.clone()
            };
            let just: Justification = Box::new(move |thms| {
                let generalized = forall_intro(&var, &thms[0])?;
                eq_mp(&sym(&conv)?, &generalized)
            });
            state.close(goal.id, vec![subgoal], just);
            return Ok(());
        }
        let mut diag = Diagnostic::new(
            name.span,
            format!(
                "`intro` needs an implication or a universal statement as the goal, but the goal is `{}`",
                self.show(&goal.target)
            ),
        );
        if unfolded.dest_and().is_some() {
            diag = diag.suggest("split");
        } else if unfolded.dest_or().is_some() {
            diag = diag.note("for a disjunction, choose a side with `left` or `right`");
        } else if unfolded.dest_exists().is_some() {
            diag = diag.note("for an existential, give a witness with `exists t`");
        }
        Err(diag)
    }

    fn revert(&mut self, state: &mut ProofState, goal: &Goal, name: &Ident) -> Result<()> {
        let Some(position) = goal.hyps.iter().rposition(|(n, _)| n.as_str() == name.name) else {
            return Err(Diagnostic::new(
                name.span,
                format!("no hypothesis named `{}`", name.name),
            ));
        };
        let (_, premise) = goal.hyps[position].clone();
        let mut hyps = goal.hyps.clone();
        hyps.remove(position);
        let target = Term::imp(&premise, &goal.target).map_err(kernel(name.span))?;
        let subgoal = Goal {
            hyps,
            target,
            ..goal.clone()
        };
        let just: Justification = Box::new(move |thms| imp_elim(&thms[0], &assume(&premise)?));
        state.close(goal.id, vec![subgoal], just);
        Ok(())
    }

    fn exact(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        expr: &ProofExpr,
        span: Span,
    ) -> Result<()> {
        let mut ctx = self.ctx(goal);
        let thm = ctx.elab_proof(expr)?;
        let thm = ctx.coerce(thm, &goal.target, span)?;
        let thm = ctx.finalize(&thm, span, "the theorem")?;
        state.close(goal.id, vec![], Box::new(move |_| Ok(thm.clone())));
        Ok(())
    }

    fn apply(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        expr: &ProofExpr,
        span: Span,
    ) -> Result<()> {
        let mut ctx = self.ctx(goal);
        let original = ctx.elab_proof(expr)?;
        let target = goal.target.clone();

        // Explore the statement with placeholder proofs, recording how to
        // rebuild it once the metavariables are known.
        #[derive(Clone)]
        enum Step {
            Premise(Term),
            Forall(Term),
            Unfold,
        }
        let mut best: Option<(Subst, Vec<Step>)> = None;
        for use_norm in [false, true] {
            let mut thm = original.clone();
            let mut plan: Vec<Step> = Vec::new();
            for _ in 0..40 {
                let concl = ctx.subst.apply(thm.concl());
                let mut trial = ctx.subst.clone();
                let matched = if use_norm {
                    let (nc, _) = normalize(&trial, &ctx.rules, &concl).map_err(kernel(span))?;
                    let (nt, _) = normalize(&trial, &ctx.rules, &target).map_err(kernel(span))?;
                    trial.unify(&rhs(&nc), &rhs(&nt))
                } else {
                    trial.unify(&concl, &target)
                };
                if matched {
                    best = Some((trial, plan));
                    break;
                }
                if let Some(pred) = concl.dest_forall() {
                    let TermView::Lam(binder, ty, _) = pred.view() else {
                        unreachable!();
                    };
                    let meta = ctx
                        .subst
                        .fresh_meta(binder.as_str(), ctx.subst.apply_type(ty));
                    thm = forall_elim(&ctx.subst.apply_thm(&thm).map_err(kernel(span))?, &meta)
                        .map_err(kernel(span))?;
                    plan.push(Step::Forall(meta));
                    continue;
                }
                if let Some((premise, _)) = concl.dest_imp() {
                    let premise = premise.clone();
                    let placeholder = assume(&premise).map_err(kernel(span))?;
                    thm = imp_elim(
                        &ctx.subst.apply_thm(&thm).map_err(kernel(span))?,
                        &placeholder,
                    )
                    .map_err(kernel(span))?;
                    plan.push(Step::Premise(premise));
                    continue;
                }
                let unfolded = head_unfold(&ctx.subst, &ctx.rules, &concl).map_err(kernel(span))?;
                if rhs(&unfolded) == concl {
                    break;
                }
                thm = eq_mp(&unfolded, &ctx.subst.apply_thm(&thm).map_err(kernel(span))?)
                    .map_err(kernel(span))?;
                plan.push(Step::Unfold);
            }
            if best.is_some() {
                break;
            }
        }
        let Some((subst, plan)) = best else {
            let concl = ctx.subst.apply(original.concl());
            let mut diag = Diagnostic::new(
                span,
                format!(
                    "cannot apply this: its conclusion does not match the goal `{}`",
                    self.show(&target)
                ),
            );
            diag = diag.note(format!("it proves: {}", ctx.show(&concl)));
            return Err(diag);
        };
        ctx.subst = subst;

        // Premises that still mention metavariables may be pinned down by a
        // hypothesis that matches exactly one of them.
        let premises: Vec<Term> = plan
            .iter()
            .filter_map(|s| match s {
                Step::Premise(p) => Some(p.clone()),
                _ => None,
            })
            .collect();
        for premise in &premises {
            if ctx.subst.unsolved_in(premise).is_empty() {
                continue;
            }
            let mut candidates: Vec<Subst> = Vec::new();
            for formula in hypothesis_consequences(goal) {
                let mut trial = ctx.subst.clone();
                if trial.unify(premise, &formula) {
                    candidates.push(trial);
                }
            }
            if candidates.len() == 1 {
                ctx.subst = candidates.remove(0);
            }
        }

        let instantiated = ctx.finalize(&original, span, "the theorem")?;
        // Rebuild the premises from the instantiated statement.
        let mut walker = instantiated.clone();
        let mut subgoals = Vec::new();
        for step in &plan {
            match step {
                Step::Forall(meta) => {
                    let value = ctx.subst.apply(meta);
                    walker = forall_elim(&walker, &value).map_err(kernel(span))?;
                }
                Step::Premise(_) => {
                    let (premise, _) = walker
                        .concl()
                        .dest_imp()
                        .map(|(a, b)| (a.clone(), b.clone()))
                        .expect("premise step");
                    subgoals.push(Goal {
                        target: premise.clone(),
                        ..goal.clone()
                    });
                    walker = imp_elim(&walker, &assume(&premise).map_err(kernel(span))?)
                        .map_err(kernel(span))?;
                }
                Step::Unfold => {
                    let conv = head_unfold(&ctx.subst, &ctx.rules, walker.concl())
                        .map_err(kernel(span))?;
                    walker = eq_mp(&conv, &walker).map_err(kernel(span))?;
                }
            }
        }
        for subgoal in &subgoals {
            let unsolved = ctx.subst.unsolved_in(&subgoal.target);
            if let Some((name, _)) = unsolved.first() {
                let display = crate::unify::meta_display_name(name);
                return Err(Diagnostic::new(
                    span,
                    format!("could not determine `{display}` from the goal or the hypotheses"),
                )
                .suggest(format!("apply ... {{{display} := ...}}")));
            }
        }
        let subst = ctx.subst.clone();
        let rules = ctx.rules.clone();
        let plan_for_just = plan.clone();
        let just: Justification = Box::new(move |thms| {
            let mut current = instantiated.clone();
            let mut proofs = thms.iter();
            for step in &plan_for_just {
                match step {
                    Step::Forall(meta) => {
                        current = forall_elim(&current, &subst.apply(meta))?;
                    }
                    Step::Premise(_) => {
                        let proof = proofs.next().expect("one proof per premise");
                        current = imp_elim(&current, proof)?;
                    }
                    Step::Unfold => {
                        let conv = head_unfold(&subst, &rules, current.concl())?;
                        current = eq_mp(&conv, &current)?;
                    }
                }
            }
            bridge(&subst, &rules, current, &target)
        });
        state.close(goal.id, subgoals, just);
        Ok(())
    }

    fn trivial(&mut self, state: &mut ProofState, goal: &Goal, span: Span) -> Result<()> {
        let ctx = self.ctx(goal);
        let conv = ctx.norm(&goal.target).map_err(kernel(span))?;
        let normalized = rhs(&conv);
        if normalized.is_true() {
            let just: Justification = Box::new(move |_| eq_mp(&sym(&conv)?, &true_intro()));
            state.close(goal.id, vec![], just);
            return Ok(());
        }
        if let Some((a, b)) = normalized.dest_eq() {
            if a == b {
                let a = a.clone();
                let just: Justification = Box::new(move |_| eq_mp(&sym(&conv)?, &refl(&a)?));
                state.close(goal.id, vec![], just);
                return Ok(());
            }
        }
        Err(Diagnostic::new(
            span,
            format!(
                "`trivial` proves `True`, but the goal is `{}`",
                self.show(&goal.target)
            ),
        ))
    }

    fn assumption(&mut self, state: &mut ProofState, goal: &Goal, span: Span) -> Result<()> {
        let ctx = self.ctx(goal);
        let nt = ctx.norm(&goal.target).map_err(kernel(span))?;
        for (_, hyp) in &goal.hyps {
            if hyp == &goal.target {
                let thm = assume(hyp).map_err(kernel(span))?;
                state.close(goal.id, vec![], Box::new(move |_| Ok(thm.clone())));
                return Ok(());
            }
            let nh = ctx.norm(hyp).map_err(kernel(span))?;
            if rhs(&nh) == rhs(&nt) {
                let thm = assume(hyp).map_err(kernel(span))?;
                let bridge = trans(&nh, &sym(&nt).map_err(kernel(span))?).map_err(kernel(span))?;
                let thm = eq_mp(&bridge, &thm).map_err(kernel(span))?;
                state.close(goal.id, vec![], Box::new(move |_| Ok(thm.clone())));
                return Ok(());
            }
        }
        Err(Diagnostic::new(
            span,
            "no matching assumption found".to_string(),
        ))
    }

    fn split(&mut self, state: &mut ProofState, goal: &Goal, span: Span) -> Result<()> {
        let (conv, unfolded) = self.whnf(goal)?;
        if let Some((a, b)) = unfolded.dest_and() {
            let left = Goal {
                target: a.clone(),
                ..goal.clone()
            };
            let right = Goal {
                target: b.clone(),
                ..goal.clone()
            };
            let just: Justification =
                Box::new(move |thms| eq_mp(&sym(&conv)?, &and_intro(&thms[0], &thms[1])?));
            state.close(goal.id, vec![left, right], just);
            return Ok(());
        }
        if let Some((a, b)) = unfolded.dest_iff() {
            let forward = Goal {
                target: Term::imp(a, b).map_err(kernel(span))?,
                ..goal.clone()
            };
            let backward = Goal {
                target: Term::imp(b, a).map_err(kernel(span))?,
                ..goal.clone()
            };
            let just: Justification =
                Box::new(move |thms| eq_mp(&sym(&conv)?, &iff_intro(&thms[0], &thms[1])?));
            state.close(goal.id, vec![forward, backward], just);
            return Ok(());
        }
        Err(Diagnostic::new(
            span,
            format!(
                "`split` needs a conjunction or biconditional as the goal, but the goal is `{}`",
                self.show(&goal.target)
            ),
        ))
    }

    fn left_right(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        left: bool,
        span: Span,
    ) -> Result<()> {
        let (conv, unfolded) = self.whnf(goal)?;
        let Some((a, b)) = unfolded.dest_or() else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "`{}` needs a disjunction as the goal, but the goal is `{}`",
                    if left { "left" } else { "right" },
                    self.show(&goal.target)
                ),
            ));
        };
        let (a, b) = (a.clone(), b.clone());
        let subgoal = Goal {
            target: if left { a.clone() } else { b.clone() },
            ..goal.clone()
        };
        let just: Justification = Box::new(move |thms| {
            let disj = if left {
                or_left(&thms[0], &b)?
            } else {
                or_right(&a, &thms[0])?
            };
            eq_mp(&sym(&conv)?, &disj)
        });
        state.close(goal.id, vec![subgoal], just);
        Ok(())
    }

    /// Destructures a proof of a disjunction, existential, conjunction,
    /// or biconditional. Returns the subgoals in arm order and the
    /// justification.
    fn destructure(
        &self,
        goal: &Goal,
        thm: Thm,
        arms: &[(String, Vec<Ident>)],
        span: Span,
    ) -> Result<(Vec<Goal>, Justification)> {
        let mut subst = Subst::new();
        let rules = Rules::definitional(self.env, &mut subst);
        let conv = head_unfold(&subst, &rules, thm.concl()).map_err(kernel(span))?;
        let concl = rhs(&conv);
        let thm = eq_mp(&conv, &thm).map_err(kernel(span))?;
        let arm_names: Vec<&str> = arms.iter().map(|(n, _)| n.as_str()).collect();
        let fresh = |name: &Ident| -> Result<()> {
            self.check_fresh(goal, name)?;
            if goal.taken_names().contains(&Name::new(&name.name)) {
                return Err(Diagnostic::new(
                    name.span,
                    format!(
                        "the name `{}` already occurs in the goal; choose another",
                        name.name
                    ),
                ));
            }
            Ok(())
        };
        if let Some((a, b)) = concl.dest_or() {
            let ok_shape = arm_names == ["left", "right"] || arm_names == ["inl", "inr"];
            if !ok_shape || arms.iter().any(|(_, b)| b.len() != 1) {
                return Err(Diagnostic::new(
                    span,
                    "a disjunction has two cases: `| left h => ...` and `| right h => ...`"
                        .to_string(),
                ));
            }
            fresh(&arms[0].1[0])?;
            fresh(&arms[1].1[0])?;
            let (a, b) = (a.clone(), b.clone());
            let mut left_hyps = goal.hyps.clone();
            left_hyps.push((Name::new(&arms[0].1[0].name), a.clone()));
            let mut right_hyps = goal.hyps.clone();
            right_hyps.push((Name::new(&arms[1].1[0].name), b.clone()));
            let left = Goal {
                hyps: left_hyps,
                ..goal.clone()
            };
            let right = Goal {
                hyps: right_hyps,
                ..goal.clone()
            };
            let just: Justification = Box::new(move |thms| or_elim(&thm, &thms[0], &thms[1]));
            return Ok((vec![left, right], just));
        }
        if let Some(pred) = concl.dest_exists() {
            if arms.len() != 1 || arms[0].1.len() != 2 {
                return Err(Diagnostic::new(
                    span,
                    "an existential has one case naming the witness and its property: `| intro x hx => ...`".to_string(),
                ));
            }
            let (var_name, hyp_name) = (&arms[0].1[0], &arms[0].1[1]);
            fresh(var_name)?;
            fresh(hyp_name)?;
            if var_name.name == hyp_name.name {
                return Err(Diagnostic::new(
                    hyp_name.span,
                    "the two names must differ".to_string(),
                ));
            }
            let TermView::Lam(_, ty, _) = pred.view() else {
                unreachable!();
            };
            let var = Term::free(var_name.name.as_str(), ty.clone());
            let property = pred.beta_apply(&var).map_err(kernel(span))?;
            let mut vars = goal.vars.clone();
            vars.push(var.clone());
            let mut hyps = goal.hyps.clone();
            hyps.push((Name::new(&hyp_name.name), property));
            let subgoal = Goal {
                vars,
                hyps,
                ..goal.clone()
            };
            let just: Justification = Box::new(move |thms| exists_elim(&thm, &var, &thms[0]));
            return Ok((vec![subgoal], just));
        }
        if concl.dest_and().is_some() || concl.dest_iff().is_some() {
            if arms.len() != 1 || arms[0].1.len() != 2 {
                return Err(Diagnostic::new(
                    span,
                    "a conjunction has one case naming both halves: `| intro hp hq => ...`"
                        .to_string(),
                ));
            }
            let (left_name, right_name) = (&arms[0].1[0], &arms[0].1[1]);
            fresh(left_name)?;
            fresh(right_name)?;
            if left_name.name == right_name.name {
                return Err(Diagnostic::new(
                    right_name.span,
                    "the two names must differ".to_string(),
                ));
            }
            let is_and = concl.dest_and().is_some();
            let (left_thm, right_thm) = if is_and {
                (
                    and_left(&thm).map_err(kernel(span))?,
                    and_right(&thm).map_err(kernel(span))?,
                )
            } else {
                (
                    iff_left(&thm).map_err(kernel(span))?,
                    iff_right(&thm).map_err(kernel(span))?,
                )
            };
            let (a, b) = (left_thm.concl().clone(), right_thm.concl().clone());
            let mut hyps = goal.hyps.clone();
            hyps.push((Name::new(&left_name.name), a.clone()));
            hyps.push((Name::new(&right_name.name), b.clone()));
            let subgoal = Goal {
                hyps,
                ..goal.clone()
            };
            let just: Justification = Box::new(move |thms| {
                let discharged = imp_intro(&a, &imp_intro(&b, &thms[0])?)?;
                imp_elim(&imp_elim(&discharged, &left_thm)?, &right_thm)
            });
            return Ok((vec![subgoal], just));
        }
        Err(Diagnostic::new(
            span,
            format!(
                "`cases` needs a disjunction, existential, or conjunction, but this proves `{}`",
                self.show(&concl)
            ),
        ))
    }

    fn cases(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        scrutinee: &ProofExpr,
        arms: &[CaseArm],
        span: Span,
    ) -> Result<()> {
        let mut ctx = self.ctx(goal);
        let thm = ctx.elab_proof(scrutinee)?;
        let thm = ctx.finalize(&thm, span, "the hypothesis")?;
        let arm_specs: Vec<(String, Vec<Ident>)> = arms
            .iter()
            .map(|arm| (arm.ctor.name.clone(), arm.binders.clone()))
            .collect();
        let (subgoals, just) = self.destructure(goal, thm, &arm_specs, span)?;
        state.close(goal.id, subgoals, just);
        for arm in arms {
            let what = format!("case `{}`", arm.ctor.name);
            self.run_block_closing(state, &arm.body, &what, arm.span)?;
        }
        Ok(())
    }

    fn obtain(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        names: &[Ident],
        proof: &ProofExpr,
        span: Span,
    ) -> Result<()> {
        let mut ctx = self.ctx(goal);
        let thm = ctx.elab_proof(proof)?;
        let thm = ctx.finalize(&thm, span, "the hypothesis")?;
        if names.len() != 2 {
            return Err(Diagnostic::new(span, "`obtain` names a witness and its property, or the two halves of a conjunction: `obtain x hx := h`".to_string()));
        }
        let (subgoals, just) =
            self.destructure(goal, thm, &[("intro".to_string(), names.to_vec())], span)?;
        state.close(goal.id, subgoals, just);
        Ok(())
    }

    fn exists(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        witness: &Expr,
        span: Span,
    ) -> Result<()> {
        let (conv, unfolded) = self.whnf(goal)?;
        let Some(pred) = unfolded.dest_exists() else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "`exists` needs an existential goal, but the goal is `{}`",
                    self.show(&goal.target)
                ),
            ));
        };
        let TermView::Lam(_, ty, _) = pred.view() else {
            unreachable!();
        };
        let mut ctx = self.ctx(goal);
        let term = ctx.elab_term(witness, Some(ty)).map_err(|d| {
            if d.message.contains("was expected here") {
                Diagnostic::new(witness.span(), format!("witness {}", d.message))
            } else {
                d
            }
        })?;
        if !ctx.subst.unsolved_in(&term).is_empty() {
            return Err(Diagnostic::new(
                witness.span(),
                "could not infer the witness's type".to_string(),
            ));
        }
        let term = ctx.subst.apply(&term);
        let instance = pred.beta_apply(&term).map_err(kernel(span))?;
        let subgoal = Goal {
            target: instance,
            ..goal.clone()
        };
        let unfolded = unfolded.clone();
        let just: Justification = Box::new(move |thms| {
            let ex = exists_intro(&unfolded, &term, &thms[0])?;
            eq_mp(&sym(&conv)?, &ex)
        });
        state.close(goal.id, vec![subgoal], just);
        Ok(())
    }

    fn refl(&mut self, state: &mut ProofState, goal: &Goal, span: Span) -> Result<()> {
        let ctx = self.ctx(goal);
        let conv = ctx.norm(&goal.target).map_err(kernel(span))?;
        let normalized = rhs(&conv);
        let Some((a, b)) = normalized.dest_eq() else {
            return Err(Diagnostic::new(
                span,
                format!(
                    "`refl` needs an equality as the goal, but the goal is `{}`",
                    self.show(&goal.target)
                ),
            ));
        };
        if a != b {
            let (a, b) = (a.clone(), b.clone());
            return Err(Diagnostic::new(
                span,
                format!(
                    "`refl` failed: after computation the two sides are `{}` and `{}`, which differ",
                    self.show(&a),
                    self.show(&b)
                ),
            ));
        }
        let a = a.clone();
        let just: Justification = Box::new(move |_| eq_mp(&sym(&conv)?, &refl(&a)?));
        state.close(goal.id, vec![], just);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn rewrite(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        dir: RewriteDir,
        all: bool,
        proof: &ProofExpr,
        at: Option<&Ident>,
        span: Span,
    ) -> Result<()> {
        let mut ctx = self.ctx(goal);
        let thm = ctx.elab_proof(proof)?;
        // Strip quantifiers with metavariables and orient the equation.
        let mut equation = thm;
        for _ in 0..20 {
            let concl = ctx.subst.apply(equation.concl());
            if let Some(pred) = concl.dest_forall() {
                let TermView::Lam(binder, ty, _) = pred.view() else {
                    unreachable!();
                };
                let meta = ctx
                    .subst
                    .fresh_meta(binder.as_str(), ctx.subst.apply_type(ty));
                equation = forall_elim(
                    &ctx.subst.apply_thm(&equation).map_err(kernel(span))?,
                    &meta,
                )
                .map_err(kernel(span))?;
                continue;
            }
            break;
        }
        let concl = ctx.subst.apply(equation.concl());
        if concl.dest_eq().is_none() {
            return Err(Diagnostic::new(
                span,
                format!(
                    "`rewrite` needs an equation, but this proves `{}`",
                    ctx.show(&concl)
                ),
            ));
        }
        let equation = match dir {
            RewriteDir::LeftToRight => equation,
            RewriteDir::RightToLeft => sym(&equation).map_err(kernel(span))?,
        };
        let rule = Rule {
            name: "rewrite".to_string(),
            lhs: ctx
                .subst
                .apply(equation.concl())
                .dest_eq()
                .unwrap()
                .0
                .clone(),
            thm: equation.clone(),
        };
        let (subject, hyp_index) = match at {
            None => (goal.target.clone(), None),
            Some(name) => {
                let Some(position) = goal.hyps.iter().rposition(|(n, _)| n.as_str() == name.name)
                else {
                    return Err(Diagnostic::new(
                        name.span,
                        format!("no hypothesis named `{}`", name.name),
                    ));
                };
                (goal.hyps[position].1.clone(), Some(position))
            }
        };
        let (conv, count) = rewrite_occurrences(&mut ctx.subst, &rule, &subject, all, span)?;
        let Some(conv) = conv else {
            let (l, r) = ctx
                .subst
                .apply(equation.concl())
                .dest_eq()
                .map(|(a, b)| (a.clone(), b.clone()))
                .unwrap();
            let mut diag = Diagnostic::new(
                span,
                format!(
                    "no occurrence of `{}` to rewrite in {}",
                    ctx.show(&l),
                    if at.is_some() {
                        "the hypothesis"
                    } else {
                        "the goal"
                    }
                ),
            );
            let reverse = Rule {
                name: "reverse".to_string(),
                lhs: r.clone(),
                thm: sym(&equation).map_err(kernel(span))?,
            };
            let mut probe = ctx.subst.clone();
            if rewrite_occurrences(&mut probe, &reverse, &subject, false, span)?
                .0
                .is_some()
            {
                let other = match dir {
                    RewriteDir::LeftToRight => "<-",
                    RewriteDir::RightToLeft => "->",
                };
                diag = diag.note(format!(
                    "`{}` does occur; rewrite in the other direction with `rewrite {other} ...`",
                    ctx.show(&r)
                ));
            }
            return Err(diag);
        };
        if count > 1 && !all {
            let (l, _) = ctx
                .subst
                .apply(equation.concl())
                .dest_eq()
                .map(|(a, b)| (a.clone(), b.clone()))
                .unwrap();
            self.notes.push(Diagnostic::new(
                span,
                format!(
                    "rewrote the 1st of {count} occurrences of `{}`; use `rewrite all` to rewrite every occurrence",
                    ctx.show(&l)
                ),
            ));
        }
        let _ = ctx.finalize(&equation, span, "the equation")?;
        self.replace_with_conv(state, goal, conv, hyp_index, span)
    }

    /// Replaces the goal target (or a hypothesis) using `|- old = new`.
    fn replace_with_conv(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        conv: Thm,
        hyp_index: Option<usize>,
        span: Span,
    ) -> Result<()> {
        let new_term = rhs(&conv);
        match hyp_index {
            None => {
                let subgoal = Goal {
                    target: new_term,
                    ..goal.clone()
                };
                let just: Justification = Box::new(move |thms| eq_mp(&sym(&conv)?, &thms[0]));
                state.close(goal.id, vec![subgoal], just);
            }
            Some(position) => {
                let old_hyp = goal.hyps[position].1.clone();
                let mut hyps = goal.hyps.clone();
                hyps[position].1 = new_term.clone();
                let subgoal = Goal {
                    hyps,
                    ..goal.clone()
                };
                let just: Justification = Box::new(move |thms| {
                    let discharged = imp_intro(&new_term, &thms[0])?;
                    let converted = eq_mp(&conv, &assume(&old_hyp)?)?;
                    imp_elim(&discharged, &converted)
                });
                state.close(goal.id, vec![subgoal], just);
            }
        }
        let _ = span;
        Ok(())
    }

    fn unfold(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        name: &Ident,
        at: Option<&Ident>,
        span: Span,
    ) -> Result<()> {
        let mut subst = Subst::new();
        let qualified = match self.env.def(&name.name) {
            Some(def) => def.name.clone(),
            None => match self.env.constant(&name.name) {
                Some(info) if self.env.equations(&info.name).is_some() => info.name.clone(),
                Some(info) => {
                    return Err(Diagnostic::new(
                        name.span,
                        format!(
                            "`{}` is a {}, not a definition; there is nothing to unfold",
                            name.name,
                            info.kind.describe()
                        ),
                    ))
                }
                None => {
                    return Err(Diagnostic::new(
                        name.span,
                        format!("unknown definition `{}`", name.name),
                    ))
                }
            },
        };
        let rules = Rules::for_def(self.env, &mut subst, &qualified);
        let (subject, hyp_index) = match at {
            None => (goal.target.clone(), None),
            Some(h) => {
                let Some(position) = goal.hyps.iter().rposition(|(n, _)| n.as_str() == h.name)
                else {
                    return Err(Diagnostic::new(
                        h.span,
                        format!("no hypothesis named `{}`", h.name),
                    ));
                };
                (goal.hyps[position].1.clone(), Some(position))
            }
        };
        let (conv, changed) = normalize(&subst, &rules, &subject).map_err(kernel(span))?;
        if !changed {
            return Err(Diagnostic::new(
                span,
                format!(
                    "no occurrence of `{}` in {}",
                    name.name,
                    if at.is_some() {
                        "the hypothesis"
                    } else {
                        "the goal"
                    }
                ),
            ));
        }
        self.replace_with_conv(state, goal, conv, hyp_index, span)
    }

    fn simp(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        extra: &[ProofExpr],
        target: &SimpTarget,
        span: Span,
    ) -> Result<()> {
        let mut ctx = self.ctx(goal);
        let mut rules = ctx.rules.clone();
        for expr in extra {
            let thm = ctx.elab_proof(expr)?;
            let thm = ctx.subst.apply_thm(&thm).map_err(kernel(span))?;
            let Some(rule) = Rule::from_thm(&mut ctx.subst, &thm, "simp", false) else {
                return Err(Diagnostic::new(
                    expr.span(),
                    format!(
                        "`simp` rules must be equations, but this proves `{}`",
                        ctx.show(thm.concl())
                    ),
                ));
            };
            rules.push(rule);
        }
        let mut targets: Vec<Option<usize>> = Vec::new();
        match target {
            SimpTarget::Goal => targets.push(None),
            SimpTarget::Hyp(name) => {
                let Some(position) = goal.hyps.iter().rposition(|(n, _)| n.as_str() == name.name)
                else {
                    return Err(Diagnostic::new(
                        name.span,
                        format!("no hypothesis named `{}`", name.name),
                    ));
                };
                targets.push(Some(position));
            }
            SimpTarget::All => {
                targets.push(None);
                targets.extend((0..goal.hyps.len()).map(Some));
            }
        }
        let mut any = false;
        let mut current = goal.clone();
        for hyp_index in targets {
            let subject = match hyp_index {
                None => current.target.clone(),
                Some(i) => current.hyps[i].1.clone(),
            };
            let (conv, changed) = normalize(&ctx.subst, &rules, &subject).map_err(kernel(span))?;
            if !changed {
                continue;
            }
            any = true;
            let goal_now = state.current().cloned().expect("goal");
            self.replace_with_conv(state, &goal_now, conv, hyp_index, span)?;
            current = state.current().cloned().expect("goal");
        }
        if !any {
            self.notes.push(Diagnostic::new(
                span,
                "this `simp` did nothing; consider deleting it".to_string(),
            ));
        }
        Ok(())
    }

    fn contradiction(&mut self, state: &mut ProofState, goal: &Goal, span: Span) -> Result<()> {
        let ctx = self.ctx(goal);
        let target = goal.target.clone();
        // Normalize hypotheses so `x in empty(T)` counts as `False`.
        let mut normalized: Vec<(Term, Thm)> = Vec::new();
        for (_, hyp) in &goal.hyps {
            let conv = ctx.norm(hyp).map_err(kernel(span))?;
            let thm = eq_mp(&conv, &assume(hyp).map_err(kernel(span))?).map_err(kernel(span))?;
            normalized.push((rhs(&conv), thm));
        }
        for (formula, thm) in &normalized {
            if formula.is_false() {
                let absurd = false_elim(thm, &target).map_err(kernel(span))?;
                state.close(goal.id, vec![], Box::new(move |_| Ok(absurd.clone())));
                return Ok(());
            }
        }
        for (formula, neg_thm) in &normalized {
            let Some(p) = formula.dest_not() else {
                continue;
            };
            for (other, pos_thm) in &normalized {
                if other == p {
                    let falsity = imp_elim(neg_thm, pos_thm).map_err(kernel(span))?;
                    let absurd = false_elim(&falsity, &target).map_err(kernel(span))?;
                    state.close(goal.id, vec![], Box::new(move |_| Ok(absurd.clone())));
                    return Ok(());
                }
            }
        }
        Err(Diagnostic::new(
            span,
            "`contradiction` needs a hypothesis `False`, or a proposition and its negation among the hypotheses".to_string(),
        ))
    }

    fn require_classical(&self, span: Span, tactic: &str, about: &Term) -> Result<()> {
        if self.env.mode == Mode::Constructive {
            return Err(Diagnostic::new(
                span,
                format!(
                    "`{tactic}` introduces a classical proof of `{}`, but the file is in constructive mode",
                    self.show(about)
                ),
            )
            .note("add `mode classical` above the theorem if classical reasoning is intended"));
        }
        Ok(())
    }

    fn by_cases(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        name: &Ident,
        prop: &Expr,
        span: Span,
    ) -> Result<()> {
        let p = self.elab_formula(goal, prop)?;
        self.require_classical(span, "by_cases", &p)?;
        self.check_fresh(goal, name)?;
        let not_p = Term::not(&p).map_err(kernel(span))?;
        let mut pos_hyps = goal.hyps.clone();
        pos_hyps.push((Name::new(&name.name), p.clone()));
        let mut neg_hyps = goal.hyps.clone();
        neg_hyps.push((Name::new(&name.name), not_p));
        let positive = Goal {
            hyps: pos_hyps,
            ..goal.clone()
        };
        let negative = Goal {
            hyps: neg_hyps,
            ..goal.clone()
        };
        let just: Justification =
            Box::new(move |thms| or_elim(&excluded_middle(&p)?, &thms[0], &thms[1]));
        state.close(goal.id, vec![positive, negative], just);
        Ok(())
    }

    fn by_contra(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        name: &Ident,
        span: Span,
    ) -> Result<()> {
        let target = goal.target.clone();
        self.require_classical(span, "by_contra", &target)?;
        self.check_fresh(goal, name)?;
        let not_target = Term::not(&target).map_err(kernel(span))?;
        let mut hyps = goal.hyps.clone();
        hyps.push((Name::new(&name.name), not_target));
        let subgoal = Goal {
            hyps,
            target: Term::false_(),
            ..goal.clone()
        };
        let just: Justification = Box::new(move |thms| {
            let positive = assume(&target)?;
            let negative = false_elim(&thms[0], &target)?;
            or_elim(&excluded_middle(&target)?, &positive, &negative)
        });
        state.close(goal.id, vec![subgoal], just);
        Ok(())
    }

    fn have(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        name: &Ident,
        stated: Option<&Expr>,
        proof: &HaveProof,
        span: Span,
    ) -> Result<()> {
        self.check_fresh(goal, name)?;
        let stated_term = match stated {
            Some(expr) => Some(self.elab_formula(goal, expr)?),
            None => None,
        };
        match proof {
            HaveProof::Subgoal => {
                let formula = stated_term.expect("parser requires a statement");
                self.have_with_goal(state, goal, name, formula, None)
            }
            HaveProof::Expr(expr) => {
                let mut ctx = self.ctx(goal);
                let thm = ctx.elab_proof(expr)?;
                let thm = match &stated_term {
                    Some(formula) => ctx.coerce(thm, formula, expr.span()).map_err(|d| {
                        if d.message.starts_with("proof has type") {
                            let message =
                                d.message
                                    .replacen("proof has type", "have proof has type", 1);
                            Diagnostic::new(
                                expr.span(),
                                message.replace("but expected", "but the stated formula is"),
                            )
                        } else {
                            d
                        }
                    })?,
                    None => thm,
                };
                let thm = ctx.finalize(&thm, expr.span(), "the theorem")?;
                let formula = thm.concl().clone();
                self.have_with_goal(state, goal, name, formula, Some(thm))
            }
            HaveProof::Block(body) => {
                let formula = stated_term.expect("parser requires a statement");
                self.have_with_goal(state, goal, name, formula, None)?;
                let what = format!("the proof of `have {}`", name.name);
                self.run_block_closing(state, body, &what, span)
            }
        }
    }

    /// Adds `name : formula` to the goal; the formula is proved by `thm`
    /// if given, otherwise by a new first subgoal.
    fn have_with_goal(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        name: &Ident,
        formula: Term,
        thm: Option<Thm>,
    ) -> Result<()> {
        let mut hyps = goal.hyps.clone();
        hyps.push((Name::new(&name.name), formula.clone()));
        let main = Goal {
            hyps,
            ..goal.clone()
        };
        match thm {
            Some(thm) => {
                let just: Justification =
                    Box::new(move |thms| imp_elim(&imp_intro(&formula, &thms[0])?, &thm));
                state.close(goal.id, vec![main], just);
            }
            None => {
                let side = Goal {
                    target: formula.clone(),
                    ..goal.clone()
                };
                let just: Justification =
                    Box::new(move |thms| imp_elim(&imp_intro(&formula, &thms[1])?, &thms[0]));
                state.close(goal.id, vec![side, main], just);
            }
        }
        Ok(())
    }

    fn show_tactic(
        &mut self,
        state: &mut ProofState,
        goal: &Goal,
        expr: &Expr,
        span: Span,
    ) -> Result<()> {
        let stated = self.elab_formula(goal, expr)?;
        let ctx = self.ctx(goal);
        let nt = ctx.norm(&goal.target).map_err(kernel(span))?;
        let ns = ctx.norm(&stated).map_err(kernel(span))?;
        if rhs(&nt) != rhs(&ns) {
            return Err(Diagnostic::new(
                span,
                format!(
                    "`show` states `{}`, but the goal is `{}`",
                    self.show(&stated),
                    self.show(&goal.target)
                ),
            ));
        }
        let subgoal = Goal {
            target: stated,
            ..goal.clone()
        };
        let just: Justification = Box::new(move |thms| {
            let bridge = trans(&ns, &sym(&nt)?)?;
            eq_mp(&bridge, &thms[0])
        });
        state.close(goal.id, vec![subgoal], just);
        Ok(())
    }
}

/// Hypotheses together with their simple consequences: conclusions of
/// implications and halves of conjunctions. Used only to pin down
/// metavariables; the student still has to prove the premise.
fn hypothesis_consequences(goal: &Goal) -> Vec<Term> {
    let mut out = Vec::new();
    let mut queue: Vec<Term> = goal.hyp_formulas();
    while let Some(formula) = queue.pop() {
        if out.contains(&formula) {
            continue;
        }
        if let Some((_, conclusion)) = formula.dest_imp() {
            if !conclusion.is_false() {
                queue.push(conclusion.clone());
            }
        }
        if let Some((a, b)) = formula.dest_and() {
            queue.push(a.clone());
            queue.push(b.clone());
        }
        out.push(formula);
    }
    out
}

/// Converts `thm` into a proof of `target` when the two agree up to
/// normalization.
fn bridge(subst: &Subst, rules: &Rules, thm: Thm, target: &Term) -> hol_kernel::Result<Thm> {
    if thm.concl() == target {
        return Ok(thm);
    }
    let (nc, _) = normalize(subst, rules, thm.concl())?;
    let (nt, _) = normalize(subst, rules, target)?;
    if rhs(&nc) != rhs(&nt) {
        return Err(hol_kernel::KernelError::new(
            "apply",
            format!(
                "`{}` does not match `{}` after normalization",
                thm.concl(),
                target
            ),
        ));
    }
    eq_mp(&trans(&nc, &sym(&nt)?)?, &thm)
}

/// Rewrites the first occurrence (or every occurrence) of the rule's left
/// side in `t`. Returns `|- t = t'` (or `None` when nothing matched) and
/// the number of occurrences of the instantiated pattern.
fn rewrite_occurrences(
    subst: &mut Subst,
    rule: &Rule,
    t: &Term,
    all: bool,
    span: Span,
) -> Result<(Option<Thm>, usize)> {
    // First pass: find the first match to instantiate metavariables.
    let Some(first) = find_first_match(subst, rule, t) else {
        return Ok((None, 0));
    };
    *subst = first;
    let instantiated = subst.apply_thm(&rule.thm).map_err(kernel(span))?;
    let (lhs, rhs_term) = instantiated
        .concl()
        .dest_eq()
        .map(|(a, b)| (a.clone(), b.clone()))
        .expect("equation");
    if all && rhs_term.count_const_free(&lhs) {
        return Err(Diagnostic::new(
            span,
            format!("`rewrite all` would loop: the replacement `{rhs_term}` contains `{lhs}`"),
        ));
    }
    let count = count_occurrences(&lhs, t);
    let conv = if all {
        rewrite_all(&instantiated, &lhs, t).map_err(kernel(span))?
    } else {
        rewrite_first(&instantiated, &lhs, t).map_err(kernel(span))?
    };
    Ok((conv, count))
}

fn find_first_match(subst: &Subst, rule: &Rule, t: &Term) -> Option<Subst> {
    let mut trial = subst.clone();
    if t.is_closed() && trial.unify(&rule.lhs, t) {
        return Some(trial);
    }
    match t.view() {
        TermView::App(f, x) => {
            find_first_match(subst, rule, f).or_else(|| find_first_match(subst, rule, x))
        }
        TermView::Lam(..) => {
            let (_, body) = t.open_fresh(&BTreeSet::new()).expect("lambda");
            find_first_match(subst, rule, &body)
        }
        _ => None,
    }
}

fn count_occurrences(pattern: &Term, t: &Term) -> usize {
    if t == pattern {
        return 1;
    }
    match t.view() {
        TermView::App(f, x) => count_occurrences(pattern, f) + count_occurrences(pattern, x),
        TermView::Lam(..) => {
            let (_, body) = t.open_fresh(&BTreeSet::new()).expect("lambda");
            count_occurrences(pattern, &body)
        }
        _ => 0,
    }
}

/// `|- t = t'` replacing the first occurrence of the equation's left side.
fn rewrite_first(equation: &Thm, lhs: &Term, t: &Term) -> hol_kernel::Result<Option<Thm>> {
    if t == lhs {
        return Ok(Some(equation.clone()));
    }
    match t.view() {
        TermView::App(f, x) => {
            if let Some(cf) = rewrite_first(equation, lhs, f)? {
                return Ok(Some(hol_kernel::mk_comb(&cf, &refl(x)?)?));
            }
            if let Some(cx) = rewrite_first(equation, lhs, x)? {
                return Ok(Some(hol_kernel::mk_comb(&refl(f)?, &cx)?));
            }
            Ok(None)
        }
        TermView::Lam(..) => {
            let (var, body) = t.open_fresh(&BTreeSet::new()).expect("lambda");
            match rewrite_first(equation, lhs, &body)? {
                Some(cb) => Ok(Some(hol_kernel::abs(&var, &cb)?)),
                None => Ok(None),
            }
        }
        _ => Ok(None),
    }
}

fn rewrite_all(equation: &Thm, lhs: &Term, t: &Term) -> hol_kernel::Result<Option<Thm>> {
    if t == lhs {
        return Ok(Some(equation.clone()));
    }
    match t.view() {
        TermView::App(f, x) => {
            let cf = rewrite_all(equation, lhs, f)?;
            let cx = rewrite_all(equation, lhs, x)?;
            match (cf, cx) {
                (None, None) => Ok(None),
                (cf, cx) => {
                    let cf = match cf {
                        Some(c) => c,
                        None => refl(f)?,
                    };
                    let cx = match cx {
                        Some(c) => c,
                        None => refl(x)?,
                    };
                    Ok(Some(hol_kernel::mk_comb(&cf, &cx)?))
                }
            }
        }
        TermView::Lam(..) => {
            let (var, body) = t.open_fresh(&BTreeSet::new()).expect("lambda");
            match rewrite_all(equation, lhs, &body)? {
                Some(cb) => Ok(Some(hol_kernel::abs(&var, &cb)?)),
                None => Ok(None),
            }
        }
        _ => Ok(None),
    }
}

trait ContainsTerm {
    fn count_const_free(&self, pattern: &Term) -> bool;
}

impl ContainsTerm for Term {
    fn count_const_free(&self, pattern: &Term) -> bool {
        count_occurrences(pattern, self) > 0
    }
}

/// Beta-normalizes a goal's statement for display.
pub fn tidy(term: &Term) -> Term {
    term.beta_normalize()
}
