//! Bounded proof construction for concrete finite enumerations.
//! Every step uses the ordinary proof language and checked library theorems.
use super::*;

pub(super) fn solve(env: &Env, goal: Goal, mode: LogicMode) -> Result<StepResult, TacticError> {
    #[cfg(not(feature = "hol-shadow"))]
    {
        let _ = (env, goal, mode);
        Err(TacticError::new(
            "finite requires checked logical-package support",
        ))
    }
    #[cfg(feature = "hol-shadow")]
    {
        let mut search = Search {
            env,
            mode,
            fuel: 2048,
            next: 1,
            helpers: BTreeMap::new(),
        };
        for (name, origin) in &env.package_origins {
            for helper in [
                "has_card_intro",
                "nodup_cons",
                "nodup_nil",
                "member_cons",
                "member_nil",
                "length_cons",
                "length_nil",
            ] {
                if (origin == &format!("std/hol/list@1.{helper}")
                    || origin == &format!("std/hol/finite@1.{helper}"))
                    && env.theorem(name).is_some()
                {
                    search
                        .helpers
                        .entry(helper)
                        .and_modify(|existing| {
                            if name < existing {
                                *existing = name.clone();
                            }
                        })
                        .or_insert_with(|| name.clone());
                }
            }
        }
        let proof = search.prove(goal.clone(), &HashSet::new(), 0).map_err(|_| {
            TacticError::new(format!("finite could not construct a proof of `{}`; use an explicit finite constructor list and import std/hol/finite@1, or prove the remaining claim manually", goal.target))
        })?;
        check_completed_draft(env, &goal.context, &proof, &goal.target, mode).map_err(|err| {
            TacticError::new(format!("finite proof was rejected: {}", err.message))
        })?;
        Ok(StepResult {
            replacement: PartialProof::Done(proof),
            new_goals: vec![],
            notes: vec![],
        })
    }
}

#[cfg(feature = "hol-shadow")]
struct Search<'a> {
    env: &'a Env,
    mode: LogicMode,
    fuel: usize,
    next: usize,
    helpers: BTreeMap<&'static str, String>,
}

#[cfg(feature = "hol-shadow")]
impl Search<'_> {
    fn fresh(&mut self, ctx: &Context) -> String {
        loop {
            let name = format!("__finite_{}", self.next);
            self.next += 1;
            if ensure_induction_binder_unused(ctx, &name).is_ok() {
                return name;
            }
        }
    }

    fn step(
        &mut self,
        goal: Goal,
        tactic: Tactic,
        expanded: &HashSet<Formula>,
        depth: usize,
    ) -> Result<DraftProof, ()> {
        let mut step = run_tactic_step(self.env, goal.clone(), &tactic, self.mode, &mut self.next)
            .map_err(|_| ())?;
        if step.new_goals.len() == 1
            && step.new_goals[0].target == goal.target
            && step.new_goals[0].context == goal.context
        {
            return Err(());
        }
        for child in step.new_goals {
            let id = child.id;
            let proof = self.prove(child, expanded, depth + 1)?;
            step.replacement
                .replace_hole(id, &PartialProof::Done(proof));
        }
        let proof = step.replacement.complete().map_err(|_| ())?;
        Ok(DraftProof::Convert {
            proof_body: Box::new(proof),
            target: goal.target,
        })
    }

    fn prove(
        &mut self,
        goal: Goal,
        expanded: &HashSet<Formula>,
        depth: usize,
    ) -> Result<DraftProof, ()> {
        if self.fuel == 0 || depth > 96 {
            return Err(());
        }
        self.fuel -= 1;
        for tactic in [
            Tactic::Trivial,
            Tactic::Assumption,
            Tactic::Contradiction,
            Tactic::Refl,
        ] {
            if let Ok(proof) = self.step(goal.clone(), tactic, expanded, depth) {
                return Ok(proof);
            }
        }
        let normalized =
            normalize_formula_defs(self.env, &goal.context, &goal.target).map_err(|_| ())?;
        if normalized != goal.target {
            let proof = self.prove(
                Goal {
                    target: normalized,
                    ..goal.clone()
                },
                expanded,
                depth + 1,
            )?;
            return Ok(DraftProof::Convert {
                proof_body: Box::new(proof),
                target: goal.target,
            });
        }
        match &goal.target {
            Formula::And(_, _) => return self.step(goal, Tactic::Split, expanded, depth),
            Formula::Implies(_, _) => {
                let name = self.fresh(&goal.context);
                return self.step(goal, Tactic::Intro(name), expanded, depth);
            }
            Formula::Or(_, _) => {
                for tactic in [Tactic::Left, Tactic::Right] {
                    if let Ok(proof) = self.step(goal.clone(), tactic, expanded, depth) {
                        return Ok(proof);
                    }
                }
            }
            Formula::Forall {
                var,
                var_type: Type::Named(data_name),
                body,
            } => {
                if let Some(data) = self.env.data_def(data_name).cloned() {
                    if data.ctors.iter().all(|ctor| ctor.arg_types.is_empty()) {
                        let name = self.fresh(&goal.context);
                        let target = subst_formula_term(body, var, &Term::Var(name.clone()));
                        let mut ctx = goal.context.clone();
                        ctx.add_term(name.clone(), Type::Named(data_name.clone()));
                        let mut arms = Vec::new();
                        for ctor in data.ctors {
                            let instance = subst_formula_term(
                                &target,
                                &name,
                                &data_ctor_term(&ctor.name, &[]),
                            );
                            let proof = self.prove(
                                Goal {
                                    id: 0,
                                    context: ctx.clone(),
                                    target: instance,
                                },
                                expanded,
                                depth + 1,
                            )?;
                            arms.push(DataIndArm {
                                ctor: ctor.name,
                                arg_names: vec![],
                                ih_names: vec![],
                                proof,
                            });
                        }
                        return Ok(DraftProof::ForallIntro {
                            var: name.clone(),
                            var_type: Type::Named(data_name.clone()),
                            body: Box::new(DraftProof::DataInd {
                                var_name: name,
                                data_name: data_name.clone(),
                                target,
                                arms,
                            }),
                        });
                    }
                }
            }
            _ => {}
        }
        for (helper, suffix) in [
            ("has_card_intro", ""),
            ("nodup_cons", ".right"),
            ("nodup_nil", ""),
            ("member_cons", ".right"),
            ("member_nil", ""),
        ] {
            if let Some(name) = self.helpers.get(helper) {
                let expr = parse_proof_expr(&format!("{name}{suffix}")).map_err(|_| ())?;
                if let Ok(proof) = self.step(goal.clone(), Tactic::Apply(expr), expanded, depth) {
                    return Ok(proof);
                }
            }
        }
        for helper in ["length_cons", "length_nil"] {
            if let Some(name) = self.helpers.get(helper) {
                let tactic = Tactic::Rewrite {
                    expr: parse_proof_expr(name).map_err(|_| ())?,
                    direction: RewriteDirection::Forward,
                    all: false,
                    hypothesis: None,
                };
                if let Ok(proof) = self.step(goal.clone(), tactic, expanded, depth) {
                    return Ok(proof);
                }
            }
        }
        for (binding, evidence) in goal.context.proof_bindings().rev() {
            if expanded.contains(&binding.formula) {
                continue;
            }
            let mut expanded = expanded.clone();
            expanded.insert(binding.formula.clone());
            if let Formula::Or(left, right) = &binding.formula {
                let left_name = self.fresh(&goal.context);
                let right_name = self.fresh(&goal.context);
                let mut left_goal = goal.clone();
                left_goal
                    .context
                    .add_proof(left_name.clone(), *left.clone());
                let mut right_goal = goal.clone();
                right_goal
                    .context
                    .add_proof(right_name.clone(), *right.clone());
                if let (Ok(left_case), Ok(right_case)) = (
                    self.prove(left_goal, &expanded, depth + 1),
                    self.prove(right_goal, &expanded, depth + 1),
                ) {
                    return Ok(DraftProof::OrElim {
                        proof_or: Box::new(evidence.clone()),
                        left_name,
                        left_case: Box::new(left_case),
                        right_name,
                        right_case: Box::new(right_case),
                        target: goal.target.clone(),
                    });
                }
            }
            if let Some(name) = self.helpers.get("member_cons") {
                let theorem = self.env.theorem(name).ok_or(())?;
                let Formula::And(forward, _) = &theorem.statement else {
                    continue;
                };
                let Formula::Implies(premise, conclusion) = forward.as_ref() else {
                    continue;
                };
                if let Ok(subst) = infer_schema_subst_for_formula(
                    self.env,
                    &goal.context,
                    &theorem.params,
                    premise,
                    &binding.formula,
                    SchemaSubst::default(),
                    Some(name),
                ) {
                    let formula = subst_formula_schema(conclusion, &subst);
                    let proof = DraftProof::ImpElim {
                        proof_imp: Box::new(DraftProof::AndElimLeft(Box::new(
                            DraftProof::TheoremRef {
                                name: name.clone(),
                                subst,
                            },
                        ))),
                        proof_arg: Box::new(evidence.clone()),
                    };
                    let mut next_goal = goal.clone();
                    let name = self.fresh(&goal.context);
                    next_goal
                        .context
                        .add_proof_with_kernel(name, formula.clone(), proof, formula);
                    if let Ok(proof) = self.prove(next_goal, &expanded, depth + 1) {
                        return Ok(proof);
                    }
                }
            }
        }
        Err(())
    }
}

#[cfg(all(test, feature = "hol-shadow"))]
mod tests {
    use super::*;
    #[test]
    fn constructs_checked_finite_enumerations() {
        let source = include_str!("../../../docs/hol/examples/finite_enumeration.ctea");
        let report = check_file_with_hol_shadow(source);
        assert!(
            report.legacy.diagnostics.is_empty(),
            "{:?}",
            report.legacy.diagnostics
        );
        assert!(report.is_match(), "{:?}", report.mismatches);
        let receipt = report
            .theorems
            .iter()
            .find(|t| t.name == "three_colours")
            .unwrap();
        assert_eq!(
            receipt.required_fragment,
            hol::StatementFragment::FirstOrderInductive
        );
        assert_eq!(receipt.hol_mode_used, LogicMode::Constructive);
        assert!(receipt.axiom_deps.is_empty());
        assert!(receipt.incomplete_deps.is_empty());
    }

    #[test]
    fn rejects_duplicates_missing_constructors_and_incorrect_lengths() {
        let prefix =
            "import std/hol/finite@1 as F\nmode constructive\ndata Colour\n| red\n| blue\n";
        for target in [
            "F.Nodup(F.cons(red, F.cons(red, F.nil)))",
            "F.HasCard(F.cons(red, F.nil), 1)",
            "F.HasCard(F.cons(red, F.cons(blue, F.nil)), 3)",
            "F.Member(blue, F.cons(red, F.nil))",
            "F.HasCard(F.cons(0, F.nil), 1)",
        ] {
            let report = check_file_with_hol_shadow(&format!(
                "{prefix}theorem bad : {target} := by\n  finite\n"
            ));
            assert!(
                report
                    .legacy
                    .diagnostics
                    .iter()
                    .any(|d| d.message.contains("finite could not construct")),
                "{target}: {:?}",
                report.legacy.diagnostics
            );
            assert!(!report.certified().theorems.iter().any(|t| t.name == "bad"));
        }
    }

    #[test]
    fn arbitrary_names_do_not_impersonate_checked_enumeration_helpers() {
        let report = check_file_with_hol_shadow("pred HasCard(Nat, Nat)\naxiom has_card_intro : HasCard(0, 7)\ntheorem bad : HasCard(0, 7) := by\n  finite\n");
        assert!(
            report
                .legacy
                .diagnostics
                .iter()
                .any(|d| d.message.contains("finite could not construct")),
            "{:?}",
            report.legacy.diagnostics
        );
        assert!(!report.certified().theorems.iter().any(|t| t.name == "bad"));
    }

    #[test]
    fn proof_search_budget_is_enforced() {
        let env = Env::default();
        let mut search = Search {
            env: &env,
            mode: LogicMode::Constructive,
            fuel: 0,
            next: 1,
            helpers: BTreeMap::new(),
        };
        assert!(search
            .prove(
                Goal {
                    id: 0,
                    context: Context::default(),
                    target: Formula::True
                },
                &HashSet::new(),
                0
            )
            .is_err());
    }
}
