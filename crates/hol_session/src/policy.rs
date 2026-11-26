//! Checking policies and course sections.
//!
//! A [`Policy`] says what a proof may rely on beyond being correct:
//! whether `sorry`, root axioms, or classical reasoning are acceptable,
//! and which tactics and library theorems may be used. A [`Course`]
//! names a policy and a tier for each section of a class, so "week 2
//! may use only the introduction and elimination rules" and "from week
//! 6 on `simp` and the `nat` library are available" are written once
//! and selected by name.
//!
//! Policies never change what is provable. A proof that breaks its
//! policy is still a kernel-checked proof; it is reported at the line
//! that broke the rule and the file does not pass.

use std::collections::BTreeSet;

use hol_syntax::{HaveProof, Span, Tactic, TacticKind, Tier};
use serde::{Deserialize, Serialize};

/// Tactics that stay available under any allow list: they inspect or
/// postpone a proof instead of making progress in it. `sorry` is still
/// governed by `deny_sorry`.
pub const ALWAYS_ALLOWED_TACTICS: &[&str] = &["show_goal", "sorry"];

/// Every tactic name the checker knows, for validating policy files.
pub const KNOWN_TACTICS: &[&str] = &[
    "intro",
    "revert",
    "exact",
    "trivial",
    "assumption",
    "apply",
    "split",
    "left",
    "right",
    "cases",
    "exists",
    "refl",
    "rewrite",
    "unfold",
    "simp",
    "induction",
    "exfalso",
    "contradiction",
    "by_cases",
    "by_contra",
    "show_goal",
    "sorry",
    "have",
    "show",
    "funext",
    "obtain",
    "calc",
];

fn is_false(value: &bool) -> bool {
    !*value
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Policy {
    #[serde(default)]
    pub deny_sorry: bool,
    #[serde(default)]
    pub deny_axioms: bool,
    #[serde(default)]
    pub deny_classical: bool,
    /// Tactics that may not be used, such as `simp` or `decide`.
    #[serde(default)]
    pub deny_tactics: Vec<String>,
    /// When present, the only tactics that may be used (besides
    /// [`ALWAYS_ALLOWED_TACTICS`]). A denied tactic stays denied.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allow_tactics: Option<Vec<String>>,
    /// Imported theorems that may not be cited. Each entry is a name or
    /// a `*` pattern (`add_*`, `*_comm`, `*`), matched against the full
    /// name and against the part after an import alias.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub deny_theorems: Vec<String>,
    /// When present, the only imported theorems that may be cited.
    /// Theorems proved in the submitted file itself are always usable.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allow_theorems: Option<Vec<String>>,
    /// The course section this policy came from, for messages.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub section: Option<String>,
    /// Report tactic and theorem rules as warnings instead of errors,
    /// for practice files where the rules are advice.
    #[serde(default, skip_serializing_if = "is_false")]
    pub advisory: bool,
}

/// True when `pattern` (a name, or a glob with `*`) matches `name`.
pub fn pattern_matches(pattern: &str, name: &str) -> bool {
    fn glob(pattern: &[u8], text: &[u8]) -> bool {
        match pattern.split_first() {
            None => text.is_empty(),
            Some((b'*', rest)) => (0..=text.len()).any(|skip| glob(rest, &text[skip..])),
            Some((ch, rest)) => text
                .split_first()
                .is_some_and(|(first, tail)| first == ch && glob(rest, tail)),
        }
    }
    let leaf = name.rsplit('.').next().unwrap_or(name);
    glob(pattern.as_bytes(), name.as_bytes())
        || (leaf != name && glob(pattern.as_bytes(), leaf.as_bytes()))
}

fn union(into: &mut Vec<String>, from: &[String]) {
    for item in from {
        if !into.contains(item) {
            into.push(item.clone());
        }
    }
}

impl Policy {
    /// True when the policy restricts nothing.
    pub fn is_empty(&self) -> bool {
        *self == Policy::default()
    }

    /// True when the policy restricts something, as opposed to only
    /// carrying a label or the advisory switch.
    pub fn has_rules(&self) -> bool {
        Policy {
            section: None,
            advisory: false,
            ..self.clone()
        } != Policy::default()
    }

    /// Where the rules come from, for messages: `section \`x\`` or
    /// `this assignment`.
    pub fn source_label(&self) -> String {
        match &self.section {
            Some(section) => format!("the section `{section}`"),
            None => "this assignment".to_string(),
        }
    }

    /// Combines two independent policies so that both are respected:
    /// flags are or-ed, deny lists are united, and when both carry an
    /// allow list only what both allow stays allowed. Used when a
    /// manifest and command-line flags both apply.
    pub fn restrict_with(&mut self, other: &Policy) {
        // Rules are advisory only when every policy that sets any says so.
        self.advisory = match (!self.has_rules(), !other.has_rules()) {
            (true, _) => other.advisory,
            (_, true) => self.advisory,
            _ => self.advisory && other.advisory,
        };
        self.deny_sorry |= other.deny_sorry;
        self.deny_axioms |= other.deny_axioms;
        self.deny_classical |= other.deny_classical;
        union(&mut self.deny_tactics, &other.deny_tactics);
        union(&mut self.deny_theorems, &other.deny_theorems);
        self.allow_tactics = match (self.allow_tactics.take(), &other.allow_tactics) {
            (Some(mine), Some(theirs)) => {
                Some(mine.into_iter().filter(|t| theirs.contains(t)).collect())
            }
            (Some(mine), None) => Some(mine),
            (None, theirs) => theirs.clone(),
        };
        self.allow_theorems = match (self.allow_theorems.take(), &other.allow_theorems) {
            (Some(mine), Some(theirs)) => {
                // Patterns cannot be intersected in general; keep the
                // entries of each list that the other list also matches.
                let mut kept: Vec<String> = mine
                    .iter()
                    .filter(|p| theirs.iter().any(|q| pattern_matches(q, p) || q == *p))
                    .cloned()
                    .collect();
                for pattern in theirs {
                    if mine.iter().any(|q| pattern_matches(q, pattern)) && !kept.contains(pattern) {
                        kept.push(pattern.clone());
                    }
                }
                Some(kept)
            }
            (Some(mine), None) => Some(mine),
            (None, theirs) => theirs.clone(),
        };
        if self.section.is_none() {
            self.section = other.section.clone();
        }
    }

    /// Builds on a parent section's policy: flags are or-ed, deny lists
    /// are united, and allow lists grow, because a later section of a
    /// course normally unlocks more than the one it extends.
    pub fn extend_from(&mut self, parent: &Policy) {
        self.deny_sorry |= parent.deny_sorry;
        self.deny_axioms |= parent.deny_axioms;
        self.deny_classical |= parent.deny_classical;
        self.advisory |= parent.advisory;
        let mut deny_tactics = parent.deny_tactics.clone();
        union(&mut deny_tactics, &self.deny_tactics);
        self.deny_tactics = deny_tactics;
        let mut deny_theorems = parent.deny_theorems.clone();
        union(&mut deny_theorems, &self.deny_theorems);
        self.deny_theorems = deny_theorems;
        self.allow_tactics = match (&parent.allow_tactics, self.allow_tactics.take()) {
            (Some(theirs), Some(mine)) => {
                let mut all = theirs.clone();
                union(&mut all, &mine);
                Some(all)
            }
            (Some(theirs), None) => Some(theirs.clone()),
            (None, mine) => mine,
        };
        self.allow_theorems = match (&parent.allow_theorems, self.allow_theorems.take()) {
            (Some(theirs), Some(mine)) => {
                let mut all = theirs.clone();
                union(&mut all, &mine);
                Some(all)
            }
            (Some(theirs), None) => Some(theirs.clone()),
            (None, mine) => mine,
        };
    }

    /// Why `tactic` may not be used, or `None` when it may.
    pub fn tactic_problem(&self, tactic: &str) -> Option<String> {
        if self.deny_tactics.iter().any(|t| t == tactic) {
            return Some(format!(
                "`{tactic}` is not allowed in {}",
                self.source_label()
            ));
        }
        if ALWAYS_ALLOWED_TACTICS.contains(&tactic) {
            return None;
        }
        match &self.allow_tactics {
            Some(allowed) if !allowed.iter().any(|t| t == tactic) => Some(format!(
                "`{tactic}` is not available in {}",
                self.source_label()
            )),
            _ => None,
        }
    }

    /// The tactics an allow list leaves available, for a note under a
    /// refusal; `None` when tactics are not restricted to a list.
    pub fn available_tactics(&self) -> Option<Vec<String>> {
        self.allow_tactics.as_ref().map(|allowed| {
            allowed
                .iter()
                .filter(|t| !self.deny_tactics.contains(t))
                .cloned()
                .collect()
        })
    }

    /// Why the imported theorem `name` may not be cited, or `None`.
    pub fn theorem_problem(&self, name: &str) -> Option<String> {
        if self.deny_theorems.iter().any(|p| pattern_matches(p, name)) {
            return Some(format!(
                "the theorem `{name}` is not allowed in {}",
                self.source_label()
            ));
        }
        match &self.allow_theorems {
            Some(allowed) if !allowed.iter().any(|p| pattern_matches(p, name)) => Some(format!(
                "the theorem `{name}` is not available in {}",
                self.source_label()
            )),
            _ => None,
        }
    }

    /// True when the policy restricts which theorems may be cited.
    pub fn restricts_theorems(&self) -> bool {
        self.allow_theorems.is_some() || !self.deny_theorems.is_empty()
    }

    /// Tactic names in the policy that the checker does not know, which
    /// are almost always typos in a course file.
    pub fn unknown_tactics(&self) -> Vec<String> {
        self.deny_tactics
            .iter()
            .chain(self.allow_tactics.iter().flatten())
            .filter(|t| !KNOWN_TACTICS.contains(&t.as_str()))
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
}

/// One section of a course: a tier and the rules for work in it.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Section {
    /// The short name used on the command line and in manifests.
    pub id: String,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub title: String,
    /// A note for students about what the section is practising.
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub description: String,
    /// The section whose rules this one builds on.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub extends: Option<String>,
    /// `fol`, `fol_nat`, or `hol`; inherited when absent.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tier: Option<String>,
    #[serde(flatten)]
    pub policy: Policy,
}

/// A course: its sections, in teaching order.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Course {
    #[serde(default)]
    pub title: String,
    #[serde(default)]
    pub sections: Vec<Section>,
}

/// A section with its inheritance resolved.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResolvedSection {
    pub id: String,
    pub title: String,
    pub description: String,
    pub tier: Option<String>,
    pub policy: Policy,
}

impl Course {
    pub fn parse(text: &str) -> Result<Course, String> {
        let course: Course =
            serde_json::from_str(text).map_err(|e| format!("the course file is not valid: {e}"))?;
        course.validate()?;
        Ok(course)
    }

    /// Checks ids, parents, tiers and tactic names, so a typo in a
    /// course file is reported when the file is loaded and not as a
    /// rule that silently never fires.
    pub fn validate(&self) -> Result<(), String> {
        let mut seen = BTreeSet::new();
        for section in &self.sections {
            if section.id.is_empty() {
                return Err("a section has an empty `id`".to_string());
            }
            if !seen.insert(section.id.as_str()) {
                return Err(format!("the section id `{}` is used twice", section.id));
            }
            if let Some(tier) = &section.tier {
                if Tier::parse(tier).is_none() {
                    return Err(format!(
                        "the section `{}` names the unknown tier `{tier}`; use `fol`, `fol_nat`, or `hol`",
                        section.id
                    ));
                }
            }
            let unknown = section.policy.unknown_tactics();
            if !unknown.is_empty() {
                return Err(format!(
                    "the section `{}` names unknown tactic{} {}",
                    section.id,
                    if unknown.len() == 1 { "" } else { "s" },
                    unknown
                        .iter()
                        .map(|t| format!("`{t}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
        }
        for section in &self.sections {
            self.resolve(&section.id)?;
        }
        Ok(())
    }

    pub fn section(&self, id: &str) -> Option<&Section> {
        self.sections.iter().find(|s| s.id == id)
    }

    /// The section's tier and policy with every `extends` applied.
    pub fn resolve(&self, id: &str) -> Result<ResolvedSection, String> {
        let mut chain: Vec<&Section> = Vec::new();
        let mut current = Some(id.to_string());
        while let Some(name) = current {
            if chain.iter().any(|s| s.id == name) {
                return Err(format!("the section `{name}` extends itself"));
            }
            let Some(section) = self.section(&name) else {
                let known: Vec<String> = self
                    .sections
                    .iter()
                    .map(|s| format!("`{}`", s.id))
                    .collect();
                return Err(if chain.is_empty() {
                    format!(
                        "there is no section `{name}` in this course; the sections are {}",
                        known.join(", ")
                    )
                } else {
                    format!(
                        "the section `{}` extends `{name}`, which does not exist",
                        chain.last().map(|s| s.id.as_str()).unwrap_or(id)
                    )
                });
            };
            chain.push(section);
            current = section.extends.clone();
        }
        // Apply from the root of the chain down to the requested section.
        let mut policy = Policy::default();
        let mut tier = None;
        for section in chain.iter().rev() {
            let mut next = section.policy.clone();
            next.extend_from(&policy);
            policy = next;
            if section.tier.is_some() {
                tier = section.tier.clone();
            }
        }
        let section = chain[0];
        policy.section = Some(if section.title.is_empty() {
            section.id.clone()
        } else {
            section.title.clone()
        });
        Ok(ResolvedSection {
            id: section.id.clone(),
            title: section.title.clone(),
            description: section.description.clone(),
            tier,
            policy,
        })
    }
}

/// Every tactic in a script with the place it was written, including
/// tactics inside case arms, `have` blocks and `calc` steps.
pub fn tactic_uses(tactics: &[Tactic]) -> Vec<(&'static str, Span)> {
    fn walk(tactics: &[Tactic], out: &mut Vec<(&'static str, Span)>) {
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
                TacticKind::Cases { .. } => "cases",
                TacticKind::Exists(_) => "exists",
                TacticKind::Refl => "refl",
                TacticKind::Rewrite { .. } => "rewrite",
                TacticKind::Unfold(..) => "unfold",
                TacticKind::Simp { .. } => "simp",
                TacticKind::Induction { .. } => "induction",
                TacticKind::Exfalso => "exfalso",
                TacticKind::Contradiction => "contradiction",
                TacticKind::ByCases { .. } => "by_cases",
                TacticKind::ByContra(_) => "by_contra",
                TacticKind::ShowGoal => "show_goal",
                TacticKind::Sorry => "sorry",
                TacticKind::Have { .. } => "have",
                TacticKind::Show(_) => "show",
                TacticKind::Funext(_) => "funext",
                TacticKind::Obtain { .. } => "obtain",
                TacticKind::Calc { .. } => "calc",
            };
            out.push((name, tactic.span));
            match &tactic.kind {
                TacticKind::Cases { arms, .. } | TacticKind::Induction { arms, .. } => {
                    for arm in arms {
                        walk(&arm.body, out);
                    }
                }
                TacticKind::Have {
                    proof: HaveProof::Block(body),
                    ..
                } => walk(body, out),
                TacticKind::Calc { steps, .. } => {
                    for step in steps {
                        if let hol_syntax::CalcProof::Block(body) = &step.proof {
                            walk(body, out);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = Vec::new();
    walk(tactics, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn patterns_match_names_leaves_and_globs() {
        assert!(pattern_matches("add_comm", "add_comm"));
        assert!(pattern_matches("add_comm", "nat.add_comm"));
        assert!(pattern_matches("add_*", "add_zero_right"));
        assert!(pattern_matches("*_comm", "nat.mul_comm"));
        assert!(pattern_matches("nat.*", "nat.mul_comm"));
        assert!(pattern_matches("*", "anything"));
        assert!(!pattern_matches("add_*", "mul_comm"));
        assert!(!pattern_matches("add", "add_comm"));
    }

    #[test]
    fn sections_inherit_and_unlock() {
        let course = Course::parse(
            r#"{"title":"T","sections":[
              {"id":"a","tier":"fol","allow_tactics":["intro","exact"],"allow_theorems":[]},
              {"id":"b","extends":"a","allow_tactics":["split"],"allow_theorems":["and_*"],"deny_tactics":["simp"]},
              {"id":"c","extends":"b","tier":"fol_nat","title":"Induction"}
            ]}"#,
        )
        .unwrap();
        let c = course.resolve("c").unwrap();
        assert_eq!(c.tier.as_deref(), Some("fol_nat"));
        assert_eq!(c.policy.section.as_deref(), Some("Induction"));
        assert!(c.policy.tactic_problem("split").is_none());
        assert!(c.policy.tactic_problem("intro").is_none());
        assert!(c.policy.tactic_problem("sorry").is_none());
        assert!(c.policy.tactic_problem("cases").is_some());
        assert!(c.policy.tactic_problem("simp").is_some());
        assert!(c.policy.theorem_problem("and_comm").is_none());
        assert!(c.policy.theorem_problem("or_comm").is_some());
        let a = course.resolve("a").unwrap();
        assert!(a.policy.theorem_problem("and_comm").is_some());
    }

    #[test]
    fn course_files_reject_typos() {
        let unknown_tactic = r#"{"sections":[{"id":"a","allow_tactics":["intros"]}]}"#;
        assert!(Course::parse(unknown_tactic)
            .unwrap_err()
            .contains("unknown tactic `intros`"));
        let missing_parent = r#"{"sections":[{"id":"a","extends":"zero"}]}"#;
        assert!(Course::parse(missing_parent)
            .unwrap_err()
            .contains("extends `zero`, which does not exist"));
        let cycle = r#"{"sections":[{"id":"a","extends":"b"},{"id":"b","extends":"a"}]}"#;
        assert!(Course::parse(cycle).unwrap_err().contains("extends itself"));
        let bad_tier = r#"{"sections":[{"id":"a","tier":"zfc"}]}"#;
        assert!(Course::parse(bad_tier)
            .unwrap_err()
            .contains("unknown tier"));
    }

    #[test]
    fn independent_policies_combine_restrictively() {
        let mut flags = Policy {
            allow_tactics: Some(vec!["intro".into(), "exact".into(), "simp".into()]),
            ..Policy::default()
        };
        let manifest = Policy {
            deny_sorry: true,
            allow_tactics: Some(vec!["intro".into(), "simp".into(), "cases".into()]),
            deny_tactics: vec!["simp".into()],
            ..Policy::default()
        };
        flags.restrict_with(&manifest);
        assert!(flags.deny_sorry);
        assert!(flags.tactic_problem("intro").is_none());
        assert!(flags.tactic_problem("exact").is_some());
        assert!(flags.tactic_problem("cases").is_some());
        assert!(flags.tactic_problem("simp").is_some());
    }
}
