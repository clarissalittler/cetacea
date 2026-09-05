//! Theorems and trust tags.
//!
//! A `Thm` can only be constructed inside this crate, by the primitive
//! rules in [`crate::rules`] and the definitional principles in
//! [`crate::Theory`]. Tags record everything a theorem depends on beyond
//! the intuitionistic core: classical reasoning, `sorry`, user axioms,
//! and datatype packages. Tags propagate by union through every rule.

use std::collections::BTreeSet;
use std::fmt;

use crate::name::Name;
use crate::term::Term;

#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct Tags {
    pub classical: bool,
    pub sorry: bool,
    pub axioms: BTreeSet<Name>,
    pub datatypes: BTreeSet<Name>,
}

impl Tags {
    pub fn none() -> Tags {
        Tags::default()
    }

    pub fn classical() -> Tags {
        Tags {
            classical: true,
            ..Tags::default()
        }
    }

    pub fn sorry() -> Tags {
        Tags {
            sorry: true,
            ..Tags::default()
        }
    }

    pub fn axiom(name: impl Into<Name>) -> Tags {
        let mut tags = Tags::default();
        tags.axioms.insert(name.into());
        tags
    }

    pub fn datatype(name: impl Into<Name>) -> Tags {
        let mut tags = Tags::default();
        tags.datatypes.insert(name.into());
        tags
    }

    pub fn is_empty(&self) -> bool {
        !self.classical && !self.sorry && self.axioms.is_empty() && self.datatypes.is_empty()
    }

    pub fn union(&self, other: &Tags) -> Tags {
        if other.is_empty() {
            return self.clone();
        }
        if self.is_empty() {
            return other.clone();
        }
        Tags {
            classical: self.classical || other.classical,
            sorry: self.sorry || other.sorry,
            axioms: self.axioms.union(&other.axioms).cloned().collect(),
            datatypes: self.datatypes.union(&other.datatypes).cloned().collect(),
        }
    }
}

impl fmt::Display for Tags {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts: Vec<String> = Vec::new();
        if self.classical {
            parts.push("classical".to_string());
        }
        if self.sorry {
            parts.push("sorry".to_string());
        }
        for axiom in &self.axioms {
            parts.push(format!("axiom {axiom}"));
        }
        for datatype in &self.datatypes {
            parts.push(format!("datatype {datatype}"));
        }
        f.write_str(&parts.join(", "))
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Thm {
    hyps: Vec<Term>,
    concl: Term,
    tags: Tags,
}

impl Thm {
    /// Crate-private constructor. Hypotheses are kept sorted and
    /// duplicate-free so that hypothesis sets compare structurally.
    pub(crate) fn new(mut hyps: Vec<Term>, concl: Term, tags: Tags) -> Thm {
        debug_assert!(concl.ty().is_prop());
        debug_assert!(concl.is_closed());
        hyps.sort();
        hyps.dedup();
        Thm { hyps, concl, tags }
    }

    pub fn hyps(&self) -> &[Term] {
        &self.hyps
    }

    pub fn concl(&self) -> &Term {
        &self.concl
    }

    pub fn tags(&self) -> &Tags {
        &self.tags
    }

    pub fn has_hyp(&self, hyp: &Term) -> bool {
        self.hyps.binary_search(hyp).is_ok()
    }

    /// Hypotheses with `discharged` removed.
    pub(crate) fn hyps_without(&self, discharged: &Term) -> Vec<Term> {
        self.hyps
            .iter()
            .filter(|hyp| *hyp != discharged)
            .cloned()
            .collect()
    }

    pub(crate) fn merged_hyps(parts: &[&[Term]]) -> Vec<Term> {
        let mut out: Vec<Term> = parts.iter().flat_map(|part| part.iter().cloned()).collect();
        out.sort();
        out.dedup();
        out
    }

    /// True when `var` occurs free in some hypothesis.
    pub fn var_in_hyps(&self, var: &Term) -> bool {
        self.hyps.iter().any(|hyp| hyp.contains_var(var))
    }
}
