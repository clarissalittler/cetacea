//! Goals and the proof state.
//!
//! A goal is a context (eigenvariables and named hypotheses) and a
//! target. A tactic replaces the current goal by subgoals together with a
//! justification: a function from the subgoals' theorems to the goal's
//! theorem. The proof state keeps the tree of justifications and the
//! list of open goals; finishing the tree runs every justification
//! through the kernel.

use std::collections::BTreeSet;

use hol_kernel::{Name, Tags, Term, Thm};
use hol_syntax::Span;

#[derive(Clone, Debug)]
pub struct Goal {
    pub id: u64,
    /// Eigenvariables introduced so far, in order.
    pub vars: Vec<Term>,
    /// Named hypotheses, in order of introduction.
    pub hyps: Vec<(Name, Term)>,
    pub target: Term,
}

impl Goal {
    pub fn hyp(&self, name: &str) -> Option<&Term> {
        self.hyps
            .iter()
            .rev()
            .find(|(n, _)| n.as_str() == name)
            .map(|(_, t)| t)
    }

    pub fn has_var(&self, name: &str) -> bool {
        self.vars.iter().any(|v| {
            v.as_free()
                .map(|(n, _)| n.as_str() == name)
                .unwrap_or(false)
        })
    }

    /// True when `name` is already a hypothesis or variable name.
    pub fn name_in_use(&self, name: &str) -> bool {
        self.hyp(name).is_some() || self.has_var(name)
    }

    /// Every name that a fresh binder must avoid.
    pub fn taken_names(&self) -> BTreeSet<Name> {
        let mut names: BTreeSet<Name> = self.target.free_var_names();
        for (name, hyp) in &self.hyps {
            names.insert(name.clone());
            names.extend(hyp.free_var_names());
        }
        for var in &self.vars {
            if let Some((n, _)) = var.as_free() {
                names.insert(n.clone());
            }
        }
        names
    }

    pub fn hyp_formulas(&self) -> Vec<Term> {
        self.hyps.iter().map(|(_, t)| t.clone()).collect()
    }
}

pub type Justification = Box<dyn Fn(&[Thm]) -> hol_kernel::Result<Thm>>;

enum Node {
    Open(u64),
    Closed {
        just: Justification,
        children: Vec<Node>,
        /// The tactic that closed this goal.
        span: Span,
    },
}

/// What the kernel did on behalf of one tactic: the primitive rules it
/// ran and any trust tags that first appear at it.
///
/// A tactic works in two phases, and both are recorded. While it runs,
/// it may build theorems directly (instantiating a cited theorem,
/// rewriting, simplifying); those entries have no `concl`. When the
/// proof is finished, each node of the proof tree runs its
/// justification; those entries carry the node's conclusion.
///
/// This is a recording for explanations and diagnostics. It plays no
/// part in checking. Rules a tactic tried on the way to an answer are
/// listed too, so it shows what the tactic did, not a minimal proof.
#[derive(Clone, Debug)]
pub struct DerivationStep {
    pub span: Span,
    /// How many times each primitive rule ran, in order of first use.
    pub rules: hol_kernel::record::RuleCounts,
    /// The theorem a proof-tree node established, when this entry is one.
    pub concl: Option<Term>,
    /// Tags on this node's theorem that none of its subproofs carried:
    /// where `classical`, `sorry`, or an axiom entered the proof.
    pub introduced: Tags,
}

fn tags_minus(all: &Tags, known: &Tags) -> Tags {
    Tags {
        classical: all.classical && !known.classical,
        sorry: all.sorry && !known.sorry,
        axioms: all.axioms.difference(&known.axioms).cloned().collect(),
        datatypes: all
            .datatypes
            .difference(&known.datatypes)
            .cloned()
            .collect(),
    }
}

enum FinishError {
    Open(u64),
    Kernel(String),
}

fn finish_node(node: &Node, trace: &mut Option<Vec<DerivationStep>>) -> Result<Thm, FinishError> {
    match node {
        Node::Open(id) => Err(FinishError::Open(*id)),
        Node::Closed {
            just,
            children,
            span,
        } => {
            let thms = children
                .iter()
                .map(|child| finish_node(child, trace))
                .collect::<Result<Vec<_>, FinishError>>()?;
            let Some(steps) = trace else {
                return just(&thms).map_err(|e| FinishError::Kernel(e.to_string()));
            };
            let enclosing = hol_kernel::record::start();
            let result = just(&thms);
            let rules = hol_kernel::record::finish(enclosing);
            let thm = result.map_err(|e| FinishError::Kernel(e.to_string()))?;
            let known = thms
                .iter()
                .fold(Tags::none(), |acc, child| acc.union(child.tags()));
            steps.push(DerivationStep {
                span: *span,
                rules,
                concl: Some(thm.concl().clone()),
                introduced: tags_minus(thm.tags(), &known),
            });
            Ok(thm)
        }
    }
}

/// Replaces the open leaf `id` by `replacement`. Returns the replacement
/// back when the leaf was not found under `node`.
fn replace_in(node: &mut Node, id: u64, replacement: Node) -> Option<Node> {
    match node {
        Node::Open(open) if *open == id => {
            *node = replacement;
            None
        }
        Node::Open(_) => Some(replacement),
        Node::Closed { children, .. } => {
            let mut pending = Some(replacement);
            for child in children.iter_mut() {
                let Some(current) = pending.take() else {
                    break;
                };
                pending = replace_in(child, id, current);
            }
            pending
        }
    }
}

pub struct ProofState {
    root: Node,
    /// Open goals, current goal first.
    pub goals: Vec<Goal>,
    next_id: u64,
    /// The last kernel error from a justification, for diagnostics.
    pub last_kernel_error: Option<String>,
    /// The tactic currently running; nodes closed now belong to it.
    pub at: Span,
    /// Whether to record what the kernel does. Off for imported files,
    /// whose derivations nobody will look at.
    pub recording: bool,
    /// The recording made by the last successful [`ProofState::finish`],
    /// in the order the kernel built the theorems (subproofs first).
    pub derivation: Vec<DerivationStep>,
}

impl ProofState {
    pub fn new(mut goal: Goal) -> ProofState {
        goal.id = 1;
        ProofState {
            root: Node::Open(1),
            goals: vec![goal],
            next_id: 2,
            last_kernel_error: None,
            at: Span::default(),
            recording: true,
            derivation: Vec::new(),
        }
    }

    pub fn current(&self) -> Option<&Goal> {
        self.goals.first()
    }

    pub fn open_count(&self) -> usize {
        self.goals.len()
    }

    pub fn is_open(&self, id: u64) -> bool {
        self.goals.iter().any(|g| g.id == id)
    }

    /// Closes goal `id` with subgoals and a justification. Subgoals take
    /// the goal's place at the front of the open list.
    pub fn close(&mut self, id: u64, mut subgoals: Vec<Goal>, just: Justification) {
        for goal in subgoals.iter_mut() {
            goal.id = self.next_id;
            self.next_id += 1;
        }
        let children = subgoals.iter().map(|g| Node::Open(g.id)).collect();
        let replacement = Node::Closed {
            just,
            children,
            span: self.at,
        };
        let leftover = replace_in(&mut self.root, id, replacement);
        debug_assert!(leftover.is_none(), "closed a goal that was not open");
        let position = self.goals.iter().position(|g| g.id == id).unwrap_or(0);
        self.goals.remove(position);
        for (offset, goal) in subgoals.into_iter().enumerate() {
            self.goals.insert(position + offset, goal);
        }
    }

    /// Runs every justification. Errors with the id of an open goal, or
    /// with `None` after recording a kernel error.
    pub fn finish(&mut self) -> Result<Thm, Option<u64>> {
        let mut trace = self.recording.then(Vec::new);
        match finish_node(&self.root, &mut trace) {
            Ok(thm) => {
                self.derivation = trace.unwrap_or_default();
                Ok(thm)
            }
            Err(FinishError::Open(id)) => Err(Some(id)),
            Err(FinishError::Kernel(message)) => {
                self.last_kernel_error = Some(message);
                Err(None)
            }
        }
    }
}
