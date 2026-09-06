//! Feedback beyond "the proof failed": countermodels for false
//! statements. A false statement has no proof, and the most useful thing
//! a checker can say is why.
//!
//! This milestone covers propositional statements: formulas built from
//! `True`, `False`, proposition variables, applied predicates over
//! variables (treated as atoms), and the connectives. A statement or an
//! open goal is checked against every assignment of its atoms, and the
//! first falsifying assignment is reported.

use std::collections::BTreeMap;

use hol_kernel::{Term, TermView};

/// A propositional countermodel: an assignment of truth values to atoms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Countermodel {
    pub assignment: Vec<(String, bool)>,
}

impl Countermodel {
    /// `P = false, Q = true`.
    pub fn describe(&self) -> String {
        if self.assignment.is_empty() {
            return "under every assignment".to_string();
        }
        self.assignment
            .iter()
            .map(|(name, value)| format!("{name} = {value}"))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

const MAX_ATOMS: usize = 12;

/// The propositional skeleton of a term, if it has one.
enum Prop {
    True,
    False,
    Atom(usize),
    Not(Box<Prop>),
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
    Imp(Box<Prop>, Box<Prop>),
    Iff(Box<Prop>, Box<Prop>),
}

struct Atoms {
    names: Vec<String>,
    index: BTreeMap<Term, usize>,
}

impl Atoms {
    fn intern(&mut self, term: &Term, display: String) -> Option<usize> {
        if let Some(&index) = self.index.get(term) {
            return Some(index);
        }
        if self.names.len() >= MAX_ATOMS {
            return None;
        }
        let index = self.names.len();
        self.names.push(display);
        self.index.insert(term.clone(), index);
        Some(index)
    }
}

fn skeleton(term: &Term, atoms: &mut Atoms, display: &dyn Fn(&Term) -> String) -> Option<Prop> {
    if term.is_true() {
        return Some(Prop::True);
    }
    if term.is_false() {
        return Some(Prop::False);
    }
    if let Some(p) = term.dest_not() {
        return Some(Prop::Not(Box::new(skeleton(p, atoms, display)?)));
    }
    if let Some((a, b)) = term.dest_and() {
        return Some(Prop::And(
            Box::new(skeleton(a, atoms, display)?),
            Box::new(skeleton(b, atoms, display)?),
        ));
    }
    if let Some((a, b)) = term.dest_or() {
        return Some(Prop::Or(
            Box::new(skeleton(a, atoms, display)?),
            Box::new(skeleton(b, atoms, display)?),
        ));
    }
    if let Some((a, b)) = term.dest_imp() {
        return Some(Prop::Imp(
            Box::new(skeleton(a, atoms, display)?),
            Box::new(skeleton(b, atoms, display)?),
        ));
    }
    if let Some((a, b)) = term.dest_iff() {
        return Some(Prop::Iff(
            Box::new(skeleton(a, atoms, display)?),
            Box::new(skeleton(b, atoms, display)?),
        ));
    }
    // Atoms: proposition variables and predicate applications whose
    // arguments contain no quantifiers or lambdas. Equalities and
    // quantified formulas are not propositional.
    if term.dest_eq().is_some() || term.dest_forall().is_some() || term.dest_exists().is_some() {
        return None;
    }
    if !term.ty().is_prop() || !term.is_closed() {
        return None;
    }
    let (head, args) = term.strip_app();
    let head_ok = matches!(head.view(), TermView::Free(..) | TermView::Const(..));
    if !head_ok || args.iter().any(|a| a.is_lam() || !a.is_closed()) {
        return None;
    }
    // Arithmetic atoms are not independent of each other; leave them to
    // the arithmetic search.
    if args.iter().any(|a| is_interpreted(a)) {
        return None;
    }
    let index = atoms.intern(term, display(term))?;
    Some(Prop::Atom(index))
}

/// Terms over `Nat` have interpreted structure.
fn is_interpreted(t: &Term) -> bool {
    matches!(t.ty(), hol_kernel::Type::Con(name, _) if name.as_str() == "Nat")
}

fn eval(prop: &Prop, row: u32) -> bool {
    match prop {
        Prop::True => true,
        Prop::False => false,
        Prop::Atom(i) => row & (1 << i) != 0,
        Prop::Not(p) => !eval(p, row),
        Prop::And(a, b) => eval(a, row) && eval(b, row),
        Prop::Or(a, b) => eval(a, row) || eval(b, row),
        Prop::Imp(a, b) => !eval(a, row) || eval(b, row),
        Prop::Iff(a, b) => eval(a, row) == eval(b, row),
    }
}

/// A falsifying assignment for a propositional statement, or `None` when
/// the statement is a tautology or is not propositional.
pub fn propositional_countermodel(
    term: &Term,
    display: &dyn Fn(&Term) -> String,
) -> Option<Countermodel> {
    let mut atoms = Atoms {
        names: Vec::new(),
        index: BTreeMap::new(),
    };
    let prop = skeleton(term, &mut atoms, display)?;
    let count = atoms.names.len();
    for row in 0..(1u32 << count) {
        if !eval(&prop, row) {
            return Some(Countermodel {
                assignment: atoms
                    .names
                    .iter()
                    .enumerate()
                    .map(|(i, name)| (name.clone(), row & (1 << i) != 0))
                    .collect(),
            });
        }
    }
    None
}

/// The countermodel of `hyps -> target`, for an open goal.
pub fn goal_countermodel(
    hyps: &[Term],
    target: &Term,
    display: &dyn Fn(&Term) -> String,
) -> Option<Countermodel> {
    let mut formula = target.clone();
    for hyp in hyps.iter().rev() {
        formula = Term::imp(hyp, &formula).ok()?;
    }
    propositional_countermodel(&formula, display)
}
