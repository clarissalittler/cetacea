//! Bounded, many-sorted first-order model search, separate from proof checking.
//! Only abstract object sorts and uninterpreted, fully applied symbols are
//! interpreted here. Definitions, arithmetic, datatypes, sets, and higher-order
//! binders are declined, never treated as independent propositional atoms.
//! Supported axioms constrain every candidate world; an unsupported axiom
//! disables this search. Exhaustion and unsupported input both return `None`,
//! which is not evidence of validity. Work limits are deterministic for Wasm.

use hol_elab::{Env, SymbolKind};
use hol_kernel::{Term, TermView, Type};

const MAX_SORTS: usize = 3;
const MAX_DOMAIN: usize = 3;
const MAX_SYMBOLS: usize = 12;
const MAX_CELLS: usize = 16;
const MAX_MODELS: usize = 32_768;
const MAX_STEPS: usize = 250_000;
const MAX_NODES: usize = 512;
const MAX_DEPTH: usize = 64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interpretation {
    pub symbol: Term,
    pub arguments: Vec<usize>,
    pub result: Option<usize>,
    pub values: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteModel {
    pub domains: Vec<(Type, usize)>,
    pub interpretations: Vec<Interpretation>,
}

impl FiniteModel {
    pub fn describe(&self) -> String {
        let domains = self
            .domains
            .iter()
            .map(|(sort, size)| {
                let elements = (0..*size).map(element).collect::<Vec<_>>().join(", ");
                format!(
                    "{sort} = {{{elements}}} ({size} element{})",
                    if *size == 1 { "" } else { "s" }
                )
            })
            .collect::<Vec<_>>()
            .join("; ");
        let symbols = self
            .interpretations
            .iter()
            .map(|entry| {
                let name = match entry.symbol.view() {
                    TermView::Free(name, _) | TermView::Const(name, _) => name.to_string(),
                    _ => unreachable!(),
                };
                if entry.arguments.is_empty() {
                    let value = if entry.result.is_some() {
                        element(entry.values[0])
                    } else {
                        (entry.values[0] == 1).to_string()
                    };
                    return format!("{name} : {} = {value}", entry.symbol.ty());
                }
                let rows = entry
                    .values
                    .iter()
                    .enumerate()
                    .filter_map(|(index, value)| {
                        if entry.result.is_none() && *value == 0 {
                            return None;
                        }
                        let mut remainder = index;
                        let mut tuple = Vec::new();
                        for sort in entry.arguments.iter().rev() {
                            let size = self.domains[*sort].1;
                            tuple.push(element(remainder % size));
                            remainder /= size;
                        }
                        tuple.reverse();
                        let tuple = format!("({})", tuple.join(", "));
                        Some(if entry.result.is_some() {
                            format!("{tuple} -> {}", element(*value))
                        } else {
                            tuple
                        })
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{name} : {} = {{{rows}}}", entry.symbol.ty())
            })
            .collect::<Vec<_>>()
            .join("; ");
        if symbols.is_empty() {
            domains
        } else {
            format!("{domains}; {symbols}. Unlisted predicate tuples are false")
        }
    }
}

fn element(index: usize) -> String {
    ((b'a' + index as u8) as char).to_string()
}

enum Object {
    Bound(usize),
    Call(usize, Vec<Object>),
}

enum Formula {
    Truth(bool),
    Atom(Object),
    Equal(Object, Object),
    Binary(Binary, Box<Formula>, Box<Formula>),
    Quantifier(bool, usize, Box<Formula>),
}

enum Binary {
    And,
    Or,
    Imp,
    Iff,
}

struct Compiler<'a> {
    env: &'a Env,
    sorts: Vec<Type>,
    symbols: Vec<Interpretation>,
    binders: Vec<Type>,
    remaining: usize,
}

impl Compiler<'_> {
    fn sort(&mut self, ty: &Type) -> Option<usize> {
        match ty {
            Type::Var(_) => {}
            Type::Con(name, args)
                if args.is_empty()
                    && !ty.is_prop()
                    && self.env.theory().signature().type_arity(name) == Some(0)
                    && self.env.theory().datatype(name.as_str()).is_none() => {}
            _ => return None,
        }
        if let Some(index) = self.sorts.iter().position(|sort| sort == ty) {
            return Some(index);
        }
        if self.sorts.len() >= MAX_SORTS {
            return None;
        }
        self.sorts.push(ty.clone());
        Some(self.sorts.len() - 1)
    }

    fn visit(&mut self, depth: usize) -> Option<()> {
        if depth > MAX_DEPTH {
            return None;
        }
        self.remaining = self.remaining.checked_sub(1)?;
        Some(())
    }

    fn object(&mut self, term: &Term, depth: usize) -> Option<Object> {
        self.visit(depth)?;
        if let TermView::Bound(index, ty) = term.view() {
            let position = self.binders.len().checked_sub(index as usize + 1)?;
            if &self.binders[position] != ty {
                return None;
            }
            self.sort(ty)?;
            return Some(Object::Bound(index as usize));
        }
        let (head, arguments) = term.strip_app();
        match head.view() {
            TermView::Free(..) => {}
            TermView::Const(name, _) => {
                let info = self.env.constant_by_exact_name(name)?;
                if !matches!(
                    info.kind,
                    SymbolKind::Const | SymbolKind::Func | SymbolKind::Pred
                ) {
                    return None;
                }
            }
            _ => return None,
        }
        let (domains, result) = head.ty().strip_fun();
        if domains.len() != arguments.len() || domains.len() > 3 {
            return None;
        }
        let sorts = domains
            .iter()
            .map(|ty| self.sort(ty))
            .collect::<Option<Vec<_>>>()?;
        let result = if result.is_prop() {
            None
        } else {
            Some(self.sort(result)?)
        };
        let index = match self.symbols.iter().position(|entry| &entry.symbol == head) {
            Some(index) => index,
            None => {
                if self.symbols.len() >= MAX_SYMBOLS {
                    return None;
                }
                self.symbols.push(Interpretation {
                    symbol: head.clone(),
                    arguments: sorts,
                    result,
                    values: Vec::new(),
                });
                self.symbols.len() - 1
            }
        };
        let arguments = arguments
            .into_iter()
            .map(|arg| self.object(arg, depth + 1))
            .collect::<Option<Vec<_>>>()?;
        Some(Object::Call(index, arguments))
    }

    fn formula(&mut self, term: &Term, depth: usize) -> Option<Formula> {
        self.visit(depth)?;
        if term.is_true() || term.is_false() {
            return Some(Formula::Truth(term.is_true()));
        }
        for (parts, connective) in [
            (term.dest_and(), Binary::And),
            (term.dest_or(), Binary::Or),
            (term.dest_imp(), Binary::Imp),
            (term.dest_iff(), Binary::Iff),
        ] {
            if let Some((left, right)) = parts {
                return Some(Formula::Binary(
                    connective,
                    Box::new(self.formula(left, depth + 1)?),
                    Box::new(self.formula(right, depth + 1)?),
                ));
            }
        }
        if let Some((left, right)) = term.dest_eq() {
            self.sort(left.ty())?;
            return Some(Formula::Equal(
                self.object(left, depth + 1)?,
                self.object(right, depth + 1)?,
            ));
        }
        for (predicate, universal) in [(term.dest_forall(), true), (term.dest_exists(), false)] {
            if let Some(predicate) = predicate {
                let TermView::Lam(_, ty, body) = predicate.view() else {
                    return None;
                };
                let sort = self.sort(ty)?;
                self.binders.push(ty.clone());
                let body = self.formula(body, depth + 1)?;
                self.binders.pop();
                return Some(Formula::Quantifier(universal, sort, Box::new(body)));
            }
        }
        if !term.ty().is_prop() {
            return None;
        }
        Some(Formula::Atom(self.object(term, depth + 1)?))
    }
}

struct Evaluator<'a> {
    model: &'a FiniteModel,
    bound: Vec<usize>,
    remaining: &'a mut usize,
}

impl Evaluator<'_> {
    fn object(&mut self, term: &Object) -> Option<usize> {
        *self.remaining = self.remaining.checked_sub(1)?;
        match term {
            Object::Bound(index) => self
                .bound
                .get(self.bound.len().checked_sub(index + 1)?)
                .copied(),
            Object::Call(symbol, arguments) => {
                let entry = &self.model.interpretations[*symbol];
                let mut index = 0;
                for (argument, sort) in arguments.iter().zip(&entry.arguments) {
                    index = index * self.model.domains[*sort].1 + self.object(argument)?;
                }
                entry.values.get(index).copied()
            }
        }
    }

    fn formula(&mut self, formula: &Formula) -> Option<bool> {
        *self.remaining = self.remaining.checked_sub(1)?;
        Some(match formula {
            Formula::Truth(value) => *value,
            Formula::Atom(atom) => self.object(atom)? == 1,
            Formula::Equal(left, right) => self.object(left)? == self.object(right)?,
            Formula::Binary(connective, left, right) => {
                let left = self.formula(left)?;
                match connective {
                    Binary::And => left && self.formula(right)?,
                    Binary::Or => left || self.formula(right)?,
                    Binary::Imp => !left || self.formula(right)?,
                    Binary::Iff => left == self.formula(right)?,
                }
            }
            Formula::Quantifier(universal, sort, body) => {
                let mut result = *universal;
                for value in 0..self.model.domains[*sort].1 {
                    self.bound.push(value);
                    let evaluated = self.formula(body)?;
                    self.bound.pop();
                    if evaluated != *universal {
                        result = evaluated;
                        break;
                    }
                }
                result
            }
        })
    }
}

pub fn first_order_countermodel(env: &Env, statement: &Term) -> Option<FiniteModel> {
    let mut compiler = Compiler {
        env,
        sorts: Vec::new(),
        symbols: Vec::new(),
        binders: Vec::new(),
        remaining: MAX_NODES,
    };
    let formula = compiler.formula(statement, 0)?;
    let mut constraints = Vec::new();
    for (_, axiom) in env
        .theory()
        .theorems()
        .filter(|(name, thm)| thm.tags().axioms.contains(*name))
    {
        let mut type_variables = std::collections::BTreeSet::new();
        axiom.concl().type_vars(&mut type_variables);
        if !type_variables.is_empty() {
            return None;
        }
        let mut closed = axiom.concl().clone();
        for (name, ty) in axiom.concl().free_vars() {
            compiler.sort(&ty)?;
            closed = Term::forall(&Term::free(name, ty), &closed).ok()?;
        }
        constraints.push(compiler.formula(&closed, 0)?);
    }
    if compiler.sorts.is_empty() {
        return None;
    }
    let mut remaining = MAX_STEPS;
    let mut models_left = MAX_MODELS;
    for largest in 1..=MAX_DOMAIN {
        for configuration in 0..largest.pow(compiler.sorts.len() as u32) {
            let mut code = configuration;
            let sizes: Vec<usize> = compiler
                .sorts
                .iter()
                .map(|_| {
                    let size = code % largest + 1;
                    code /= largest;
                    size
                })
                .collect();
            if !sizes.contains(&largest) {
                continue;
            }
            let mut model = FiniteModel {
                domains: compiler.sorts.iter().cloned().zip(sizes).collect(),
                interpretations: compiler.symbols.clone(),
            };
            let mut cells = Vec::new();
            for (symbol, entry) in model.interpretations.iter_mut().enumerate() {
                let count: usize = entry
                    .arguments
                    .iter()
                    .map(|sort| model.domains[*sort].1)
                    .product();
                let radix = entry.result.map(|sort| model.domains[sort].1).unwrap_or(2);
                entry.values = vec![0; count];
                for index in 0..count {
                    cells.push((symbol, index, radix));
                }
            }
            if cells.len() > MAX_CELLS {
                continue;
            }
            loop {
                models_left = models_left.checked_sub(1)?;
                let mut evaluator = Evaluator {
                    model: &model,
                    bound: Vec::new(),
                    remaining: &mut remaining,
                };
                let mut consistent = true;
                for constraint in &constraints {
                    if !evaluator.formula(constraint)? {
                        consistent = false;
                        break;
                    }
                }
                if consistent && !evaluator.formula(&formula)? {
                    return Some(model);
                }
                let mut advanced = false;
                for (symbol, index, radix) in &cells {
                    let value = &mut model.interpretations[*symbol].values[*index];
                    *value += 1;
                    if *value < *radix {
                        advanced = true;
                        break;
                    }
                    *value = 0;
                }
                if !advanced {
                    break;
                }
            }
        }
    }
    None
}

pub fn propositional_countermodel(
    env: &Env,
    statement: &Term,
) -> Option<hol_feedback::Countermodel> {
    fn pure(term: &Term, depth: usize) -> bool {
        if depth > MAX_DEPTH {
            return false;
        }
        if term.is_true() || term.is_false() {
            return true;
        }
        if let Some((left, right)) = [
            term.dest_and(),
            term.dest_or(),
            term.dest_imp(),
            term.dest_iff(),
        ]
        .into_iter()
        .flatten()
        .next()
        {
            return pure(left, depth + 1) && pure(right, depth + 1);
        }
        matches!(term.view(), TermView::Free(_, ty) if ty.is_prop())
    }
    if env
        .theory()
        .theorems()
        .any(|(_, thm)| !thm.tags().axioms.is_empty())
        || !pure(statement, 0)
    {
        return None;
    }
    hol_feedback::propositional_countermodel(statement, &|term| hol_elab::print_term(env, term))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evaluation_stops_when_its_shared_budget_runs_out() {
        let model = FiniteModel {
            domains: vec![(Type::var("U"), 3)],
            interpretations: vec![],
        };
        let formula = Formula::Quantifier(true, 0, Box::new(Formula::Truth(true)));
        let mut remaining = 2;
        let mut evaluator = Evaluator {
            model: &model,
            bound: Vec::new(),
            remaining: &mut remaining,
        };
        assert_eq!(evaluator.formula(&formula), None);
        assert_eq!(remaining, 0);
    }
}
