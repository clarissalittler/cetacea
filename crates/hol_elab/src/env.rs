//! The checking environment: the kernel theory plus the symbol tables
//! the elaborator needs (sorts, constants with their surface arity and
//! kind, definitions, theorems) and the current tier, mode, and
//! namespace.

use std::collections::BTreeMap;

use hol_kernel::{Name, Term, Theory, Thm, Type};
use hol_syntax::{Mode, Span, Tier};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymbolKind {
    /// `const c : T`.
    Const,
    /// `func f : A -> B`.
    Func,
    /// `pred P(A, B)`.
    Pred,
    /// `def name ... := body`.
    Def,
    /// A datatype constructor.
    Ctor,
    /// A built-in set or arithmetic operation.
    Builtin,
}

impl SymbolKind {
    pub fn describe(self) -> &'static str {
        match self {
            SymbolKind::Const => "constant",
            SymbolKind::Func => "function",
            SymbolKind::Pred => "predicate",
            SymbolKind::Def => "definition",
            SymbolKind::Ctor => "constructor",
            SymbolKind::Builtin => "built-in operation",
        }
    }
}

#[derive(Clone, Debug)]
pub struct ConstInfo {
    pub name: Name,
    /// The declared generic type, with type variables for type parameters.
    pub ty: Type,
    pub kind: SymbolKind,
    /// Number of surface arguments, for `f(a, b)` syntax and arity errors.
    pub arity: usize,
    pub span: Option<Span>,
}

#[derive(Clone, Debug)]
pub struct DefInfo {
    pub name: Name,
    pub type_params: Vec<Name>,
    pub params: Vec<(Name, Type)>,
    pub result: Type,
    /// `|- c = fun params => body`.
    pub equation: Thm,
    pub is_formula: bool,
    pub span: Option<Span>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParamInfo {
    /// `(A : Type)`: a type variable of the statement.
    TypeVar(Name),
    /// `(x : A)`, `(P : Prop)`, `(R : A -> A -> Prop)`: a free variable.
    Var(Name, Type),
    /// `(h : P)`: a hypothesis, folded into the statement as a premise.
    Hyp(Name, Term),
}

impl ParamInfo {
    pub fn name(&self) -> &Name {
        match self {
            ParamInfo::TypeVar(name) | ParamInfo::Var(name, _) | ParamInfo::Hyp(name, _) => name,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Accepted,
    Incomplete,
    Axiom,
}

#[derive(Clone, Debug)]
pub struct TheoremInfo {
    pub name: Name,
    pub params: Vec<ParamInfo>,
    /// The closed statement, whose free variables are the parameters.
    pub statement: Term,
    pub thm: Thm,
    pub status: Status,
    pub is_imported: bool,
    pub span: Option<Span>,
}

impl TheoremInfo {
    pub fn type_params(&self) -> Vec<Name> {
        self.params
            .iter()
            .filter_map(|p| match p {
                ParamInfo::TypeVar(name) => Some(name.clone()),
                _ => None,
            })
            .collect()
    }

    pub fn term_params(&self) -> Vec<(Name, Type)> {
        self.params
            .iter()
            .filter_map(|p| match p {
                ParamInfo::Var(name, ty) => Some((name.clone(), ty.clone())),
                _ => None,
            })
            .collect()
    }
}

#[derive(Clone, Debug)]
pub struct Env {
    theory: Theory,
    sorts: BTreeMap<Name, usize>,
    consts: BTreeMap<Name, ConstInfo>,
    defs: BTreeMap<Name, DefInfo>,
    theorems: BTreeMap<Name, TheoremInfo>,
    theorem_order: Vec<Name>,
    /// Defining equations of recursive functions, by function name.
    equations: BTreeMap<Name, Vec<Thm>>,
    pub tier: Tier,
    pub mode: Mode,
    namespace: Vec<String>,
    /// Names declared by the current file, in order, for status reporting.
    pub local_declarations: Vec<Name>,
    /// Whether declarations being added come from an import.
    pub importing: bool,
    counter: u64,
}

impl Env {
    /// An environment over the base kernel theory. Call
    /// [`crate::prelude::install`] to add sets and pairs.
    pub fn bare() -> Env {
        Env {
            theory: Theory::new(),
            sorts: BTreeMap::new(),
            consts: BTreeMap::new(),
            defs: BTreeMap::new(),
            theorems: BTreeMap::new(),
            theorem_order: Vec::new(),
            equations: BTreeMap::new(),
            tier: Tier::Fol,
            mode: Mode::Constructive,
            namespace: Vec::new(),
            local_declarations: Vec::new(),
            importing: false,
            counter: 0,
        }
    }

    pub fn theory(&self) -> &Theory {
        &self.theory
    }

    pub fn theory_mut(&mut self) -> &mut Theory {
        &mut self.theory
    }

    pub fn fresh_id(&mut self) -> u64 {
        self.counter += 1;
        self.counter
    }

    // ---- namespaces ----

    pub fn push_namespace(&mut self, name: &str) {
        self.namespace.push(name.to_string());
    }

    pub fn pop_namespace(&mut self) -> Option<String> {
        self.namespace.pop()
    }

    pub fn current_namespace(&self) -> Option<String> {
        if self.namespace.is_empty() {
            None
        } else {
            Some(self.namespace.join("."))
        }
    }

    /// The fully qualified name for a declaration made now.
    pub fn qualify(&self, name: &str) -> Name {
        match self.current_namespace() {
            Some(ns) => Name::new(&format!("{ns}.{name}")),
            None => Name::new(name),
        }
    }

    /// Candidate qualified names for a reference, innermost namespace
    /// first, ending with the bare name.
    fn candidates(&self, name: &str) -> Vec<Name> {
        let mut out = Vec::new();
        for depth in (1..=self.namespace.len()).rev() {
            out.push(Name::new(&format!(
                "{}.{name}",
                self.namespace[..depth].join(".")
            )));
        }
        out.push(Name::new(name));
        out
    }

    fn resolve<'a, V>(&self, table: &'a BTreeMap<Name, V>, name: &str) -> Option<(Name, &'a V)> {
        for candidate in self.candidates(name) {
            if let Some(value) = table.get(&candidate) {
                return Some((candidate, value));
            }
        }
        None
    }

    // ---- sorts ----

    pub fn sort(&self, name: &str) -> Option<(Name, usize)> {
        self.resolve(&self.sorts, name).map(|(n, a)| (n, *a))
    }

    pub fn add_sort(&mut self, name: Name, arity: usize) {
        self.sorts.insert(name, arity);
    }

    pub fn sorts(&self) -> impl Iterator<Item = (&Name, usize)> {
        self.sorts.iter().map(|(n, a)| (n, *a))
    }

    // ---- constants ----

    pub fn constant(&self, name: &str) -> Option<&ConstInfo> {
        self.resolve(&self.consts, name).map(|(_, c)| c)
    }

    pub fn constant_by_exact_name(&self, name: &Name) -> Option<&ConstInfo> {
        self.consts.get(name)
    }

    pub fn add_constant(&mut self, info: ConstInfo) {
        self.consts.insert(info.name.clone(), info);
    }

    pub fn constants(&self) -> impl Iterator<Item = &ConstInfo> {
        self.consts.values()
    }

    // ---- definitions ----

    pub fn def(&self, name: &str) -> Option<&DefInfo> {
        self.resolve(&self.defs, name).map(|(_, d)| d)
    }

    pub fn def_by_exact_name(&self, name: &Name) -> Option<&DefInfo> {
        self.defs.get(name)
    }

    pub fn add_def(&mut self, info: DefInfo) {
        self.defs.insert(info.name.clone(), info);
    }

    pub fn defs(&self) -> impl Iterator<Item = &DefInfo> {
        self.defs.values()
    }

    // ---- recursive function equations ----

    pub fn add_equations(&mut self, name: Name, thms: Vec<Thm>) {
        self.equations.insert(name, thms);
    }

    pub fn equations(&self, name: &Name) -> Option<&[Thm]> {
        self.equations.get(name).map(|v| v.as_slice())
    }

    pub fn all_equations(&self) -> impl Iterator<Item = &Thm> {
        self.equations.values().flatten()
    }

    // ---- theorems ----

    pub fn theorem(&self, name: &str) -> Option<&TheoremInfo> {
        self.resolve(&self.theorems, name).map(|(_, t)| t)
    }

    pub fn has_theorem_exact(&self, name: &Name) -> bool {
        self.theorems.contains_key(name)
    }

    pub fn add_theorem(&mut self, info: TheoremInfo) {
        if !self.theorems.contains_key(&info.name) {
            self.theorem_order.push(info.name.clone());
        }
        self.theorems.insert(info.name.clone(), info);
    }

    /// Theorems in declaration order.
    pub fn theorems(&self) -> impl Iterator<Item = &TheoremInfo> {
        self.theorem_order
            .iter()
            .filter_map(move |name| self.theorems.get(name))
    }

    /// True when `name` is an imported theorem that a local declaration
    /// may shadow: a file's own names win over the library's.
    pub fn is_shadowable_theorem(&self, name: &Name) -> bool {
        !self.importing
            && self
                .theorems
                .get(name)
                .map(|t| t.is_imported)
                .unwrap_or(false)
    }

    /// True when a name is taken by any declaration kind.
    pub fn name_taken(&self, name: &Name) -> Option<&'static str> {
        if self.sorts.contains_key(name) {
            Some("a sort")
        } else if let Some(c) = self.consts.get(name) {
            Some(match c.kind {
                SymbolKind::Const => "a constant",
                SymbolKind::Func => "a function",
                SymbolKind::Pred => "a predicate",
                SymbolKind::Def => "a definition",
                SymbolKind::Ctor => "a constructor",
                SymbolKind::Builtin => "a built-in operation",
            })
        } else if self.theorems.contains_key(name) {
            Some("a theorem")
        } else {
            None
        }
    }

    pub fn note_declaration(&mut self, name: Name) {
        if !self.importing {
            self.local_declarations.push(name);
        }
    }
}
