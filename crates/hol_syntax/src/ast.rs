//! The concrete syntax tree. Every node carries a [`Span`].

use crate::lexer::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

impl Ident {
    pub fn new(name: &str, span: Span) -> Ident {
        Ident {
            name: name.to_string(),
            span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeExpr {
    /// A named type applied to arguments: `Person`, `Set T`, `Prod T U`,
    /// `Prop`, `Type`.
    Named(Ident, Vec<TypeExpr>, Span),
    Fun(Box<TypeExpr>, Box<TypeExpr>, Span),
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named(_, _, span) | TypeExpr::Fun(_, _, span) => *span,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinderKind {
    Forall,
    Exists,
    Fun,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binder {
    pub names: Vec<Ident>,
    pub ty: Option<TypeExpr>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    And,
    Or,
    Imp,
    Iff,
    Eq,
    Mem,
    Subset,
    Add,
    Mul,
    Sub,
    Le,
    Lt,
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::And => "/\\",
            BinOp::Or => "\\/",
            BinOp::Imp => "->",
            BinOp::Iff => "<->",
            BinOp::Eq => "=",
            BinOp::Mem => "in",
            BinOp::Subset => "subset",
            BinOp::Add => "+",
            BinOp::Mul => "*",
            BinOp::Sub => "-",
            BinOp::Le => "<=",
            BinOp::Lt => "<",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Var(Ident),
    Num(u64, Span),
    True(Span),
    False(Span),
    /// `f(a, b)`.
    App(Box<Expr>, Vec<Expr>, Span),
    /// `empty(T)` and `univ(T)`: a constant indexed by a type.
    TypeApp(Ident, TypeExpr, Span),
    Binder(BinderKind, Vec<Binder>, Box<Expr>, Span),
    Not(Box<Expr>, Span),
    Binary(BinOp, Box<Expr>, Box<Expr>, Span),
    /// `{a, b, c}`.
    SetLit(Vec<Expr>, Span),
    /// `{ x : T | P }`.
    SetBuilder(Ident, TypeExpr, Box<Expr>, Span),
}

impl Expr {
    pub fn span(&self) -> Span {
        match self {
            Expr::Var(ident) => ident.span,
            Expr::Num(_, span)
            | Expr::True(span)
            | Expr::False(span)
            | Expr::App(_, _, span)
            | Expr::TypeApp(_, _, span)
            | Expr::Binder(_, _, _, span)
            | Expr::Not(_, span)
            | Expr::Binary(_, _, _, span)
            | Expr::SetLit(_, span)
            | Expr::SetBuilder(_, _, _, span) => *span,
        }
    }
}

/// A parameter annotation that may read as a type or as a formula:
/// `(x : A)` versus `(h : P)`. The elaborator decides.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Annotation {
    /// `(A : Type)`.
    TypeKind(Span),
    /// Parsed as a type; `formula` holds the same text read as a formula
    /// when that also parses.
    Type(TypeExpr, Option<Expr>),
    /// Only parses as a formula.
    Formula(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub names: Vec<Ident>,
    pub annotation: Annotation,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Constructive,
    Classical,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Tier {
    Fol,
    FolNat,
    Hol,
}

impl Tier {
    pub fn name(self) -> &'static str {
        match self {
            Tier::Fol => "fol",
            Tier::FolNat => "fol_nat",
            Tier::Hol => "hol",
        }
    }

    pub fn parse(name: &str) -> Option<Tier> {
        match name {
            "fol" => Some(Tier::Fol),
            "fol_nat" | "fol+nat" | "nat" => Some(Tier::FolNat),
            "hol" => Some(Tier::Hol),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CtorDecl {
    pub name: Ident,
    pub args: Vec<TypeExpr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecArm {
    pub ctor: Ident,
    pub binders: Vec<Ident>,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    Import {
        path: String,
        alias: Option<Ident>,
        span: Span,
    },
    Mode(Mode, Span),
    Logic(Tier, Span),
    Sort(Ident, Span),
    Const {
        name: Ident,
        ty: TypeExpr,
        span: Span,
    },
    Func {
        name: Ident,
        ty: TypeExpr,
        span: Span,
    },
    Pred {
        name: Ident,
        args: Vec<TypeExpr>,
        span: Span,
    },
    Def {
        name: Ident,
        params: Vec<Param>,
        result: TypeExpr,
        body: Expr,
        span: Span,
    },
    Axiom {
        name: Ident,
        params: Vec<Param>,
        statement: Expr,
        span: Span,
    },
    Theorem {
        name: Ident,
        params: Vec<Param>,
        statement: Expr,
        proof: Vec<Tactic>,
        /// Span of the whole declaration including the proof block.
        span: Span,
        /// Span of the header up to and including `by`.
        header_span: Span,
    },
    Data {
        name: Ident,
        params: Vec<Ident>,
        ctors: Vec<CtorDecl>,
        span: Span,
    },
    Defrec {
        name: Ident,
        params: Vec<Param>,
        result: TypeExpr,
        /// `on x`: the parameter to recurse on (default: the first
        /// parameter of a data type).
        rec_on: Option<Ident>,
        arms: Vec<RecArm>,
        span: Span,
    },
    Namespace(Ident, Span),
    End(Ident, Span),
}

impl Command {
    pub fn span(&self) -> Span {
        match self {
            Command::Import { span, .. }
            | Command::Mode(_, span)
            | Command::Logic(_, span)
            | Command::Sort(_, span)
            | Command::Const { span, .. }
            | Command::Func { span, .. }
            | Command::Pred { span, .. }
            | Command::Def { span, .. }
            | Command::Axiom { span, .. }
            | Command::Theorem { span, .. }
            | Command::Data { span, .. }
            | Command::Defrec { span, .. }
            | Command::Namespace(_, span)
            | Command::End(_, span) => *span,
        }
    }

    pub fn name(&self) -> Option<&Ident> {
        match self {
            Command::Sort(name, _)
            | Command::Const { name, .. }
            | Command::Func { name, .. }
            | Command::Pred { name, .. }
            | Command::Def { name, .. }
            | Command::Axiom { name, .. }
            | Command::Theorem { name, .. }
            | Command::Data { name, .. }
            | Command::Defrec { name, .. } => Some(name),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct File {
    pub commands: Vec<Command>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Projection {
    Left,
    Right,
}

/// An explicit instantiation value: `{A := Person; P := fun x => ...}`.
/// Type parameters take types, so both readings are kept when both
/// parse.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstArg {
    pub param: Ident,
    pub expr: Option<Expr>,
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

/// Proof expressions: hypotheses, theorems, projections, applications to
/// terms and proofs, and explicit instantiation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofExpr {
    /// A name that may be a hypothesis, a theorem, a variable, or a
    /// constant; the elaborator decides.
    Name(Ident),
    /// Something that can only be a term: an application `f(x)`, a
    /// numeral, a set literal, a binder, `True`, `False`.
    Term(Expr),
    Proj(Box<ProofExpr>, Projection, Span),
    App(Box<ProofExpr>, Vec<ProofExpr>, Span),
    Inst(Box<ProofExpr>, Vec<InstArg>, Span),
}

impl ProofExpr {
    pub fn span(&self) -> Span {
        match self {
            ProofExpr::Name(ident) => ident.span,
            ProofExpr::Term(expr) => expr.span(),
            ProofExpr::Proj(_, _, span)
            | ProofExpr::App(_, _, span)
            | ProofExpr::Inst(_, _, span) => *span,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RewriteDir {
    /// `rewrite -> h` and bare `rewrite h`: replace the left side by the
    /// right side.
    LeftToRight,
    /// `rewrite <- h`.
    RightToLeft,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimpTarget {
    Goal,
    Hyp(Ident),
    All,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaseArm {
    pub ctor: Ident,
    pub binders: Vec<Ident>,
    pub body: Vec<Tactic>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HaveProof {
    /// `have h : P`: opens a subgoal.
    Subgoal,
    /// `have h : P := expr` or `have h := expr`.
    Expr(ProofExpr),
    /// `have h : P := by` followed by an indented block.
    Block(Vec<Tactic>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CalcProof {
    Expr(ProofExpr),
    Block(Vec<Tactic>),
}

/// One `_ = rhs := proof` step of a `calc` chain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CalcStep {
    pub op: BinOp,
    pub rhs: Expr,
    pub proof: CalcProof,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TacticKind {
    /// `calc a = b := p` followed by `_ = c := q` lines.
    Calc {
        start: Expr,
        steps: Vec<CalcStep>,
    },
    Intro(Vec<Ident>),
    Revert(Ident),
    Exact(ProofExpr),
    Trivial,
    Assumption,
    Apply(ProofExpr),
    Split,
    Left,
    Right,
    Cases {
        scrutinee: ProofExpr,
        arms: Vec<CaseArm>,
    },
    Exists(Expr),
    Refl,
    Rewrite {
        dir: RewriteDir,
        all: bool,
        proof: ProofExpr,
        at: Option<Ident>,
    },
    Unfold(Ident, Option<Ident>),
    Simp {
        rules: Vec<ProofExpr>,
        target: SimpTarget,
    },
    Induction {
        var: Ident,
        generalizing: Vec<Ident>,
        arms: Vec<CaseArm>,
    },
    Exfalso,
    Contradiction,
    ByCases {
        name: Ident,
        prop: Expr,
    },
    ByContra(Ident),
    ShowGoal,
    Sorry,
    Have {
        name: Ident,
        stated: Option<Expr>,
        proof: HaveProof,
    },
    Show(Expr),
    Obtain {
        names: Vec<Ident>,
        proof: ProofExpr,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tactic {
    pub kind: TacticKind,
    pub span: Span,
}
