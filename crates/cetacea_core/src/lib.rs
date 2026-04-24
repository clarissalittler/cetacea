use std::collections::HashMap;
use std::fmt;

pub type Name = String;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Formula {
    True,
    False,
    Atom(Name),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
}

impl Formula {
    pub fn and(left: Formula, right: Formula) -> Self {
        Self::And(Box::new(left), Box::new(right))
    }

    pub fn or(left: Formula, right: Formula) -> Self {
        Self::Or(Box::new(left), Box::new(right))
    }

    pub fn implies(left: Formula, right: Formula) -> Self {
        Self::Implies(Box::new(left), Box::new(right))
    }

    pub fn negate(formula: Formula) -> Self {
        Self::implies(formula, Self::False)
    }

    fn is_not(&self) -> Option<&Formula> {
        match self {
            Formula::Implies(left, right) if matches!(right.as_ref(), Formula::False) => Some(left),
            _ => None,
        }
    }

    fn precedence(&self) -> u8 {
        match self {
            Formula::Implies(_, _) => 1,
            Formula::Or(_, _) => 2,
            Formula::And(_, _) => 3,
            Formula::True | Formula::False | Formula::Atom(_) => 4,
        }
    }

    fn fmt_with_prec(&self, f: &mut fmt::Formatter<'_>, parent_prec: u8) -> fmt::Result {
        if let Some(inner) = self.is_not() {
            let needs_parens = self.precedence() < parent_prec;
            if needs_parens {
                write!(f, "(")?;
            }
            write!(f, "not ")?;
            inner.fmt_with_prec(f, 4)?;
            if needs_parens {
                write!(f, ")")?;
            }
            return Ok(());
        }

        let my_prec = self.precedence();
        let needs_parens = my_prec < parent_prec;
        if needs_parens {
            write!(f, "(")?;
        }

        match self {
            Formula::True => write!(f, "True")?,
            Formula::False => write!(f, "False")?,
            Formula::Atom(name) => write!(f, "{name}")?,
            Formula::And(left, right) => {
                left.fmt_with_prec(f, my_prec)?;
                write!(f, " /\\ ")?;
                right.fmt_with_prec(f, my_prec + 1)?;
            }
            Formula::Or(left, right) => {
                left.fmt_with_prec(f, my_prec)?;
                write!(f, " \\/ ")?;
                right.fmt_with_prec(f, my_prec + 1)?;
            }
            Formula::Implies(left, right) => {
                left.fmt_with_prec(f, my_prec + 1)?;
                write!(f, " -> ")?;
                right.fmt_with_prec(f, my_prec)?;
            }
        }

        if needs_parens {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_prec(f, 0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogicMode {
    Constructive,
    Classical,
}

impl LogicMode {
    fn combine(self, other: LogicMode) -> LogicMode {
        if matches!(self, LogicMode::Classical) || matches!(other, LogicMode::Classical) {
            LogicMode::Classical
        } else {
            LogicMode::Constructive
        }
    }
}

impl fmt::Display for LogicMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LogicMode::Constructive => write!(f, "constructive"),
            LogicMode::Classical => write!(f, "classical"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParamKind {
    Prop,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: Name,
    pub kind: ParamKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClassicalRule {
    ExcludedMiddle,
    ByContra,
    DoubleNegationElim,
}

impl fmt::Display for ClassicalRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClassicalRule::ExcludedMiddle => write!(f, "excluded middle"),
            ClassicalRule::ByContra => write!(f, "proof by contradiction"),
            ClassicalRule::DoubleNegationElim => write!(f, "double-negation elimination"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proof {
    Hyp(Name),
    TrueIntro,
    FalseElim {
        proof_false: Box<Proof>,
        target: Formula,
    },
    AndIntro(Box<Proof>, Box<Proof>),
    AndElimLeft(Box<Proof>),
    AndElimRight(Box<Proof>),
    OrIntroLeft {
        proof_left: Box<Proof>,
        right_formula: Formula,
    },
    OrIntroRight {
        left_formula: Formula,
        proof_right: Box<Proof>,
    },
    OrElim {
        proof_or: Box<Proof>,
        left_name: Name,
        left_case: Box<Proof>,
        right_name: Name,
        right_case: Box<Proof>,
        target: Formula,
    },
    ImpIntro {
        hyp_name: Name,
        hyp_formula: Formula,
        body: Box<Proof>,
    },
    ImpElim {
        proof_imp: Box<Proof>,
        proof_arg: Box<Proof>,
    },
    TheoremRef {
        name: Name,
        formula_args: Vec<Formula>,
    },
    Classical {
        rule: ClassicalRule,
        args: Vec<Proof>,
        target: Formula,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofBinding {
    pub name: Name,
    pub formula: Formula,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Context {
    proof_vars: Vec<ProofBinding>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_proof(&mut self, name: Name, formula: Formula) {
        self.proof_vars.push(ProofBinding { name, formula });
    }

    pub fn lookup(&self, name: &str) -> Option<&Formula> {
        self.proof_vars
            .iter()
            .rev()
            .find(|binding| binding.name == name)
            .map(|binding| &binding.formula)
    }

    fn proofs(&self) -> &[ProofBinding] {
        &self.proof_vars
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Theorem {
    pub name: Name,
    pub params: Vec<Param>,
    pub statement: Formula,
    pub proof: Proof,
    pub mode_used: LogicMode,
}

#[derive(Clone, Debug, Default)]
pub struct Env {
    theorems: HashMap<Name, Theorem>,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn theorem(&self, name: &str) -> Option<&Theorem> {
        self.theorems.get(name)
    }

    pub fn add_theorem(&mut self, theorem: Theorem) {
        self.theorems.insert(theorem.name.clone(), theorem);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Option<Span>,
    pub message: String,
    pub notes: Vec<String>,
}

impl Diagnostic {
    fn error(message: impl Into<String>) -> Self {
        Self {
            span: None,
            message: message.into(),
            notes: Vec::new(),
        }
    }

    fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedTheorem {
    pub name: Name,
    pub mode_used: LogicMode,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckResult {
    pub theorems: Vec<CheckedTheorem>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn check_file(source: &str) -> CheckResult {
    let file = match parse_file(source) {
        Ok(file) => file,
        Err(err) => {
            return CheckResult {
                theorems: Vec::new(),
                diagnostics: vec![Diagnostic::error(err.message)],
            };
        }
    };

    let mut env = Env::new();
    let mut mode = LogicMode::Constructive;
    let mut result = CheckResult::default();

    for command in file.commands {
        match command {
            Command::Mode(next_mode) => mode = next_mode,
            Command::Theorem(decl) => {
                let proof = match prove(
                    &env,
                    Context::new(),
                    decl.statement.clone(),
                    &decl.tactics,
                    mode,
                ) {
                    Ok(proof) => proof,
                    Err(err) => {
                        result.diagnostics.push(
                            Diagnostic::error(format!(
                                "theorem `{}` failed: {}",
                                decl.name, err.message
                            ))
                            .with_note(format!("target: {}", decl.statement)),
                        );
                        continue;
                    }
                };

                let mode_used =
                    match check_proof(&env, &Context::new(), &proof, &decl.statement, mode) {
                        Ok(mode_used) => mode_used,
                        Err(err) => {
                            result.diagnostics.push(
                                Diagnostic::error(format!(
                                    "theorem `{}` was rejected by the kernel: {}",
                                    decl.name, err.message
                                ))
                                .with_note(format!("target: {}", decl.statement)),
                            );
                            continue;
                        }
                    };

                if matches!(mode, LogicMode::Constructive)
                    && matches!(mode_used, LogicMode::Classical)
                {
                    result.diagnostics.push(
                        Diagnostic::error(format!(
                            "theorem `{}` uses classical reasoning in constructive mode",
                            decl.name
                        ))
                        .with_note("change to `mode classical` or use a constructive proof"),
                    );
                    continue;
                }

                env.add_theorem(Theorem {
                    name: decl.name.clone(),
                    params: decl.params,
                    statement: decl.statement,
                    proof,
                    mode_used,
                });
                result.theorems.push(CheckedTheorem {
                    name: decl.name,
                    mode_used,
                });
            }
        }
    }

    result
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelError {
    pub message: String,
}

impl KernelError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedProof {
    pub formula: Formula,
    pub mode_used: LogicMode,
}

pub fn check_proof(
    env: &Env,
    ctx: &Context,
    proof: &Proof,
    expected: &Formula,
    allowed_mode: LogicMode,
) -> Result<LogicMode, KernelError> {
    let checked = infer_proof(env, ctx, proof, allowed_mode)?;
    if checked.formula == *expected {
        Ok(checked.mode_used)
    } else {
        Err(KernelError::new(format!(
            "proof has type `{}`, but expected `{}`",
            checked.formula, expected
        )))
    }
}

pub fn infer_proof(
    env: &Env,
    ctx: &Context,
    proof: &Proof,
    allowed_mode: LogicMode,
) -> Result<CheckedProof, KernelError> {
    match proof {
        Proof::Hyp(name) => {
            let Some(formula) = ctx.lookup(name) else {
                return Err(KernelError::new(format!("unknown hypothesis `{name}`")));
            };
            Ok(CheckedProof {
                formula: formula.clone(),
                mode_used: LogicMode::Constructive,
            })
        }
        Proof::TrueIntro => Ok(CheckedProof {
            formula: Formula::True,
            mode_used: LogicMode::Constructive,
        }),
        Proof::FalseElim {
            proof_false,
            target,
        } => {
            let mode_used = check_proof(env, ctx, proof_false, &Formula::False, allowed_mode)?;
            Ok(CheckedProof {
                formula: target.clone(),
                mode_used,
            })
        }
        Proof::AndIntro(left, right) => {
            let left = infer_proof(env, ctx, left, allowed_mode)?;
            let right = infer_proof(env, ctx, right, allowed_mode)?;
            Ok(CheckedProof {
                formula: Formula::and(left.formula, right.formula),
                mode_used: left.mode_used.combine(right.mode_used),
            })
        }
        Proof::AndElimLeft(proof) => {
            let checked = infer_proof(env, ctx, proof, allowed_mode)?;
            let Formula::And(left, _) = checked.formula else {
                return Err(KernelError::new(
                    "`.left` can only be used on a conjunction",
                ));
            };
            Ok(CheckedProof {
                formula: *left,
                mode_used: checked.mode_used,
            })
        }
        Proof::AndElimRight(proof) => {
            let checked = infer_proof(env, ctx, proof, allowed_mode)?;
            let Formula::And(_, right) = checked.formula else {
                return Err(KernelError::new(
                    "`.right` can only be used on a conjunction",
                ));
            };
            Ok(CheckedProof {
                formula: *right,
                mode_used: checked.mode_used,
            })
        }
        Proof::OrIntroLeft {
            proof_left,
            right_formula,
        } => {
            let checked = infer_proof(env, ctx, proof_left, allowed_mode)?;
            Ok(CheckedProof {
                formula: Formula::or(checked.formula, right_formula.clone()),
                mode_used: checked.mode_used,
            })
        }
        Proof::OrIntroRight {
            left_formula,
            proof_right,
        } => {
            let checked = infer_proof(env, ctx, proof_right, allowed_mode)?;
            Ok(CheckedProof {
                formula: Formula::or(left_formula.clone(), checked.formula),
                mode_used: checked.mode_used,
            })
        }
        Proof::OrElim {
            proof_or,
            left_name,
            left_case,
            right_name,
            right_case,
            target,
        } => {
            let checked_or = infer_proof(env, ctx, proof_or, allowed_mode)?;
            let Formula::Or(left_formula, right_formula) = checked_or.formula else {
                return Err(KernelError::new("cases can only eliminate a disjunction"));
            };

            let mut left_ctx = ctx.clone();
            left_ctx.add_proof(left_name.clone(), *left_formula);
            let left_mode = check_proof(env, &left_ctx, left_case, target, allowed_mode)?;

            let mut right_ctx = ctx.clone();
            right_ctx.add_proof(right_name.clone(), *right_formula);
            let right_mode = check_proof(env, &right_ctx, right_case, target, allowed_mode)?;

            Ok(CheckedProof {
                formula: target.clone(),
                mode_used: checked_or.mode_used.combine(left_mode).combine(right_mode),
            })
        }
        Proof::ImpIntro {
            hyp_name,
            hyp_formula,
            body,
        } => {
            let mut body_ctx = ctx.clone();
            body_ctx.add_proof(hyp_name.clone(), hyp_formula.clone());
            let body = infer_proof(env, &body_ctx, body, allowed_mode)?;
            Ok(CheckedProof {
                formula: Formula::implies(hyp_formula.clone(), body.formula),
                mode_used: body.mode_used,
            })
        }
        Proof::ImpElim {
            proof_imp,
            proof_arg,
        } => {
            let checked_imp = infer_proof(env, ctx, proof_imp, allowed_mode)?;
            let Formula::Implies(premise, conclusion) = checked_imp.formula else {
                return Err(KernelError::new("apply expected an implication"));
            };
            let arg_mode = check_proof(env, ctx, proof_arg, &premise, allowed_mode)?;
            Ok(CheckedProof {
                formula: *conclusion,
                mode_used: checked_imp.mode_used.combine(arg_mode),
            })
        }
        Proof::TheoremRef { name, formula_args } => {
            let Some(theorem) = env.theorem(name) else {
                return Err(KernelError::new(format!("unknown theorem `{name}`")));
            };
            let formula = instantiate_theorem(theorem, formula_args)?;
            Ok(CheckedProof {
                formula,
                mode_used: theorem.mode_used,
            })
        }
        Proof::Classical { rule, args, target } => {
            if matches!(allowed_mode, LogicMode::Constructive) {
                return Err(KernelError::new(format!(
                    "`{rule}` requires classical mode"
                )));
            }

            match rule {
                ClassicalRule::ExcludedMiddle => {
                    if !args.is_empty() {
                        return Err(KernelError::new("excluded middle takes no proof arguments"));
                    }
                    match target {
                        Formula::Or(left, right)
                            if right.as_ref() == &Formula::negate(left.as_ref().clone()) =>
                        {
                            Ok(CheckedProof {
                                formula: target.clone(),
                                mode_used: LogicMode::Classical,
                            })
                        }
                        _ => Err(KernelError::new(
                            "excluded middle must target `P \\/ not P`",
                        )),
                    }
                }
                ClassicalRule::ByContra => {
                    if args.len() != 1 {
                        return Err(KernelError::new("by_contra takes one proof argument"));
                    }
                    let expected =
                        Formula::implies(Formula::negate(target.clone()), Formula::False);
                    let arg_mode = check_proof(env, ctx, &args[0], &expected, allowed_mode)?;
                    Ok(CheckedProof {
                        formula: target.clone(),
                        mode_used: LogicMode::Classical.combine(arg_mode),
                    })
                }
                ClassicalRule::DoubleNegationElim => {
                    if args.len() != 1 {
                        return Err(KernelError::new(
                            "double-negation elimination takes one proof argument",
                        ));
                    }
                    let expected = Formula::negate(Formula::negate(target.clone()));
                    let arg_mode = check_proof(env, ctx, &args[0], &expected, allowed_mode)?;
                    Ok(CheckedProof {
                        formula: target.clone(),
                        mode_used: LogicMode::Classical.combine(arg_mode),
                    })
                }
            }
        }
    }
}

fn instantiate_theorem(
    theorem: &Theorem,
    formula_args: &[Formula],
) -> Result<Formula, KernelError> {
    let prop_params: Vec<&Param> = theorem
        .params
        .iter()
        .filter(|param| matches!(&param.kind, ParamKind::Prop))
        .collect();
    if formula_args.is_empty() {
        return Ok(theorem.statement.clone());
    }
    if formula_args.len() != prop_params.len() {
        return Err(KernelError::new(format!(
            "theorem `{}` expects {} formula argument(s), but got {}",
            theorem.name,
            prop_params.len(),
            formula_args.len()
        )));
    }

    let mut subst = HashMap::new();
    for (param, arg) in prop_params.into_iter().zip(formula_args.iter()) {
        subst.insert(param.name.clone(), arg.clone());
    }
    Ok(subst_formula(&theorem.statement, &subst))
}

fn subst_formula(formula: &Formula, subst: &HashMap<Name, Formula>) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Atom(name) => subst
            .get(name)
            .cloned()
            .unwrap_or_else(|| Formula::Atom(name.clone())),
        Formula::And(left, right) => {
            Formula::and(subst_formula(left, subst), subst_formula(right, subst))
        }
        Formula::Or(left, right) => {
            Formula::or(subst_formula(left, subst), subst_formula(right, subst))
        }
        Formula::Implies(left, right) => {
            Formula::implies(subst_formula(left, subst), subst_formula(right, subst))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TheoremDecl {
    name: Name,
    params: Vec<Param>,
    statement: Formula,
    tactics: Vec<Tactic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Command {
    Mode(LogicMode),
    Theorem(TheoremDecl),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct File {
    commands: Vec<Command>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParseError {
    message: String,
}

impl ParseError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Projection {
    Left,
    Right,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProofExpr {
    base: Name,
    projections: Vec<Projection>,
}

impl ProofExpr {
    fn to_proof(&self, env: &Env, ctx: &Context) -> Proof {
        let mut proof = if ctx.lookup(&self.base).is_some() {
            Proof::Hyp(self.base.clone())
        } else if env.theorem(&self.base).is_some() {
            Proof::TheoremRef {
                name: self.base.clone(),
                formula_args: Vec::new(),
            }
        } else {
            Proof::Hyp(self.base.clone())
        };

        for projection in &self.projections {
            proof = match projection {
                Projection::Left => Proof::AndElimLeft(Box::new(proof)),
                Projection::Right => Proof::AndElimRight(Box::new(proof)),
            };
        }

        proof
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tactic {
    Intro(Name),
    Exact(ProofExpr),
    Assumption,
    Apply(ProofExpr),
    Split,
    Left,
    Right,
    Cases {
        expr: ProofExpr,
        left_name: Name,
        left_tactics: Vec<Tactic>,
        right_name: Name,
        right_tactics: Vec<Tactic>,
    },
    Exfalso,
    Contradiction,
    ByCases {
        name: Name,
        formula: Formula,
    },
    ByContra(Name),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Token {
    kind: TokenKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokenKind {
    Ident(String),
    Sym(String),
    Eof,
}

struct Tokens {
    tokens: Vec<Token>,
    pos: usize,
}

impl Tokens {
    fn new(input: &str) -> Result<Self, ParseError> {
        Ok(Self {
            tokens: lex(input)?,
            pos: 0,
        })
    }

    fn peek(&self) -> &TokenKind {
        &self.tokens[self.pos].kind
    }

    fn eat_sym(&mut self, sym: &str) -> bool {
        if matches!(self.peek(), TokenKind::Sym(actual) if actual == sym) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect_sym(&mut self, sym: &str) -> Result<(), ParseError> {
        if self.eat_sym(sym) {
            Ok(())
        } else {
            Err(ParseError::new(format!("expected `{sym}`")))
        }
    }

    fn eat_ident(&mut self, expected: &str) -> bool {
        if matches!(self.peek(), TokenKind::Ident(actual) if actual == expected) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect_ident(&mut self) -> Result<String, ParseError> {
        match self.peek() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.pos += 1;
                Ok(name)
            }
            _ => Err(ParseError::new("expected identifier")),
        }
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<(), ParseError> {
        if self.eat_ident(keyword) {
            Ok(())
        } else {
            Err(ParseError::new(format!("expected `{keyword}`")))
        }
    }

    fn expect_eof(&self) -> Result<(), ParseError> {
        if matches!(self.peek(), TokenKind::Eof) {
            Ok(())
        } else {
            Err(ParseError::new("unexpected trailing input"))
        }
    }

    fn parse_formula(&mut self) -> Result<Formula, ParseError> {
        self.parse_implication()
    }

    fn parse_implication(&mut self) -> Result<Formula, ParseError> {
        let left = self.parse_iff()?;
        if self.eat_sym("->") {
            let right = self.parse_implication()?;
            return Ok(Formula::implies(left, right));
        }
        Ok(left)
    }

    fn parse_iff(&mut self) -> Result<Formula, ParseError> {
        let left = self.parse_or()?;
        if self.eat_sym("<->") {
            let right = self.parse_implication()?;
            return Ok(Formula::and(
                Formula::implies(left.clone(), right.clone()),
                Formula::implies(right, left),
            ));
        }
        Ok(left)
    }

    fn parse_or(&mut self) -> Result<Formula, ParseError> {
        let mut formula = self.parse_and()?;
        while self.eat_sym("\\/") {
            let right = self.parse_and()?;
            formula = Formula::or(formula, right);
        }
        Ok(formula)
    }

    fn parse_and(&mut self) -> Result<Formula, ParseError> {
        let mut formula = self.parse_unary()?;
        while self.eat_sym("/\\") {
            let right = self.parse_unary()?;
            formula = Formula::and(formula, right);
        }
        Ok(formula)
    }

    fn parse_unary(&mut self) -> Result<Formula, ParseError> {
        if self.eat_ident("not") {
            let formula = self.parse_unary()?;
            return Ok(Formula::negate(formula));
        }
        if self.eat_ident("True") {
            return Ok(Formula::True);
        }
        if self.eat_ident("False") {
            return Ok(Formula::False);
        }
        if self.eat_sym("(") {
            let formula = self.parse_formula()?;
            self.expect_sym(")")?;
            return Ok(formula);
        }
        Ok(Formula::Atom(self.expect_ident()?))
    }
}

fn lex(input: &str) -> Result<Vec<Token>, ParseError> {
    let chars: Vec<char> = input.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;

    while i < chars.len() {
        let ch = chars[i];
        if ch.is_whitespace() {
            i += 1;
            continue;
        }
        if ch.is_ascii_alphabetic() || ch == '_' {
            let start = i;
            i += 1;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            tokens.push(Token {
                kind: TokenKind::Ident(chars[start..i].iter().collect()),
            });
            continue;
        }

        let rest: String = chars[i..].iter().collect();
        let sym = if rest.starts_with(":=") {
            Some(":=")
        } else if rest.starts_with("->") {
            Some("->")
        } else if rest.starts_with("<->") {
            Some("<->")
        } else if rest.starts_with("/\\") {
            Some("/\\")
        } else if rest.starts_with("\\/") {
            Some("\\/")
        } else {
            match ch {
                '(' => Some("("),
                ')' => Some(")"),
                ':' => Some(":"),
                ',' => Some(","),
                '.' => Some("."),
                _ => None,
            }
        };

        let Some(sym) = sym else {
            return Err(ParseError::new(format!("unexpected character `{ch}`")));
        };
        tokens.push(Token {
            kind: TokenKind::Sym(sym.to_string()),
        });
        i += sym.chars().count();
    }

    tokens.push(Token {
        kind: TokenKind::Eof,
    });
    Ok(tokens)
}

fn parse_file(source: &str) -> Result<File, ParseError> {
    let mut commands = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let trimmed = strip_comment(lines[i]).trim();
        if trimmed.is_empty() {
            i += 1;
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("mode ") {
            let mode = match rest.trim() {
                "constructive" => LogicMode::Constructive,
                "classical" => LogicMode::Classical,
                other => return Err(ParseError::new(format!("unknown mode `{other}`"))),
            };
            commands.push(Command::Mode(mode));
            i += 1;
            continue;
        }

        if trimmed.starts_with("theorem ") {
            let mut header = String::from(trimmed);
            while !header.contains(":= by") {
                i += 1;
                if i >= lines.len() {
                    return Err(ParseError::new("unterminated theorem header"));
                }
                header.push(' ');
                header.push_str(strip_comment(lines[i]).trim());
            }

            let Some((header, _)) = header.split_once(":= by") else {
                return Err(ParseError::new("expected `:= by` in theorem declaration"));
            };
            let (name, params, statement) = parse_theorem_header(header)?;

            i += 1;
            let mut tactic_lines = Vec::new();
            while i < lines.len() {
                let next = strip_comment(lines[i]).trim();
                if is_command_start(next) {
                    break;
                }
                tactic_lines.push(strip_comment(lines[i]).to_string());
                i += 1;
            }

            commands.push(Command::Theorem(TheoremDecl {
                name,
                params,
                statement,
                tactics: parse_tactic_lines(&tactic_lines)?,
            }));
            continue;
        }

        return Err(ParseError::new(format!("unsupported command `{trimmed}`")));
    }

    Ok(File { commands })
}

fn strip_comment(line: &str) -> &str {
    line.split_once("--")
        .map(|(before, _)| before)
        .unwrap_or(line)
}

fn is_command_start(trimmed: &str) -> bool {
    trimmed.starts_with("mode ")
        || trimmed.starts_with("theorem ")
        || trimmed.starts_with("sort ")
        || trimmed.starts_with("const ")
        || trimmed.starts_with("func ")
        || trimmed.starts_with("pred ")
        || trimmed.starts_with("def ")
        || trimmed.starts_with("axiom ")
}

fn parse_theorem_header(header: &str) -> Result<(Name, Vec<Param>, Formula), ParseError> {
    let mut tokens = Tokens::new(header)?;
    tokens.expect_keyword("theorem")?;
    let name = tokens.expect_ident()?;
    let mut params = Vec::new();

    while tokens.eat_sym("(") {
        let mut names = Vec::new();
        loop {
            names.push(tokens.expect_ident()?);
            if matches!(tokens.peek(), TokenKind::Sym(sym) if sym == ":") {
                break;
            }
        }
        tokens.expect_sym(":")?;
        let kind = tokens.expect_ident()?;
        if kind != "Prop" {
            return Err(ParseError::new(format!(
                "only proposition parameters are implemented in this milestone, got `{kind}`"
            )));
        }
        tokens.expect_sym(")")?;
        for name in names {
            params.push(Param {
                name,
                kind: ParamKind::Prop,
            });
        }
    }

    tokens.expect_sym(":")?;
    let statement = tokens.parse_formula()?;
    tokens.expect_eof()?;
    Ok((name, params, statement))
}

fn parse_formula_str(input: &str) -> Result<Formula, ParseError> {
    let mut tokens = Tokens::new(input)?;
    let formula = tokens.parse_formula()?;
    tokens.expect_eof()?;
    Ok(formula)
}

fn parse_tactic_lines(lines: &[String]) -> Result<Vec<Tactic>, ParseError> {
    let mut tactics = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let trimmed = lines[i].trim();
        if trimmed.is_empty() {
            i += 1;
            continue;
        }
        if trimmed.starts_with('|') {
            return Err(ParseError::new("case arm appeared outside `cases`"));
        }

        if let Some(expr) = trimmed
            .strip_prefix("cases ")
            .and_then(|rest| rest.strip_suffix(" with"))
        {
            i += 1;
            if i >= lines.len() {
                return Err(ParseError::new("expected left case arm"));
            }

            let left_name = parse_case_arm(lines[i].trim(), "left")?;
            i += 1;
            let left_start = i;
            while i < lines.len() && !lines[i].trim().starts_with("| right ") {
                i += 1;
            }
            if i >= lines.len() {
                return Err(ParseError::new("expected right case arm"));
            }
            let left_tactics = parse_tactic_lines(&lines[left_start..i])?;

            let right_name = parse_case_arm(lines[i].trim(), "right")?;
            i += 1;
            let right_tactics = parse_tactic_lines(&lines[i..])?;
            i = lines.len();

            tactics.push(Tactic::Cases {
                expr: parse_proof_expr(expr.trim())?,
                left_name,
                left_tactics,
                right_name,
                right_tactics,
            });
            continue;
        }

        tactics.push(parse_tactic_line(trimmed)?);
        i += 1;
    }

    Ok(tactics)
}

fn parse_case_arm(line: &str, side: &str) -> Result<Name, ParseError> {
    let prefix = format!("| {side} ");
    let Some(rest) = line.strip_prefix(&prefix) else {
        return Err(ParseError::new(format!("expected `{side}` case arm")));
    };
    let Some(name) = rest.strip_suffix("=>") else {
        return Err(ParseError::new("case arm must end with `=>`"));
    };
    let name = name.trim();
    if name.is_empty() {
        return Err(ParseError::new("case arm needs a hypothesis name"));
    }
    Ok(name.to_string())
}

fn parse_tactic_line(line: &str) -> Result<Tactic, ParseError> {
    if let Some(rest) = line.strip_prefix("intro ") {
        return Ok(Tactic::Intro(expect_single_name(rest, "intro")?));
    }
    if let Some(rest) = line.strip_prefix("exact ") {
        return Ok(Tactic::Exact(parse_proof_expr(rest.trim())?));
    }
    if line == "assumption" {
        return Ok(Tactic::Assumption);
    }
    if let Some(rest) = line.strip_prefix("apply ") {
        return Ok(Tactic::Apply(parse_proof_expr(rest.trim())?));
    }
    if line == "split" {
        return Ok(Tactic::Split);
    }
    if line == "left" {
        return Ok(Tactic::Left);
    }
    if line == "right" {
        return Ok(Tactic::Right);
    }
    if line == "exfalso" {
        return Ok(Tactic::Exfalso);
    }
    if line == "contradiction" {
        return Ok(Tactic::Contradiction);
    }
    if let Some(rest) = line.strip_prefix("by_cases ") {
        let Some((name, formula)) = rest.split_once(':') else {
            return Err(ParseError::new("by_cases expects `name : formula`"));
        };
        return Ok(Tactic::ByCases {
            name: expect_single_name(name, "by_cases")?,
            formula: parse_formula_str(formula.trim())?,
        });
    }
    if let Some(rest) = line.strip_prefix("by_contra ") {
        return Ok(Tactic::ByContra(expect_single_name(rest, "by_contra")?));
    }

    Err(ParseError::new(format!("unknown tactic `{line}`")))
}

fn expect_single_name(input: &str, tactic: &str) -> Result<Name, ParseError> {
    let name = input.trim();
    if name.is_empty() || name.split_whitespace().count() != 1 {
        return Err(ParseError::new(format!("{tactic} expects one identifier")));
    }
    Ok(name.to_string())
}

fn parse_proof_expr(input: &str) -> Result<ProofExpr, ParseError> {
    let mut parts = input.split('.');
    let Some(base) = parts.next() else {
        return Err(ParseError::new("expected proof expression"));
    };
    let base = base.trim();
    if base.is_empty() {
        return Err(ParseError::new("expected proof expression"));
    }

    let mut projections = Vec::new();
    for part in parts {
        match part.trim() {
            "left" => projections.push(Projection::Left),
            "right" => projections.push(Projection::Right),
            other => {
                return Err(ParseError::new(format!(
                    "unknown proof projection `.{other}`"
                )))
            }
        }
    }

    Ok(ProofExpr {
        base: base.to_string(),
        projections,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TacticError {
    message: String,
}

impl TacticError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Goal {
    id: usize,
    context: Context,
    target: Formula,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum PartialProof {
    Hole(usize),
    Done(Proof),
    FalseElim {
        proof_false: Box<PartialProof>,
        target: Formula,
    },
    AndIntro(Box<PartialProof>, Box<PartialProof>),
    OrIntroLeft {
        proof_left: Box<PartialProof>,
        right_formula: Formula,
    },
    OrIntroRight {
        left_formula: Formula,
        proof_right: Box<PartialProof>,
    },
    OrElim {
        proof_or: Box<PartialProof>,
        left_name: Name,
        left_case: Box<PartialProof>,
        right_name: Name,
        right_case: Box<PartialProof>,
        target: Formula,
    },
    ImpIntro {
        hyp_name: Name,
        hyp_formula: Formula,
        body: Box<PartialProof>,
    },
    ImpElim {
        proof_imp: Box<PartialProof>,
        proof_arg: Box<PartialProof>,
    },
    Classical {
        rule: ClassicalRule,
        args: Vec<PartialProof>,
        target: Formula,
    },
}

impl PartialProof {
    fn replace_hole(&mut self, id: usize, replacement: &PartialProof) -> bool {
        match self {
            PartialProof::Hole(hole_id) if *hole_id == id => {
                *self = replacement.clone();
                true
            }
            PartialProof::Hole(_) | PartialProof::Done(_) => false,
            PartialProof::FalseElim { proof_false, .. } => {
                proof_false.replace_hole(id, replacement)
            }
            PartialProof::AndIntro(left, right) => {
                left.replace_hole(id, replacement) || right.replace_hole(id, replacement)
            }
            PartialProof::OrIntroLeft { proof_left, .. } => {
                proof_left.replace_hole(id, replacement)
            }
            PartialProof::OrIntroRight { proof_right, .. } => {
                proof_right.replace_hole(id, replacement)
            }
            PartialProof::OrElim {
                proof_or,
                left_case,
                right_case,
                ..
            } => {
                proof_or.replace_hole(id, replacement)
                    || left_case.replace_hole(id, replacement)
                    || right_case.replace_hole(id, replacement)
            }
            PartialProof::ImpIntro { body, .. } => body.replace_hole(id, replacement),
            PartialProof::ImpElim {
                proof_imp,
                proof_arg,
            } => proof_imp.replace_hole(id, replacement) || proof_arg.replace_hole(id, replacement),
            PartialProof::Classical { args, .. } => {
                args.iter_mut().any(|arg| arg.replace_hole(id, replacement))
            }
        }
    }

    fn complete(self) -> Result<Proof, TacticError> {
        match self {
            PartialProof::Hole(_) => Err(TacticError::new("proof has an unsolved goal")),
            PartialProof::Done(proof) => Ok(proof),
            PartialProof::FalseElim {
                proof_false,
                target,
            } => Ok(Proof::FalseElim {
                proof_false: Box::new(proof_false.complete()?),
                target,
            }),
            PartialProof::AndIntro(left, right) => Ok(Proof::AndIntro(
                Box::new(left.complete()?),
                Box::new(right.complete()?),
            )),
            PartialProof::OrIntroLeft {
                proof_left,
                right_formula,
            } => Ok(Proof::OrIntroLeft {
                proof_left: Box::new(proof_left.complete()?),
                right_formula,
            }),
            PartialProof::OrIntroRight {
                left_formula,
                proof_right,
            } => Ok(Proof::OrIntroRight {
                left_formula,
                proof_right: Box::new(proof_right.complete()?),
            }),
            PartialProof::OrElim {
                proof_or,
                left_name,
                left_case,
                right_name,
                right_case,
                target,
            } => Ok(Proof::OrElim {
                proof_or: Box::new(proof_or.complete()?),
                left_name,
                left_case: Box::new(left_case.complete()?),
                right_name,
                right_case: Box::new(right_case.complete()?),
                target,
            }),
            PartialProof::ImpIntro {
                hyp_name,
                hyp_formula,
                body,
            } => Ok(Proof::ImpIntro {
                hyp_name,
                hyp_formula,
                body: Box::new(body.complete()?),
            }),
            PartialProof::ImpElim {
                proof_imp,
                proof_arg,
            } => Ok(Proof::ImpElim {
                proof_imp: Box::new(proof_imp.complete()?),
                proof_arg: Box::new(proof_arg.complete()?),
            }),
            PartialProof::Classical { rule, args, target } => {
                let mut completed_args = Vec::new();
                for arg in args {
                    completed_args.push(arg.complete()?);
                }
                Ok(Proof::Classical {
                    rule,
                    args: completed_args,
                    target,
                })
            }
        }
    }
}

fn prove(
    env: &Env,
    context: Context,
    target: Formula,
    tactics: &[Tactic],
    allowed_mode: LogicMode,
) -> Result<Proof, TacticError> {
    let mut root = PartialProof::Hole(0);
    let mut goals = vec![Goal {
        id: 0,
        context,
        target,
    }];
    let mut next_goal_id = 1;

    for tactic in tactics {
        if goals.is_empty() {
            return Err(TacticError::new(
                "tactic was provided after all goals were solved",
            ));
        }

        let goal = goals.remove(0);
        let goal_id = goal.id;
        let StepResult {
            replacement,
            new_goals,
        } = run_tactic(env, goal, tactic, allowed_mode, &mut next_goal_id)?;
        if !root.replace_hole(goal_id, &replacement) {
            return Err(TacticError::new("internal error: missing proof hole"));
        }
        for new_goal in new_goals.into_iter().rev() {
            goals.insert(0, new_goal);
        }
    }

    if let Some(goal) = goals.first() {
        return Err(TacticError::new(format!("unsolved goal `{}`", goal.target)));
    }

    root.complete()
}

struct StepResult {
    replacement: PartialProof,
    new_goals: Vec<Goal>,
}

fn run_tactic(
    env: &Env,
    goal: Goal,
    tactic: &Tactic,
    allowed_mode: LogicMode,
    next_goal_id: &mut usize,
) -> Result<StepResult, TacticError> {
    match tactic {
        Tactic::Intro(name) => {
            let Formula::Implies(premise, conclusion) = goal.target else {
                return Err(TacticError::new("intro expects an implication goal"));
            };
            let mut context = goal.context;
            context.add_proof(name.clone(), *premise.clone());
            let body_id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::ImpIntro {
                    hyp_name: name.clone(),
                    hyp_formula: *premise,
                    body: Box::new(PartialProof::Hole(body_id)),
                },
                new_goals: vec![Goal {
                    id: body_id,
                    context,
                    target: *conclusion,
                }],
            })
        }
        Tactic::Exact(expr) => {
            let proof = expr.to_proof(env, &goal.context);
            check_proof(env, &goal.context, &proof, &goal.target, allowed_mode).map_err(|err| {
                TacticError::new(format!(
                    "exact expression does not solve the goal: {}",
                    err.message
                ))
            })?;
            Ok(StepResult {
                replacement: PartialProof::Done(proof),
                new_goals: Vec::new(),
            })
        }
        Tactic::Assumption => {
            let Some(binding) = goal
                .context
                .proofs()
                .iter()
                .rev()
                .find(|binding| binding.formula == goal.target)
            else {
                return Err(TacticError::new("no matching assumption found"));
            };
            Ok(StepResult {
                replacement: PartialProof::Done(Proof::Hyp(binding.name.clone())),
                new_goals: Vec::new(),
            })
        }
        Tactic::Apply(expr) => {
            let proof = expr.to_proof(env, &goal.context);
            let checked = infer_proof(env, &goal.context, &proof, allowed_mode).map_err(|err| {
                TacticError::new(format!("cannot apply expression: {}", err.message))
            })?;
            let premises = implication_premises_for_goal(&checked.formula, &goal.target)?;
            let mut replacement = PartialProof::Done(proof);
            let mut new_goals = Vec::new();

            for premise in premises {
                let id = fresh_goal(next_goal_id);
                replacement = PartialProof::ImpElim {
                    proof_imp: Box::new(replacement),
                    proof_arg: Box::new(PartialProof::Hole(id)),
                };
                new_goals.push(Goal {
                    id,
                    context: goal.context.clone(),
                    target: premise,
                });
            }

            Ok(StepResult {
                replacement,
                new_goals,
            })
        }
        Tactic::Split => {
            let Formula::And(left, right) = goal.target else {
                return Err(TacticError::new("split expects a conjunction goal"));
            };
            let left_id = fresh_goal(next_goal_id);
            let right_id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::AndIntro(
                    Box::new(PartialProof::Hole(left_id)),
                    Box::new(PartialProof::Hole(right_id)),
                ),
                new_goals: vec![
                    Goal {
                        id: left_id,
                        context: goal.context.clone(),
                        target: *left,
                    },
                    Goal {
                        id: right_id,
                        context: goal.context,
                        target: *right,
                    },
                ],
            })
        }
        Tactic::Left => {
            let Formula::Or(left, right) = goal.target else {
                return Err(TacticError::new("left expects a disjunction goal"));
            };
            let id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::OrIntroLeft {
                    proof_left: Box::new(PartialProof::Hole(id)),
                    right_formula: *right,
                },
                new_goals: vec![Goal {
                    id,
                    context: goal.context,
                    target: *left,
                }],
            })
        }
        Tactic::Right => {
            let Formula::Or(left, right) = goal.target else {
                return Err(TacticError::new("right expects a disjunction goal"));
            };
            let id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::OrIntroRight {
                    left_formula: *left,
                    proof_right: Box::new(PartialProof::Hole(id)),
                },
                new_goals: vec![Goal {
                    id,
                    context: goal.context,
                    target: *right,
                }],
            })
        }
        Tactic::Cases {
            expr,
            left_name,
            left_tactics,
            right_name,
            right_tactics,
        } => {
            let proof_or = expr.to_proof(env, &goal.context);
            let checked = infer_proof(env, &goal.context, &proof_or, allowed_mode)
                .map_err(|err| TacticError::new(format!("cannot case split: {}", err.message)))?;
            let Formula::Or(left_formula, right_formula) = checked.formula else {
                return Err(TacticError::new("cases expects a disjunction proof"));
            };

            let mut left_ctx = goal.context.clone();
            left_ctx.add_proof(left_name.clone(), *left_formula);
            let left_case = prove(
                env,
                left_ctx,
                goal.target.clone(),
                left_tactics,
                allowed_mode,
            )?;

            let mut right_ctx = goal.context;
            right_ctx.add_proof(right_name.clone(), *right_formula);
            let right_case = prove(
                env,
                right_ctx,
                goal.target.clone(),
                right_tactics,
                allowed_mode,
            )?;

            Ok(StepResult {
                replacement: PartialProof::Done(Proof::OrElim {
                    proof_or: Box::new(proof_or),
                    left_name: left_name.clone(),
                    left_case: Box::new(left_case),
                    right_name: right_name.clone(),
                    right_case: Box::new(right_case),
                    target: goal.target,
                }),
                new_goals: Vec::new(),
            })
        }
        Tactic::Exfalso => {
            let id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::FalseElim {
                    proof_false: Box::new(PartialProof::Hole(id)),
                    target: goal.target,
                },
                new_goals: vec![Goal {
                    id,
                    context: goal.context,
                    target: Formula::False,
                }],
            })
        }
        Tactic::Contradiction => contradiction_step(goal),
        Tactic::ByCases { name, formula } => {
            if matches!(allowed_mode, LogicMode::Constructive) {
                return Err(TacticError::new(format!(
                    "by_cases uses excluded middle for `{formula}` and requires classical mode"
                )));
            }
            let not_formula = Formula::negate(formula.clone());
            let left_id = fresh_goal(next_goal_id);
            let right_id = fresh_goal(next_goal_id);

            let mut left_ctx = goal.context.clone();
            left_ctx.add_proof(name.clone(), formula.clone());

            let mut right_ctx = goal.context.clone();
            right_ctx.add_proof(name.clone(), not_formula.clone());

            Ok(StepResult {
                replacement: PartialProof::OrElim {
                    proof_or: Box::new(PartialProof::Done(Proof::Classical {
                        rule: ClassicalRule::ExcludedMiddle,
                        args: Vec::new(),
                        target: Formula::or(formula.clone(), not_formula),
                    })),
                    left_name: name.clone(),
                    left_case: Box::new(PartialProof::Hole(left_id)),
                    right_name: name.clone(),
                    right_case: Box::new(PartialProof::Hole(right_id)),
                    target: goal.target.clone(),
                },
                new_goals: vec![
                    Goal {
                        id: left_id,
                        context: left_ctx,
                        target: goal.target.clone(),
                    },
                    Goal {
                        id: right_id,
                        context: right_ctx,
                        target: goal.target,
                    },
                ],
            })
        }
        Tactic::ByContra(name) => {
            if matches!(allowed_mode, LogicMode::Constructive) {
                return Err(TacticError::new(format!(
                    "by_contra introduces a classical proof of `{}`",
                    goal.target
                )));
            }
            let not_target = Formula::negate(goal.target.clone());
            let false_id = fresh_goal(next_goal_id);
            let mut context = goal.context;
            context.add_proof(name.clone(), not_target.clone());

            Ok(StepResult {
                replacement: PartialProof::Classical {
                    rule: ClassicalRule::ByContra,
                    args: vec![PartialProof::ImpIntro {
                        hyp_name: name.clone(),
                        hyp_formula: not_target,
                        body: Box::new(PartialProof::Hole(false_id)),
                    }],
                    target: goal.target,
                },
                new_goals: vec![Goal {
                    id: false_id,
                    context,
                    target: Formula::False,
                }],
            })
        }
    }
}

fn fresh_goal(next_goal_id: &mut usize) -> usize {
    let id = *next_goal_id;
    *next_goal_id += 1;
    id
}

fn implication_premises_for_goal(
    formula: &Formula,
    target: &Formula,
) -> Result<Vec<Formula>, TacticError> {
    let mut premises = Vec::new();
    let mut cursor = formula;
    while let Formula::Implies(premise, conclusion) = cursor {
        premises.push(*premise.clone());
        cursor = conclusion;
    }

    if cursor == target {
        Ok(premises)
    } else {
        Err(TacticError::new(format!(
            "cannot apply expression with conclusion `{cursor}` to goal `{target}`"
        )))
    }
}

fn contradiction_step(goal: Goal) -> Result<StepResult, TacticError> {
    if let Some(binding) = goal
        .context
        .proofs()
        .iter()
        .rev()
        .find(|binding| matches!(&binding.formula, Formula::False))
    {
        return Ok(StepResult {
            replacement: PartialProof::FalseElim {
                proof_false: Box::new(PartialProof::Done(Proof::Hyp(binding.name.clone()))),
                target: goal.target,
            },
            new_goals: Vec::new(),
        });
    }

    for neg in goal.context.proofs() {
        let Formula::Implies(premise, conclusion) = &neg.formula else {
            continue;
        };
        if !matches!(conclusion.as_ref(), Formula::False) {
            continue;
        }
        if let Some(pos) = goal
            .context
            .proofs()
            .iter()
            .find(|binding| &binding.formula == premise.as_ref())
        {
            return Ok(StepResult {
                replacement: PartialProof::FalseElim {
                    proof_false: Box::new(PartialProof::Done(Proof::ImpElim {
                        proof_imp: Box::new(Proof::Hyp(neg.name.clone())),
                        proof_arg: Box::new(Proof::Hyp(pos.name.clone())),
                    })),
                    target: goal.target,
                },
                new_goals: Vec::new(),
            });
        }
    }

    Err(TacticError::new("no contradiction found in the context"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_ok(source: &str) -> CheckResult {
        let result = check_file(source);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected diagnostics: {:#?}",
            result.diagnostics
        );
        result
    }

    #[test]
    fn and_comm_succeeds_constructively() {
        let result = check_ok(
            r#"
mode constructive

theorem and_comm (P Q : Prop) : P /\ Q -> Q /\ P := by
  intro h
  split
  exact h.right
  exact h.left
"#,
        );
        assert_eq!(result.theorems[0].mode_used, LogicMode::Constructive);
    }

    #[test]
    fn imp_trans_succeeds_constructively() {
        check_ok(
            r#"
mode constructive

theorem imp_trans (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R := by
  intro hpq
  intro hqr
  intro hp
  apply hqr
  apply hpq
  exact hp
"#,
        );
    }

    #[test]
    fn not_not_em_succeeds_constructively() {
        check_ok(
            r#"
mode constructive

theorem not_not_em (P : Prop) : not not (P \/ not P) := by
  intro h
  apply h
  right
  intro p
  apply h
  left
  exact p
"#,
        );
    }

    #[test]
    fn em_fails_constructively() {
        let result = check_file(
            r#"
mode constructive

theorem em (P : Prop) : P \/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h
"#,
        );
        assert!(!result.diagnostics.is_empty());
    }

    #[test]
    fn em_succeeds_classically() {
        let result = check_ok(
            r#"
mode classical

theorem em (P : Prop) : P \/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h
"#,
        );
        assert_eq!(result.theorems[0].mode_used, LogicMode::Classical);
    }

    #[test]
    fn by_contra_fails_constructively() {
        let result = check_file(
            r#"
mode constructive

theorem dne (P : Prop) : not not P -> P := by
  intro hnn
  by_contra hn
  apply hnn
  exact hn
"#,
        );
        assert!(!result.diagnostics.is_empty());
    }

    #[test]
    fn by_contra_succeeds_classically() {
        let result = check_ok(
            r#"
mode classical

theorem dne (P : Prop) : not not P -> P := by
  intro hnn
  by_contra hn
  apply hnn
  exact hn
"#,
        );
        assert_eq!(result.theorems[0].mode_used, LogicMode::Classical);
    }
}
