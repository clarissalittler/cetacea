use std::collections::HashMap;
use std::fmt;

pub type Name = String;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Named(Name),
    Nat,
    Set(Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Named(name) => write!(f, "{name}"),
            Type::Nat => write!(f, "Nat"),
            Type::Set(elem) => write!(f, "Set {elem}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Var(Name),
    App(Name, Vec<Term>),
    Zero,
    Succ(Box<Term>),
    Add(Box<Term>, Box<Term>),
    EmptySet(Type),
    Singleton(Box<Term>),
    Union(Box<Term>, Box<Term>),
    Inter(Box<Term>, Box<Term>),
    Diff(Box<Term>, Box<Term>),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(name) => write!(f, "{name}"),
            Term::App(name, args) => {
                write!(f, "{name}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            Term::Zero => write!(f, "0"),
            Term::Succ(term) => write!(f, "succ({term})"),
            Term::Add(left, right) => write!(f, "add({left}, {right})"),
            Term::EmptySet(ty) => write!(f, "empty({ty})"),
            Term::Singleton(term) => write!(f, "singleton({term})"),
            Term::Union(left, right) => write!(f, "union({left}, {right})"),
            Term::Inter(left, right) => write!(f, "inter({left}, {right})"),
            Term::Diff(left, right) => write!(f, "diff({left}, {right})"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Formula {
    True,
    False,
    Atom(Name),
    PredApp(Name, Vec<Term>),
    Eq(Term, Term),
    In(Term, Term),
    Subset(Term, Term),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Forall {
        var: Name,
        var_type: Type,
        body: Box<Formula>,
    },
    Exists {
        var: Name,
        var_type: Type,
        body: Box<Formula>,
    },
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

    pub fn eq(left: Term, right: Term) -> Self {
        Self::Eq(left, right)
    }

    pub fn membership(elem: Term, set: Term) -> Self {
        Self::In(elem, set)
    }

    pub fn subset(left: Term, right: Term) -> Self {
        Self::Subset(left, right)
    }

    pub fn negate(formula: Formula) -> Self {
        Self::implies(formula, Self::False)
    }

    pub fn forall(var: Name, var_type: Type, body: Formula) -> Self {
        Self::Forall {
            var,
            var_type,
            body: Box::new(body),
        }
    }

    pub fn exists(var: Name, var_type: Type, body: Formula) -> Self {
        Self::Exists {
            var,
            var_type,
            body: Box::new(body),
        }
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
            Formula::Forall { .. } | Formula::Exists { .. } => 1,
            Formula::True
            | Formula::False
            | Formula::Atom(_)
            | Formula::PredApp(_, _)
            | Formula::Eq(_, _)
            | Formula::In(_, _)
            | Formula::Subset(_, _) => 4,
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
            Formula::PredApp(name, args) => {
                write!(f, "{name}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")?;
            }
            Formula::Eq(left, right) => write!(f, "{left} = {right}")?,
            Formula::In(elem, set) => write!(f, "{elem} in {set}")?,
            Formula::Subset(left, right) => write!(f, "{left} subset {right}")?,
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
            Formula::Forall {
                var,
                var_type,
                body,
            } => {
                write!(f, "forall {var} : {var_type}, ")?;
                body.fmt_with_prec(f, my_prec)?;
            }
            Formula::Exists {
                var,
                var_type,
                body,
            } => {
                write!(f, "exists {var} : {var_type}, ")?;
                body.fmt_with_prec(f, my_prec)?;
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
    Predicate(Vec<Type>),
    Type,
    Term(Type),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: Name,
    pub kind: ParamKind,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SchemaSubst {
    pub type_args: HashMap<Name, Type>,
    pub term_args: HashMap<Name, Term>,
    pub formula_args: HashMap<Name, Formula>,
    pub predicate_args: HashMap<Name, Name>,
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
    EqRefl(Term),
    EqSubst {
        eq_proof: Box<Proof>,
        proof_body: Box<Proof>,
        target: Formula,
    },
    Convert {
        proof_body: Box<Proof>,
        target: Formula,
    },
    ForallIntro {
        var: Name,
        var_type: Type,
        body: Box<Proof>,
    },
    ForallElim {
        proof_forall: Box<Proof>,
        arg: Term,
    },
    ExistsIntro {
        witness: Term,
        proof_body: Box<Proof>,
        exists_formula: Formula,
    },
    ExistsElim {
        proof_exists: Box<Proof>,
        witness_name: Name,
        hyp_name: Name,
        body: Box<Proof>,
        target: Formula,
    },
    NatInd {
        var_name: Name,
        target: Formula,
        base_case: Box<Proof>,
        step_var: Name,
        ih_name: Name,
        step_case: Box<Proof>,
    },
    TheoremRef {
        name: Name,
        subst: SchemaSubst,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermBinding {
    pub name: Name,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncDecl {
    pub args: Vec<Type>,
    pub result: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FormulaDef {
    pub name: Name,
    pub params: Vec<Param>,
    pub body: Formula,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Context {
    type_vars: Vec<Name>,
    prop_vars: Vec<Name>,
    pred_vars: HashMap<Name, Vec<Type>>,
    term_vars: Vec<TermBinding>,
    proof_vars: Vec<ProofBinding>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_proof(&mut self, name: Name, formula: Formula) {
        self.proof_vars.push(ProofBinding { name, formula });
    }

    pub fn add_type_var(&mut self, name: Name) {
        self.type_vars.push(name);
    }

    pub fn add_prop_var(&mut self, name: Name) {
        self.prop_vars.push(name);
    }

    pub fn add_predicate_var(&mut self, name: Name, args: Vec<Type>) {
        self.pred_vars.insert(name, args);
    }

    pub fn add_term(&mut self, name: Name, ty: Type) {
        self.term_vars.push(TermBinding { name, ty });
    }

    pub fn has_type_var(&self, name: &str) -> bool {
        self.type_vars.iter().rev().any(|var| var == name)
    }

    pub fn has_prop_var(&self, name: &str) -> bool {
        self.prop_vars.iter().rev().any(|var| var == name)
    }

    pub fn lookup_predicate_var(&self, name: &str) -> Option<&[Type]> {
        self.pred_vars.get(name).map(Vec::as_slice)
    }

    pub fn lookup_term(&self, name: &str) -> Option<&Type> {
        self.term_vars
            .iter()
            .rev()
            .find(|binding| binding.name == name)
            .map(|binding| &binding.ty)
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

    fn has_schema_name(&self, name: &str) -> bool {
        self.has_type_var(name)
            || self.has_prop_var(name)
            || self.lookup_predicate_var(name).is_some()
            || self.lookup_term(name).is_some()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Theorem {
    pub name: Name,
    pub params: Vec<Param>,
    pub statement: Formula,
    pub proof: Option<Proof>,
    pub mode_used: LogicMode,
    pub is_axiom: bool,
}

#[derive(Clone, Debug, Default)]
pub struct Env {
    sorts: HashMap<Name, Type>,
    consts: HashMap<Name, Type>,
    funcs: HashMap<Name, FuncDecl>,
    preds: HashMap<Name, Vec<Type>>,
    defs: HashMap<Name, FormulaDef>,
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

    pub fn add_sort(&mut self, name: Name) {
        self.sorts.insert(name.clone(), Type::Named(name));
    }

    pub fn add_const(&mut self, name: Name, ty: Type) {
        self.consts.insert(name, ty);
    }

    pub fn add_func(&mut self, name: Name, args: Vec<Type>, result: Type) {
        self.funcs.insert(name, FuncDecl { args, result });
    }

    pub fn add_pred(&mut self, name: Name, args: Vec<Type>) {
        self.preds.insert(name, args);
    }

    pub fn add_def(&mut self, def: FormulaDef) {
        self.defs.insert(def.name.clone(), def);
    }

    fn formula_def(&self, name: &str) -> Option<&FormulaDef> {
        self.defs.get(name)
    }

    fn has_sort(&self, name: &str) -> bool {
        self.sorts.contains_key(name)
    }

    fn has_const(&self, name: &str) -> bool {
        self.consts.contains_key(name)
    }

    fn has_func(&self, name: &str) -> bool {
        self.funcs.contains_key(name)
    }

    fn has_pred(&self, name: &str) -> bool {
        self.preds.contains_key(name)
    }

    fn has_theorem(&self, name: &str) -> bool {
        self.theorems.contains_key(name)
    }

    fn has_def(&self, name: &str) -> bool {
        self.defs.contains_key(name)
    }

    fn has_top_level_name(&self, name: &str) -> bool {
        is_builtin_name(name)
            || self.has_sort(name)
            || self.has_const(name)
            || self.has_func(name)
            || self.has_pred(name)
            || self.has_def(name)
            || self.has_theorem(name)
    }
}

fn is_builtin_name(name: &str) -> bool {
    matches!(
        name,
        "Nat" | "Set" | "succ" | "add" | "empty" | "singleton" | "union" | "inter" | "diff"
    )
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
    pub is_axiom: bool,
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
            Command::Sort(name) => {
                if env.has_top_level_name(&name) {
                    result.diagnostics.push(Diagnostic::error(format!(
                        "cannot redeclare `{name}` as a sort"
                    )));
                    continue;
                }
                env.add_sort(name);
            }
            Command::Const(name, ty) => {
                if env.has_top_level_name(&name) {
                    result.diagnostics.push(Diagnostic::error(format!(
                        "cannot redeclare `{name}` as a constant"
                    )));
                    continue;
                }
                if let Err(err) = validate_type(&env, &Context::new(), &ty) {
                    result.diagnostics.push(
                        Diagnostic::error(format!("constant `{name}` has invalid type"))
                            .with_note(err.message),
                    );
                    continue;
                }
                env.add_const(name, ty);
            }
            Command::Func(name, args, result_type) => {
                if env.has_top_level_name(&name) {
                    result.diagnostics.push(Diagnostic::error(format!(
                        "cannot redeclare `{name}` as a function"
                    )));
                    continue;
                }
                let empty_ctx = Context::new();
                let mut invalid_type = None;
                for ty in args.iter().chain(std::iter::once(&result_type)) {
                    if let Err(err) = validate_type(&env, &empty_ctx, ty) {
                        invalid_type = Some(err);
                        break;
                    }
                }
                if let Some(err) = invalid_type {
                    result.diagnostics.push(
                        Diagnostic::error(format!("function `{name}` has invalid type"))
                            .with_note(err.message),
                    );
                    continue;
                }
                env.add_func(name, args, result_type);
            }
            Command::Pred(name, args) => {
                if env.has_top_level_name(&name) {
                    result.diagnostics.push(Diagnostic::error(format!(
                        "cannot redeclare `{name}` as a predicate"
                    )));
                    continue;
                }
                let empty_ctx = Context::new();
                if let Err(err) = args
                    .iter()
                    .try_for_each(|arg| validate_type(&env, &empty_ctx, arg))
                {
                    result.diagnostics.push(
                        Diagnostic::error(format!("predicate `{name}` has invalid argument type"))
                            .with_note(err.message),
                    );
                    continue;
                }
                env.add_pred(name, args);
            }
            Command::Def(decl) => {
                if env.has_top_level_name(&decl.name) {
                    result.diagnostics.push(Diagnostic::error(format!(
                        "cannot redeclare `{}` as a definition",
                        decl.name
                    )));
                    continue;
                }
                if let Err(err) = validate_formula_def_params(&decl.params) {
                    result.diagnostics.push(
                        Diagnostic::error(format!(
                            "definition `{}` has invalid parameters",
                            decl.name
                        ))
                        .with_note(err.message),
                    );
                    continue;
                }
                let def_ctx = match build_theorem_context(&env, &decl.params) {
                    Ok(ctx) => ctx,
                    Err(err) => {
                        result.diagnostics.push(
                            Diagnostic::error(format!(
                                "definition `{}` has invalid parameters",
                                decl.name
                            ))
                            .with_note(err.message),
                        );
                        continue;
                    }
                };
                if let Err(err) = validate_formula(&env, &def_ctx, &decl.body) {
                    result.diagnostics.push(
                        Diagnostic::error(format!("definition `{}` has invalid body", decl.name))
                            .with_note(err.message)
                            .with_note(format!("body: {}", decl.body)),
                    );
                    continue;
                }
                env.add_def(FormulaDef {
                    name: decl.name,
                    params: decl.params,
                    body: decl.body,
                });
            }
            Command::Axiom(decl) => {
                if env.has_top_level_name(&decl.name) {
                    result.diagnostics.push(Diagnostic::error(format!(
                        "cannot redeclare `{}` as an axiom",
                        decl.name
                    )));
                    continue;
                }
                let axiom_ctx = match build_theorem_context(&env, &decl.params) {
                    Ok(ctx) => ctx,
                    Err(err) => {
                        result.diagnostics.push(
                            Diagnostic::error(format!(
                                "axiom `{}` has invalid parameters",
                                decl.name
                            ))
                            .with_note(err.message),
                        );
                        continue;
                    }
                };
                if let Err(err) = validate_formula(&env, &axiom_ctx, &decl.statement) {
                    result.diagnostics.push(
                        Diagnostic::error(format!("axiom `{}` has invalid statement", decl.name))
                            .with_note(err.message)
                            .with_note(format!("target: {}", decl.statement)),
                    );
                    continue;
                }

                env.add_theorem(Theorem {
                    name: decl.name.clone(),
                    params: decl.params,
                    statement: decl.statement,
                    proof: None,
                    mode_used: mode,
                    is_axiom: true,
                });
                result.theorems.push(CheckedTheorem {
                    name: decl.name,
                    mode_used: mode,
                    is_axiom: true,
                });
            }
            Command::Theorem(decl) => {
                if env.has_top_level_name(&decl.name) {
                    result.diagnostics.push(Diagnostic::error(format!(
                        "cannot redeclare `{}` as a theorem",
                        decl.name
                    )));
                    continue;
                }
                let theorem_ctx = match build_theorem_context(&env, &decl.params) {
                    Ok(ctx) => ctx,
                    Err(err) => {
                        result.diagnostics.push(
                            Diagnostic::error(format!(
                                "theorem `{}` has invalid parameters",
                                decl.name
                            ))
                            .with_note(err.message),
                        );
                        continue;
                    }
                };
                if let Err(err) = validate_formula(&env, &theorem_ctx, &decl.statement) {
                    result.diagnostics.push(
                        Diagnostic::error(format!("theorem `{}` has invalid statement", decl.name))
                            .with_note(err.message)
                            .with_note(format!("target: {}", decl.statement)),
                    );
                    continue;
                }
                let proof = match prove(
                    &env,
                    theorem_ctx.clone(),
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

                let mode_used = match check_proof(&env, &theorem_ctx, &proof, &decl.statement, mode)
                {
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
                    proof: Some(proof),
                    mode_used,
                    is_axiom: false,
                });
                result.theorems.push(CheckedTheorem {
                    name: decl.name,
                    mode_used,
                    is_axiom: false,
                });
            }
        }
    }

    result
}

fn validate_formula_def_params(params: &[Param]) -> Result<(), ValidationError> {
    for param in params {
        if matches!(param.kind, ParamKind::Prop | ParamKind::Predicate(_)) {
            return Err(ValidationError::new(
                "formula definitions currently support only type and term parameters",
            ));
        }
    }
    Ok(())
}

fn build_theorem_context(env: &Env, params: &[Param]) -> Result<Context, ValidationError> {
    let mut ctx = Context::new();
    for param in params {
        if env.has_top_level_name(&param.name) || ctx.has_schema_name(&param.name) {
            return Err(ValidationError::new(format!(
                "parameter `{}` is already declared",
                param.name
            )));
        }

        match &param.kind {
            ParamKind::Prop => ctx.add_prop_var(param.name.clone()),
            ParamKind::Predicate(args) => {
                for arg in args {
                    validate_type(env, &ctx, arg)?;
                }
                ctx.add_predicate_var(param.name.clone(), args.clone());
            }
            ParamKind::Type => ctx.add_type_var(param.name.clone()),
            ParamKind::Term(ty) => {
                validate_type(env, &ctx, ty)?;
                ctx.add_term(param.name.clone(), ty.clone());
            }
        }
    }
    Ok(ctx)
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
struct ValidationError {
    message: String,
}

impl ValidationError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl From<ValidationError> for KernelError {
    fn from(value: ValidationError) -> Self {
        KernelError::new(value.message)
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
    validate_formula(env, ctx, expected)?;
    let checked = infer_proof(env, ctx, proof, allowed_mode)?;
    validate_formula(env, ctx, &checked.formula)?;
    if formulas_def_eq(env, ctx, &checked.formula, expected)? {
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
            validate_formula(env, ctx, target)?;
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
            let formula = normalize_formula_defs(env, ctx, &checked.formula)?;
            let Formula::And(left, _) = formula else {
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
            let formula = normalize_formula_defs(env, ctx, &checked.formula)?;
            let Formula::And(_, right) = formula else {
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
            validate_formula(env, ctx, right_formula)?;
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
            validate_formula(env, ctx, left_formula)?;
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
            let formula = normalize_formula_defs(env, ctx, &checked_or.formula)?;
            let Formula::Or(left_formula, right_formula) = formula else {
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
            validate_formula(env, ctx, hyp_formula)?;
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
            let formula = normalize_formula_defs(env, ctx, &checked_imp.formula)?;
            let Formula::Implies(premise, conclusion) = formula else {
                return Err(KernelError::new("apply expected an implication"));
            };
            let arg_mode = check_proof(env, ctx, proof_arg, &premise, allowed_mode)?;
            Ok(CheckedProof {
                formula: *conclusion,
                mode_used: checked_imp.mode_used.combine(arg_mode),
            })
        }
        Proof::EqRefl(term) => {
            term_type(env, ctx, term)?;
            Ok(CheckedProof {
                formula: Formula::eq(term.clone(), term.clone()),
                mode_used: LogicMode::Constructive,
            })
        }
        Proof::EqSubst {
            eq_proof,
            proof_body,
            target,
        } => {
            validate_formula(env, ctx, target)?;
            let checked_eq = infer_proof(env, ctx, eq_proof, allowed_mode)?;
            let formula = normalize_formula_defs(env, ctx, &checked_eq.formula)?;
            let Formula::Eq(left, right) = formula else {
                return Err(KernelError::new("rewrite expected an equality proof"));
            };
            let checked_body = infer_proof(env, ctx, proof_body, allowed_mode)?;
            if !formula_rewrite_matches(&checked_body.formula, target, &left, &right) {
                return Err(KernelError::new(format!(
                    "cannot rewrite `{}` to `{target}` using `{left} = {right}`",
                    checked_body.formula
                )));
            }
            Ok(CheckedProof {
                formula: target.clone(),
                mode_used: checked_eq.mode_used.combine(checked_body.mode_used),
            })
        }
        Proof::Convert { proof_body, target } => {
            validate_formula(env, ctx, target)?;
            let checked_body = infer_proof(env, ctx, proof_body, allowed_mode)?;
            if !formulas_def_eq(env, ctx, &checked_body.formula, target)? {
                return Err(KernelError::new(format!(
                    "cannot convert proof of `{}` to `{target}` by unfolding definitions",
                    checked_body.formula
                )));
            }
            Ok(CheckedProof {
                formula: target.clone(),
                mode_used: checked_body.mode_used,
            })
        }
        Proof::ForallIntro {
            var,
            var_type,
            body,
        } => {
            validate_type(env, ctx, var_type)?;
            let mut body_ctx = ctx.clone();
            body_ctx.add_term(var.clone(), var_type.clone());
            let body = infer_proof(env, &body_ctx, body, allowed_mode)?;
            Ok(CheckedProof {
                formula: Formula::forall(var.clone(), var_type.clone(), body.formula),
                mode_used: body.mode_used,
            })
        }
        Proof::ForallElim { proof_forall, arg } => {
            let checked = infer_proof(env, ctx, proof_forall, allowed_mode)?;
            let formula = normalize_formula_defs(env, ctx, &checked.formula)?;
            let Formula::Forall {
                var,
                var_type,
                body,
            } = formula
            else {
                return Err(KernelError::new(
                    "first-order application expects a universal proof",
                ));
            };
            let actual = term_type(env, ctx, arg)?;
            if actual != var_type {
                return Err(KernelError::new(format!(
                    "term `{arg}` has type `{actual}`, but expected `{var_type}`"
                )));
            }
            Ok(CheckedProof {
                formula: subst_formula_term(&body, &var, arg),
                mode_used: checked.mode_used,
            })
        }
        Proof::ExistsIntro {
            witness,
            proof_body,
            exists_formula,
        } => {
            validate_formula(env, ctx, exists_formula)?;
            let Formula::Exists {
                var,
                var_type,
                body,
            } = exists_formula
            else {
                return Err(KernelError::new(
                    "exists_intro must target an existential formula",
                ));
            };
            let actual = term_type(env, ctx, witness)?;
            if actual != *var_type {
                return Err(KernelError::new(format!(
                    "witness `{witness}` has type `{actual}`, but expected `{var_type}`"
                )));
            }
            let expected_body = subst_formula_term(body, var, witness);
            let mode_used = check_proof(env, ctx, proof_body, &expected_body, allowed_mode)?;
            Ok(CheckedProof {
                formula: exists_formula.clone(),
                mode_used,
            })
        }
        Proof::ExistsElim {
            proof_exists,
            witness_name,
            hyp_name,
            body,
            target,
        } => {
            validate_formula(env, ctx, target)?;
            let checked_exists = infer_proof(env, ctx, proof_exists, allowed_mode)?;
            let formula = normalize_formula_defs(env, ctx, &checked_exists.formula)?;
            let Formula::Exists {
                var,
                var_type,
                body: exists_body,
            } = formula
            else {
                return Err(KernelError::new(
                    "cases can only eliminate an existential or disjunction",
                ));
            };
            if formula_has_free_term(target, witness_name) {
                return Err(KernelError::new(format!(
                    "existential witness `{witness_name}` escapes the target"
                )));
            }
            let witness = Term::Var(witness_name.clone());
            let hyp_formula = subst_formula_term(&exists_body, &var, &witness);
            let mut body_ctx = ctx.clone();
            body_ctx.add_term(witness_name.clone(), var_type);
            body_ctx.add_proof(hyp_name.clone(), hyp_formula);
            let body_mode = check_proof(env, &body_ctx, body, target, allowed_mode)?;
            Ok(CheckedProof {
                formula: target.clone(),
                mode_used: checked_exists.mode_used.combine(body_mode),
            })
        }
        Proof::NatInd {
            var_name,
            target,
            base_case,
            step_var,
            ih_name,
            step_case,
        } => {
            validate_formula(env, ctx, target)?;
            let Some(var_type) = ctx.lookup_term(var_name) else {
                return Err(KernelError::new(format!(
                    "induction variable `{var_name}` is not in scope"
                )));
            };
            if var_type != &Type::Nat {
                return Err(KernelError::new(format!(
                    "induction variable `{var_name}` has type `{var_type}`, but expected `Nat`"
                )));
            }
            for binding in ctx.proofs() {
                if formula_has_free_term(&binding.formula, var_name) {
                    return Err(KernelError::new(format!(
                        "cannot induct on `{var_name}` while hypothesis `{}` depends on it",
                        binding.name
                    )));
                }
            }

            let base_target = subst_formula_term(target, var_name, &Term::Zero);
            let base_mode = check_proof(env, ctx, base_case, &base_target, allowed_mode)?;

            let mut step_ctx = ctx.clone();
            step_ctx.add_term(step_var.clone(), Type::Nat);
            let step_var_term = Term::Var(step_var.clone());
            let ih_formula = subst_formula_term(target, var_name, &step_var_term);
            step_ctx.add_proof(ih_name.clone(), ih_formula);
            let step_target =
                subst_formula_term(target, var_name, &Term::Succ(Box::new(step_var_term)));
            let step_mode = check_proof(env, &step_ctx, step_case, &step_target, allowed_mode)?;

            Ok(CheckedProof {
                formula: target.clone(),
                mode_used: base_mode.combine(step_mode),
            })
        }
        Proof::TheoremRef { name, subst } => {
            let Some(theorem) = env.theorem(name) else {
                return Err(KernelError::new(format!("unknown theorem `{name}`")));
            };
            let formula = instantiate_theorem(env, ctx, theorem, subst)?;
            validate_formula(env, ctx, &formula)?;
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

            validate_formula(env, ctx, target)?;
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
    env: &Env,
    ctx: &Context,
    theorem: &Theorem,
    subst: &SchemaSubst,
) -> Result<Formula, KernelError> {
    for param in &theorem.params {
        match &param.kind {
            ParamKind::Type => {
                let Some(arg) = subst.type_args.get(&param.name) else {
                    return Err(KernelError::new(format!(
                        "missing type argument `{}` for theorem `{}`",
                        param.name, theorem.name
                    )));
                };
                validate_type(env, ctx, arg)?;
            }
            ParamKind::Prop => {
                let Some(arg) = subst.formula_args.get(&param.name) else {
                    return Err(KernelError::new(format!(
                        "missing proposition argument `{}` for theorem `{}`",
                        param.name, theorem.name
                    )));
                };
                validate_formula(env, ctx, arg)?;
            }
            ParamKind::Predicate(args) => {
                let Some(arg) = subst.predicate_args.get(&param.name) else {
                    return Err(KernelError::new(format!(
                        "missing predicate argument `{}` for theorem `{}`",
                        param.name, theorem.name
                    )));
                };
                let Some(signature) = predicate_signature(env, ctx, arg) else {
                    return Err(KernelError::new(format!("unknown predicate `{arg}`")));
                };
                let expected: Vec<Type> =
                    args.iter().map(|ty| subst_type_schema(ty, subst)).collect();
                if signature != expected.as_slice() {
                    return Err(KernelError::new(format!(
                        "predicate `{arg}` does not match expected schema type"
                    )));
                }
            }
            ParamKind::Term(ty) => {
                let Some(arg) = subst.term_args.get(&param.name) else {
                    return Err(KernelError::new(format!(
                        "missing term argument `{}` for theorem `{}`",
                        param.name, theorem.name
                    )));
                };
                let actual = validate_term(env, ctx, arg)?;
                let expected = subst_type_schema(ty, subst);
                if actual != expected {
                    return Err(KernelError::new(format!(
                        "term argument `{}` has type `{actual}`, but expected `{expected}`",
                        param.name
                    )));
                }
            }
        }
    }

    Ok(subst_formula_schema(&theorem.statement, subst))
}

fn validate_type(env: &Env, ctx: &Context, ty: &Type) -> Result<(), ValidationError> {
    match ty {
        Type::Nat => Ok(()),
        Type::Set(elem) => validate_type(env, ctx, elem),
        Type::Named(name) if env.has_sort(name) || ctx.has_type_var(name) => Ok(()),
        Type::Named(name) => Err(ValidationError::new(format!("unknown type `{name}`"))),
    }
}

fn validate_term(env: &Env, ctx: &Context, term: &Term) -> Result<Type, ValidationError> {
    match term {
        Term::Var(name) => ctx
            .lookup_term(name)
            .or_else(|| env.consts.get(name))
            .cloned()
            .ok_or_else(|| ValidationError::new(format!("unknown term `{name}`"))),
        Term::App(name, args) => {
            let Some(func) = env.funcs.get(name) else {
                return Err(ValidationError::new(format!("unknown function `{name}`")));
            };
            if func.args.len() != args.len() {
                return Err(ValidationError::new(format!(
                    "function `{name}` expects {} argument(s), but got {}",
                    func.args.len(),
                    args.len()
                )));
            }
            for (idx, (arg, expected)) in args.iter().zip(func.args.iter()).enumerate() {
                let actual = validate_term(env, ctx, arg)?;
                if &actual != expected {
                    return Err(ValidationError::new(format!(
                        "argument {} of `{name}` has type `{actual}`, but expected `{expected}`",
                        idx + 1
                    )));
                }
            }
            Ok(func.result.clone())
        }
        Term::Zero => Ok(Type::Nat),
        Term::Succ(term) => {
            let actual = validate_term(env, ctx, term)?;
            if actual == Type::Nat {
                Ok(Type::Nat)
            } else {
                Err(ValidationError::new(format!(
                    "succ argument has type `{actual}`, but expected `Nat`"
                )))
            }
        }
        Term::Add(left, right) => {
            for (idx, term) in [left.as_ref(), right.as_ref()].iter().enumerate() {
                let actual = validate_term(env, ctx, term)?;
                if actual != Type::Nat {
                    return Err(ValidationError::new(format!(
                        "argument {} of `add` has type `{actual}`, but expected `Nat`",
                        idx + 1
                    )));
                }
            }
            Ok(Type::Nat)
        }
        Term::EmptySet(elem_ty) => {
            validate_type(env, ctx, elem_ty)?;
            Ok(Type::Set(Box::new(elem_ty.clone())))
        }
        Term::Singleton(elem) => {
            let elem_ty = validate_term(env, ctx, elem)?;
            Ok(Type::Set(Box::new(elem_ty)))
        }
        Term::Union(left, right) | Term::Inter(left, right) | Term::Diff(left, right) => {
            let left_ty = validate_term(env, ctx, left)?;
            let right_ty = validate_term(env, ctx, right)?;
            let Type::Set(left_elem) = left_ty else {
                return Err(ValidationError::new(format!(
                    "set operation argument 1 has type `{left_ty}`, but expected a set"
                )));
            };
            let Type::Set(right_elem) = right_ty else {
                return Err(ValidationError::new(format!(
                    "set operation argument 2 has type `{right_ty}`, but expected a set"
                )));
            };
            if left_elem == right_elem {
                Ok(Type::Set(left_elem))
            } else {
                Err(ValidationError::new(format!(
                    "set operation combines `Set {left_elem}` with `Set {right_elem}`"
                )))
            }
        }
    }
}

fn predicate_signature<'a>(env: &'a Env, ctx: &'a Context, name: &str) -> Option<&'a [Type]> {
    ctx.lookup_predicate_var(name)
        .or_else(|| env.preds.get(name).map(Vec::as_slice))
}

fn validate_formula(env: &Env, ctx: &Context, formula: &Formula) -> Result<(), ValidationError> {
    match formula {
        Formula::True | Formula::False => Ok(()),
        Formula::Atom(name) => {
            if ctx.has_prop_var(name)
                || matches!(predicate_signature(env, ctx, name), Some(sig) if sig.is_empty())
            {
                Ok(())
            } else if let Some(def) = env.formula_def(name) {
                instantiate_formula_def(env, ctx, def, &[]).map(|_| ())
            } else {
                Err(ValidationError::new(format!(
                    "unknown proposition variable `{name}`"
                )))
            }
        }
        Formula::Eq(left, right) => {
            let left_type = validate_term(env, ctx, left)?;
            let right_type = validate_term(env, ctx, right)?;
            if left_type == right_type {
                Ok(())
            } else {
                Err(ValidationError::new(format!(
                    "equality compares `{left}` of type `{left_type}` with `{right}` of type `{right_type}`"
                )))
            }
        }
        Formula::In(elem, set) => {
            let elem_type = validate_term(env, ctx, elem)?;
            let set_type = validate_term(env, ctx, set)?;
            match set_type {
                Type::Set(expected) if elem_type == *expected => Ok(()),
                Type::Set(expected) => Err(ValidationError::new(format!(
                    "membership compares `{elem}` of type `{elem_type}` with a set of `{expected}`"
                ))),
                other => Err(ValidationError::new(format!(
                    "right side of membership has type `{other}`, but expected a set"
                ))),
            }
        }
        Formula::Subset(left, right) => {
            let left_type = validate_term(env, ctx, left)?;
            let right_type = validate_term(env, ctx, right)?;
            match (&left_type, &right_type) {
                (Type::Set(left_elem), Type::Set(right_elem)) if left_elem == right_elem => Ok(()),
                (Type::Set(_), Type::Set(_)) => Err(ValidationError::new(format!(
                    "subset compares `{left}` of type `{left_type}` with `{right}` of type `{right_type}`"
                ))),
                _ => Err(ValidationError::new(format!(
                    "subset expects set arguments, but got `{left_type}` and `{right_type}`"
                ))),
            }
        }
        Formula::PredApp(name, args) => {
            if let Some(signature) = predicate_signature(env, ctx, name) {
                if signature.len() != args.len() {
                    return Err(ValidationError::new(format!(
                        "predicate `{name}` expects {} argument(s), but got {}",
                        signature.len(),
                        args.len()
                    )));
                }
                for (idx, (arg, expected)) in args.iter().zip(signature.iter()).enumerate() {
                    let actual = validate_term(env, ctx, arg)?;
                    if &actual != expected {
                        return Err(ValidationError::new(format!(
                            "argument {} of `{name}` has type `{actual}`, but expected `{expected}`",
                            idx + 1
                        )));
                    }
                }
                Ok(())
            } else if let Some(def) = env.formula_def(name) {
                instantiate_formula_def(env, ctx, def, args).map(|_| ())
            } else {
                Err(ValidationError::new(format!("unknown predicate `{name}`")))
            }
        }
        Formula::And(left, right) | Formula::Or(left, right) | Formula::Implies(left, right) => {
            validate_formula(env, ctx, left)?;
            validate_formula(env, ctx, right)
        }
        Formula::Forall {
            var,
            var_type,
            body,
        }
        | Formula::Exists {
            var,
            var_type,
            body,
        } => {
            validate_type(env, ctx, var_type)?;
            let mut body_ctx = ctx.clone();
            body_ctx.add_term(var.clone(), var_type.clone());
            validate_formula(env, &body_ctx, body)
        }
    }
}

fn instantiate_formula_def(
    env: &Env,
    ctx: &Context,
    def: &FormulaDef,
    args: &[Term],
) -> Result<Formula, ValidationError> {
    let expected_args = def
        .params
        .iter()
        .filter(|param| matches!(param.kind, ParamKind::Term(_)))
        .count();
    if expected_args != args.len() {
        return Err(ValidationError::new(format!(
            "definition `{}` expects {expected_args} argument(s), but got {}",
            def.name,
            args.len()
        )));
    }

    let mut schema_subst = SchemaSubst::default();
    let mut term_subst = HashMap::new();
    let mut args = args.iter();
    let mut arg_idx = 0usize;

    for param in &def.params {
        match &param.kind {
            ParamKind::Type => {}
            ParamKind::Term(ty) => {
                let Some(arg) = args.next() else {
                    return Err(ValidationError::new(format!(
                        "definition `{}` expects {expected_args} argument(s)",
                        def.name
                    )));
                };
                let actual = validate_term(env, ctx, arg)?;
                unify_type(ty, &actual, &def.params, &mut schema_subst).map_err(|_| {
                    let expected = subst_type_schema(ty, &schema_subst);
                    ValidationError::new(format!(
                        "argument {} of definition `{}` has type `{actual}`, but expected `{expected}`",
                        arg_idx + 1,
                        def.name
                    ))
                })?;
                term_subst.insert(param.name.clone(), arg.clone());
                arg_idx += 1;
            }
            ParamKind::Prop | ParamKind::Predicate(_) => {
                return Err(ValidationError::new(
                    "formula definitions currently support only type and term parameters",
                ));
            }
        }
    }

    for param in &def.params {
        if matches!(param.kind, ParamKind::Type)
            && !schema_subst.type_args.contains_key(&param.name)
        {
            return Err(ValidationError::new(format!(
                "cannot infer type argument `{}` for definition `{}`",
                param.name, def.name
            )));
        }
    }

    let body = subst_formula_terms(&subst_formula_schema(&def.body, &schema_subst), &term_subst);
    validate_formula(env, ctx, &body)?;
    Ok(body)
}

fn formulas_def_eq(
    env: &Env,
    ctx: &Context,
    left: &Formula,
    right: &Formula,
) -> Result<bool, ValidationError> {
    Ok(normalize_formula_defs(env, ctx, left)? == normalize_formula_defs(env, ctx, right)?)
}

fn normalize_formula_defs(
    env: &Env,
    ctx: &Context,
    formula: &Formula,
) -> Result<Formula, ValidationError> {
    unfold_formula_defs(env, ctx, formula, None).map(|(formula, _)| formula)
}

fn unfold_named_formula_def(
    env: &Env,
    ctx: &Context,
    formula: &Formula,
    name: &str,
) -> Result<(Formula, bool), ValidationError> {
    unfold_formula_defs(env, ctx, formula, Some(name))
}

fn unfold_formula_defs(
    env: &Env,
    ctx: &Context,
    formula: &Formula,
    only: Option<&str>,
) -> Result<(Formula, bool), ValidationError> {
    match formula {
        Formula::True => Ok((Formula::True, false)),
        Formula::False => Ok((Formula::False, false)),
        Formula::Atom(name) => {
            if only.is_none_or(|only| only == name) {
                if let Some(def) = env.formula_def(name) {
                    let unfolded = instantiate_formula_def(env, ctx, def, &[])?;
                    if only.is_none() {
                        let (unfolded, _) = unfold_formula_defs(env, ctx, &unfolded, only)?;
                        return Ok((unfolded, true));
                    }
                    return Ok((unfolded, true));
                }
            }
            Ok((formula.clone(), false))
        }
        Formula::PredApp(name, args) => {
            if only.is_none_or(|only| only == name) {
                if let Some(def) = env.formula_def(name) {
                    let unfolded = instantiate_formula_def(env, ctx, def, args)?;
                    if only.is_none() {
                        let (unfolded, _) = unfold_formula_defs(env, ctx, &unfolded, only)?;
                        return Ok((unfolded, true));
                    }
                    return Ok((unfolded, true));
                }
            }
            Ok((formula.clone(), false))
        }
        Formula::Eq(left, right) => {
            if only.is_some() {
                return Ok((formula.clone(), false));
            }
            let simplified =
                Formula::eq(normalize_term_compute(left), normalize_term_compute(right));
            Ok((simplified.clone(), &simplified != formula))
        }
        Formula::In(elem, set) => {
            if only.is_some() {
                return Ok((formula.clone(), false));
            }
            let elem = normalize_term_compute(elem);
            let set = normalize_term_compute(set);
            let simplified = match set {
                Term::EmptySet(_) => Formula::False,
                Term::Singleton(singleton_elem) => Formula::eq(elem, *singleton_elem),
                Term::Union(left, right) => Formula::or(
                    Formula::membership(elem.clone(), *left),
                    Formula::membership(elem, *right),
                ),
                Term::Inter(left, right) => Formula::and(
                    Formula::membership(elem.clone(), *left),
                    Formula::membership(elem, *right),
                ),
                Term::Diff(left, right) => Formula::and(
                    Formula::membership(elem.clone(), *left),
                    Formula::negate(Formula::membership(elem, *right)),
                ),
                other => Formula::membership(elem, other),
            };
            let changed = &simplified != formula;
            if changed {
                let (simplified, _) = unfold_formula_defs(env, ctx, &simplified, only)?;
                Ok((simplified, true))
            } else {
                Ok((simplified, false))
            }
        }
        Formula::Subset(left, right) => {
            if only.is_some() {
                return Ok((formula.clone(), false));
            }
            let left = normalize_term_compute(left);
            let right = normalize_term_compute(right);
            let elem_ty = set_element_type(env, ctx, &left)?;
            let right_elem_ty = set_element_type(env, ctx, &right)?;
            if elem_ty != right_elem_ty {
                return Err(ValidationError::new(format!(
                    "subset compares `Set {elem_ty}` with `Set {right_elem_ty}`"
                )));
            }
            let var = fresh_set_element_name(ctx, &[&left, &right]);
            let elem = Term::Var(var.clone());
            let expanded = Formula::forall(
                var,
                elem_ty,
                Formula::implies(
                    Formula::membership(elem.clone(), left),
                    Formula::membership(elem, right),
                ),
            );
            let (simplified, _) = unfold_formula_defs(env, ctx, &expanded, only)?;
            Ok((simplified, true))
        }
        Formula::And(left, right) => {
            unfold_binary_formula(env, ctx, left, right, only, Formula::and)
        }
        Formula::Or(left, right) => unfold_binary_formula(env, ctx, left, right, only, Formula::or),
        Formula::Implies(left, right) => {
            unfold_binary_formula(env, ctx, left, right, only, Formula::implies)
        }
        Formula::Forall {
            var,
            var_type,
            body,
        } => {
            let mut body_ctx = ctx.clone();
            body_ctx.add_term(var.clone(), var_type.clone());
            let (body, changed) = unfold_formula_defs(env, &body_ctx, body, only)?;
            Ok((
                Formula::forall(var.clone(), var_type.clone(), body),
                changed,
            ))
        }
        Formula::Exists {
            var,
            var_type,
            body,
        } => {
            let mut body_ctx = ctx.clone();
            body_ctx.add_term(var.clone(), var_type.clone());
            let (body, changed) = unfold_formula_defs(env, &body_ctx, body, only)?;
            Ok((
                Formula::exists(var.clone(), var_type.clone(), body),
                changed,
            ))
        }
    }
}

fn normalize_term_compute(term: &Term) -> Term {
    match term {
        Term::Var(_) | Term::Zero | Term::EmptySet(_) => term.clone(),
        Term::App(name, args) => Term::App(
            name.clone(),
            args.iter().map(normalize_term_compute).collect(),
        ),
        Term::Succ(term) => Term::Succ(Box::new(normalize_term_compute(term))),
        Term::Add(left, right) => {
            let left = normalize_term_compute(left);
            let right = normalize_term_compute(right);
            match left {
                Term::Zero => right,
                Term::Succ(pred) => {
                    normalize_term_compute(&Term::Succ(Box::new(Term::Add(pred, Box::new(right)))))
                }
                other => Term::Add(Box::new(other), Box::new(right)),
            }
        }
        Term::Singleton(term) => Term::Singleton(Box::new(normalize_term_compute(term))),
        Term::Union(left, right) => Term::Union(
            Box::new(normalize_term_compute(left)),
            Box::new(normalize_term_compute(right)),
        ),
        Term::Inter(left, right) => Term::Inter(
            Box::new(normalize_term_compute(left)),
            Box::new(normalize_term_compute(right)),
        ),
        Term::Diff(left, right) => Term::Diff(
            Box::new(normalize_term_compute(left)),
            Box::new(normalize_term_compute(right)),
        ),
    }
}

fn set_element_type(env: &Env, ctx: &Context, set: &Term) -> Result<Type, ValidationError> {
    match validate_term(env, ctx, set)? {
        Type::Set(elem) => Ok(*elem),
        other => Err(ValidationError::new(format!(
            "term `{set}` has type `{other}`, but expected a set"
        ))),
    }
}

fn fresh_set_element_name(ctx: &Context, terms: &[&Term]) -> Name {
    for idx in 0.. {
        let candidate = if idx == 0 {
            "x".to_string()
        } else {
            format!("x{idx}")
        };
        if ctx.has_schema_name(&candidate)
            || terms.iter().any(|term| term_has_free_var(term, &candidate))
        {
            continue;
        }
        return candidate;
    }
    unreachable!("fresh name search is infinite")
}

fn unfold_binary_formula(
    env: &Env,
    ctx: &Context,
    left: &Formula,
    right: &Formula,
    only: Option<&str>,
    rebuild: fn(Formula, Formula) -> Formula,
) -> Result<(Formula, bool), ValidationError> {
    let (left, left_changed) = unfold_formula_defs(env, ctx, left, only)?;
    let (right, right_changed) = unfold_formula_defs(env, ctx, right, only)?;
    Ok((rebuild(left, right), left_changed || right_changed))
}

fn subst_type_schema(ty: &Type, subst: &SchemaSubst) -> Type {
    match ty {
        Type::Nat => Type::Nat,
        Type::Set(elem) => Type::Set(Box::new(subst_type_schema(elem, subst))),
        Type::Named(name) => subst
            .type_args
            .get(name)
            .cloned()
            .unwrap_or_else(|| Type::Named(name.clone())),
    }
}

fn subst_term_schema(term: &Term, subst: &SchemaSubst) -> Term {
    match term {
        Term::Var(name) => subst
            .term_args
            .get(name)
            .cloned()
            .unwrap_or_else(|| Term::Var(name.clone())),
        Term::App(name, args) => Term::App(
            name.clone(),
            args.iter()
                .map(|arg| subst_term_schema(arg, subst))
                .collect(),
        ),
        Term::Zero => Term::Zero,
        Term::Succ(term) => Term::Succ(Box::new(subst_term_schema(term, subst))),
        Term::Add(left, right) => Term::Add(
            Box::new(subst_term_schema(left, subst)),
            Box::new(subst_term_schema(right, subst)),
        ),
        Term::EmptySet(ty) => Term::EmptySet(subst_type_schema(ty, subst)),
        Term::Singleton(term) => Term::Singleton(Box::new(subst_term_schema(term, subst))),
        Term::Union(left, right) => Term::Union(
            Box::new(subst_term_schema(left, subst)),
            Box::new(subst_term_schema(right, subst)),
        ),
        Term::Inter(left, right) => Term::Inter(
            Box::new(subst_term_schema(left, subst)),
            Box::new(subst_term_schema(right, subst)),
        ),
        Term::Diff(left, right) => Term::Diff(
            Box::new(subst_term_schema(left, subst)),
            Box::new(subst_term_schema(right, subst)),
        ),
    }
}

fn subst_without_term_arg(subst: &SchemaSubst, var: &str) -> SchemaSubst {
    let mut scoped = subst.clone();
    scoped.term_args.remove(var);
    scoped
}

fn subst_formula_schema(formula: &Formula, subst: &SchemaSubst) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Atom(name) => subst
            .formula_args
            .get(name)
            .cloned()
            .unwrap_or_else(|| Formula::Atom(name.clone())),
        Formula::Eq(left, right) => Formula::eq(
            subst_term_schema(left, subst),
            subst_term_schema(right, subst),
        ),
        Formula::In(elem, set) => Formula::membership(
            subst_term_schema(elem, subst),
            subst_term_schema(set, subst),
        ),
        Formula::Subset(left, right) => Formula::subset(
            subst_term_schema(left, subst),
            subst_term_schema(right, subst),
        ),
        Formula::PredApp(name, args) => Formula::PredApp(
            subst
                .predicate_args
                .get(name)
                .cloned()
                .unwrap_or_else(|| name.clone()),
            args.iter()
                .map(|arg| subst_term_schema(arg, subst))
                .collect(),
        ),
        Formula::And(left, right) => Formula::and(
            subst_formula_schema(left, subst),
            subst_formula_schema(right, subst),
        ),
        Formula::Or(left, right) => Formula::or(
            subst_formula_schema(left, subst),
            subst_formula_schema(right, subst),
        ),
        Formula::Implies(left, right) => Formula::implies(
            subst_formula_schema(left, subst),
            subst_formula_schema(right, subst),
        ),
        Formula::Forall {
            var,
            var_type,
            body,
        } => {
            let scoped = subst_without_term_arg(subst, var);
            Formula::forall(
                var.clone(),
                subst_type_schema(var_type, subst),
                subst_formula_schema(body, &scoped),
            )
        }
        Formula::Exists {
            var,
            var_type,
            body,
        } => {
            let scoped = subst_without_term_arg(subst, var);
            Formula::exists(
                var.clone(),
                subst_type_schema(var_type, subst),
                subst_formula_schema(body, &scoped),
            )
        }
    }
}

fn term_type(env: &Env, ctx: &Context, term: &Term) -> Result<Type, KernelError> {
    validate_term(env, ctx, term).map_err(KernelError::from)
}

fn subst_term(term: &Term, var: &str, replacement: &Term) -> Term {
    match term {
        Term::Var(name) if name == var => replacement.clone(),
        Term::Var(_) => term.clone(),
        Term::App(name, args) => Term::App(
            name.clone(),
            args.iter()
                .map(|arg| subst_term(arg, var, replacement))
                .collect(),
        ),
        Term::Zero => Term::Zero,
        Term::Succ(term) => Term::Succ(Box::new(subst_term(term, var, replacement))),
        Term::Add(left, right) => Term::Add(
            Box::new(subst_term(left, var, replacement)),
            Box::new(subst_term(right, var, replacement)),
        ),
        Term::EmptySet(ty) => Term::EmptySet(ty.clone()),
        Term::Singleton(term) => Term::Singleton(Box::new(subst_term(term, var, replacement))),
        Term::Union(left, right) => Term::Union(
            Box::new(subst_term(left, var, replacement)),
            Box::new(subst_term(right, var, replacement)),
        ),
        Term::Inter(left, right) => Term::Inter(
            Box::new(subst_term(left, var, replacement)),
            Box::new(subst_term(right, var, replacement)),
        ),
        Term::Diff(left, right) => Term::Diff(
            Box::new(subst_term(left, var, replacement)),
            Box::new(subst_term(right, var, replacement)),
        ),
    }
}

fn subst_formula_term(formula: &Formula, var: &str, replacement: &Term) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Atom(name) => Formula::Atom(name.clone()),
        Formula::Eq(left, right) => Formula::eq(
            subst_term(left, var, replacement),
            subst_term(right, var, replacement),
        ),
        Formula::In(elem, set) => Formula::membership(
            subst_term(elem, var, replacement),
            subst_term(set, var, replacement),
        ),
        Formula::Subset(left, right) => Formula::subset(
            subst_term(left, var, replacement),
            subst_term(right, var, replacement),
        ),
        Formula::PredApp(name, args) => Formula::PredApp(
            name.clone(),
            args.iter()
                .map(|arg| subst_term(arg, var, replacement))
                .collect(),
        ),
        Formula::And(left, right) => Formula::and(
            subst_formula_term(left, var, replacement),
            subst_formula_term(right, var, replacement),
        ),
        Formula::Or(left, right) => Formula::or(
            subst_formula_term(left, var, replacement),
            subst_formula_term(right, var, replacement),
        ),
        Formula::Implies(left, right) => Formula::implies(
            subst_formula_term(left, var, replacement),
            subst_formula_term(right, var, replacement),
        ),
        Formula::Forall {
            var: bound,
            var_type,
            body,
        } if bound == var => Formula::forall(bound.clone(), var_type.clone(), *body.clone()),
        Formula::Forall {
            var: bound,
            var_type,
            body,
        } => Formula::forall(
            bound.clone(),
            var_type.clone(),
            subst_formula_term(body, var, replacement),
        ),
        Formula::Exists {
            var: bound,
            var_type,
            body,
        } if bound == var => Formula::exists(bound.clone(), var_type.clone(), *body.clone()),
        Formula::Exists {
            var: bound,
            var_type,
            body,
        } => Formula::exists(
            bound.clone(),
            var_type.clone(),
            subst_formula_term(body, var, replacement),
        ),
    }
}

fn term_has_free_var(term: &Term, name: &str) -> bool {
    match term {
        Term::Var(var) => var == name,
        Term::App(_, args) => args.iter().any(|arg| term_has_free_var(arg, name)),
        Term::Zero | Term::EmptySet(_) => false,
        Term::Succ(term) | Term::Singleton(term) => term_has_free_var(term, name),
        Term::Add(left, right)
        | Term::Union(left, right)
        | Term::Inter(left, right)
        | Term::Diff(left, right) => {
            term_has_free_var(left, name) || term_has_free_var(right, name)
        }
    }
}

fn formula_has_free_term(formula: &Formula, name: &str) -> bool {
    match formula {
        Formula::True | Formula::False | Formula::Atom(_) => false,
        Formula::Eq(left, right) | Formula::In(left, right) | Formula::Subset(left, right) => {
            term_has_free_var(left, name) || term_has_free_var(right, name)
        }
        Formula::PredApp(_, args) => args.iter().any(|arg| term_has_free_var(arg, name)),
        Formula::And(left, right) | Formula::Or(left, right) | Formula::Implies(left, right) => {
            formula_has_free_term(left, name) || formula_has_free_term(right, name)
        }
        Formula::Forall { var, body, .. } | Formula::Exists { var, body, .. } if var == name => {
            false
        }
        Formula::Forall { body, .. } | Formula::Exists { body, .. } => {
            formula_has_free_term(body, name)
        }
    }
}

fn replace_term_once(term: &Term, from: &Term, to: &Term) -> Vec<Term> {
    let mut results = Vec::new();
    if term == from {
        results.push(to.clone());
    }

    if let Term::App(name, args) = term {
        for (idx, arg) in args.iter().enumerate() {
            for replaced_arg in replace_term_once(arg, from, to) {
                let mut new_args = args.clone();
                new_args[idx] = replaced_arg;
                results.push(Term::App(name.clone(), new_args));
            }
        }
    }

    match term {
        Term::Succ(inner) => {
            for replaced in replace_term_once(inner, from, to) {
                results.push(Term::Succ(Box::new(replaced)));
            }
        }
        Term::Add(left, right) => {
            for replaced in replace_term_once(left, from, to) {
                results.push(Term::Add(Box::new(replaced), right.clone()));
            }
            for replaced in replace_term_once(right, from, to) {
                results.push(Term::Add(left.clone(), Box::new(replaced)));
            }
        }
        Term::Singleton(inner) => {
            for replaced in replace_term_once(inner, from, to) {
                results.push(Term::Singleton(Box::new(replaced)));
            }
        }
        Term::Union(left, right) => {
            for replaced in replace_term_once(left, from, to) {
                results.push(Term::Union(Box::new(replaced), right.clone()));
            }
            for replaced in replace_term_once(right, from, to) {
                results.push(Term::Union(left.clone(), Box::new(replaced)));
            }
        }
        Term::Inter(left, right) => {
            for replaced in replace_term_once(left, from, to) {
                results.push(Term::Inter(Box::new(replaced), right.clone()));
            }
            for replaced in replace_term_once(right, from, to) {
                results.push(Term::Inter(left.clone(), Box::new(replaced)));
            }
        }
        Term::Diff(left, right) => {
            for replaced in replace_term_once(left, from, to) {
                results.push(Term::Diff(Box::new(replaced), right.clone()));
            }
            for replaced in replace_term_once(right, from, to) {
                results.push(Term::Diff(left.clone(), Box::new(replaced)));
            }
        }
        Term::Var(_) | Term::App(_, _) | Term::Zero | Term::EmptySet(_) => {}
    }

    results
}

fn replace_formula_once(formula: &Formula, from: &Term, to: &Term) -> Vec<Formula> {
    match formula {
        Formula::True | Formula::False | Formula::Atom(_) => Vec::new(),
        Formula::Eq(left, right) => {
            let mut results = Vec::new();
            for new_left in replace_term_once(left, from, to) {
                results.push(Formula::eq(new_left, right.clone()));
            }
            for new_right in replace_term_once(right, from, to) {
                results.push(Formula::eq(left.clone(), new_right));
            }
            results
        }
        Formula::In(left, right) => {
            replace_binary_term_formula(left, right, from, to, Formula::membership)
        }
        Formula::Subset(left, right) => {
            replace_binary_term_formula(left, right, from, to, Formula::subset)
        }
        Formula::PredApp(name, args) => {
            let mut results = Vec::new();
            for (idx, arg) in args.iter().enumerate() {
                for replaced_arg in replace_term_once(arg, from, to) {
                    let mut new_args = args.clone();
                    new_args[idx] = replaced_arg;
                    results.push(Formula::PredApp(name.clone(), new_args));
                }
            }
            results
        }
        Formula::And(left, right) => replace_binary_formula(left, right, from, to, Formula::and),
        Formula::Or(left, right) => replace_binary_formula(left, right, from, to, Formula::or),
        Formula::Implies(left, right) => {
            replace_binary_formula(left, right, from, to, Formula::implies)
        }
        Formula::Forall {
            var,
            var_type,
            body,
        } => {
            if term_has_free_var(from, var) || term_has_free_var(to, var) {
                Vec::new()
            } else {
                replace_formula_once(body, from, to)
                    .into_iter()
                    .map(|new_body| Formula::forall(var.clone(), var_type.clone(), new_body))
                    .collect()
            }
        }
        Formula::Exists {
            var,
            var_type,
            body,
        } => {
            if term_has_free_var(from, var) || term_has_free_var(to, var) {
                Vec::new()
            } else {
                replace_formula_once(body, from, to)
                    .into_iter()
                    .map(|new_body| Formula::exists(var.clone(), var_type.clone(), new_body))
                    .collect()
            }
        }
    }
}

fn replace_binary_term_formula(
    left: &Term,
    right: &Term,
    from: &Term,
    to: &Term,
    rebuild: fn(Term, Term) -> Formula,
) -> Vec<Formula> {
    let mut results = Vec::new();
    for new_left in replace_term_once(left, from, to) {
        results.push(rebuild(new_left, right.clone()));
    }
    for new_right in replace_term_once(right, from, to) {
        results.push(rebuild(left.clone(), new_right));
    }
    results
}

fn replace_binary_formula(
    left: &Formula,
    right: &Formula,
    from: &Term,
    to: &Term,
    rebuild: fn(Formula, Formula) -> Formula,
) -> Vec<Formula> {
    let mut results = Vec::new();
    for new_left in replace_formula_once(left, from, to) {
        results.push(rebuild(new_left, right.clone()));
    }
    for new_right in replace_formula_once(right, from, to) {
        results.push(rebuild(left.clone(), new_right));
    }
    results
}

fn formula_rewrite_matches(source: &Formula, target: &Formula, from: &Term, to: &Term) -> bool {
    replace_formula_once(source, from, to)
        .into_iter()
        .any(|rewritten| &rewritten == target)
}

fn formula_rewrite_sources(target: &Formula, from: &Term, to: &Term) -> Vec<Formula> {
    replace_formula_once(target, to, from)
}

fn rewrite_source_score(formula: &Formula) -> usize {
    if let Formula::Eq(left, right) = formula {
        if normalize_term_compute(left) == normalize_term_compute(right) {
            return 0;
        }
    }
    1 + formula_size(formula)
}

fn formula_size(formula: &Formula) -> usize {
    match formula {
        Formula::True | Formula::False | Formula::Atom(_) => 1,
        Formula::PredApp(_, args) => 1 + args.iter().map(term_size).sum::<usize>(),
        Formula::Eq(left, right) | Formula::In(left, right) | Formula::Subset(left, right) => {
            1 + term_size(left) + term_size(right)
        }
        Formula::And(left, right) | Formula::Or(left, right) | Formula::Implies(left, right) => {
            1 + formula_size(left) + formula_size(right)
        }
        Formula::Forall { body, .. } | Formula::Exists { body, .. } => 1 + formula_size(body),
    }
}

fn term_size(term: &Term) -> usize {
    match term {
        Term::Var(_) | Term::Zero | Term::EmptySet(_) => 1,
        Term::App(_, args) => 1 + args.iter().map(term_size).sum::<usize>(),
        Term::Succ(term) | Term::Singleton(term) => 1 + term_size(term),
        Term::Add(left, right)
        | Term::Union(left, right)
        | Term::Inter(left, right)
        | Term::Diff(left, right) => 1 + term_size(left) + term_size(right),
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
struct DefDecl {
    name: Name,
    params: Vec<Param>,
    body: Formula,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AxiomDecl {
    name: Name,
    params: Vec<Param>,
    statement: Formula,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Command {
    Mode(LogicMode),
    Sort(Name),
    Const(Name, Type),
    Func(Name, Vec<Type>, Type),
    Pred(Name, Vec<Type>),
    Def(DefDecl),
    Axiom(AxiomDecl),
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
    explicit_args: Vec<ExplicitArg>,
    steps: Vec<ProofStep>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExplicitArg {
    name: Name,
    value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ProofStep {
    Arg(Term),
    Projection(Projection),
}

impl ProofExpr {
    fn is_bare_theorem_ref(&self, env: &Env, ctx: &Context) -> bool {
        self.steps.is_empty()
            && ctx.lookup(&self.base).is_none()
            && env.theorem(&self.base).is_some()
    }

    fn has_explicit_args(&self) -> bool {
        !self.explicit_args.is_empty()
    }

    fn to_proof(&self, env: &Env, ctx: &Context) -> Proof {
        let mut proof = if ctx.lookup(&self.base).is_some() {
            Proof::Hyp(self.base.clone())
        } else if env.theorem(&self.base).is_some() {
            Proof::TheoremRef {
                name: self.base.clone(),
                subst: SchemaSubst::default(),
            }
        } else {
            Proof::Hyp(self.base.clone())
        };

        for step in &self.steps {
            proof = match step {
                ProofStep::Arg(arg) => Proof::ForallElim {
                    proof_forall: Box::new(proof),
                    arg: arg.clone(),
                },
                ProofStep::Projection(Projection::Left) => Proof::AndElimLeft(Box::new(proof)),
                ProofStep::Projection(Projection::Right) => Proof::AndElimRight(Box::new(proof)),
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
    CasesOr {
        expr: ProofExpr,
        left_name: Name,
        left_tactics: Vec<Tactic>,
        right_name: Name,
        right_tactics: Vec<Tactic>,
    },
    CasesExists {
        expr: ProofExpr,
        witness_name: Name,
        hyp_name: Name,
        body_tactics: Vec<Tactic>,
    },
    Exists(Term),
    Refl,
    Rewrite(ProofExpr),
    Unfold(Name),
    Simp,
    Induction {
        var_name: Name,
        zero_tactics: Vec<Tactic>,
        step_var: Name,
        ih_name: Name,
        step_tactics: Vec<Tactic>,
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

    fn parse_type(&mut self) -> Result<Type, ParseError> {
        let name = self.expect_ident()?;
        match name.as_str() {
            "Prop" | "Type" => Err(ParseError::new(format!(
                "`{name}` is not a first-order type"
            ))),
            "Nat" => Ok(Type::Nat),
            "Set" => Ok(Type::Set(Box::new(self.parse_type()?))),
            _ => Ok(Type::Named(name)),
        }
    }

    fn parse_param_kind(&mut self) -> Result<ParamKind, ParseError> {
        if self.eat_ident("Prop") {
            return Ok(ParamKind::Prop);
        }
        if self.eat_ident("Type") {
            return Ok(ParamKind::Type);
        }

        let ty = self.parse_type()?;
        if self.eat_sym("->") {
            let mut args = vec![ty];
            loop {
                if self.eat_ident("Prop") {
                    return Ok(ParamKind::Predicate(args));
                }
                if matches!(self.peek(), TokenKind::Ident(name) if name == "Type") {
                    return Err(ParseError::new(
                        "`Type` cannot appear in predicate arguments",
                    ));
                }
                args.push(self.parse_type()?);
                self.expect_sym("->")?;
            }
        } else {
            Ok(ParamKind::Term(ty))
        }
    }

    fn parse_function_type(&mut self) -> Result<(Vec<Type>, Type), ParseError> {
        let mut types = vec![self.parse_type()?];
        while self.eat_sym("->") {
            types.push(self.parse_type()?);
        }
        if types.len() < 2 {
            return Err(ParseError::new(
                "function type expects at least one argument and a result",
            ));
        }
        let result = types
            .pop()
            .ok_or_else(|| ParseError::new("function type is empty"))?;
        Ok((types, result))
    }

    fn parse_term(&mut self) -> Result<Term, ParseError> {
        if self.eat_sym("0") {
            return Ok(Term::Zero);
        }
        let name = self.expect_ident()?;
        if self.eat_sym("(") {
            if name == "empty" {
                let ty = self.parse_type()?;
                self.expect_sym(")")?;
                return Ok(Term::EmptySet(ty));
            }
            let mut args = Vec::new();
            if !self.eat_sym(")") {
                loop {
                    args.push(self.parse_term()?);
                    if self.eat_sym(")") {
                        break;
                    }
                    self.expect_sym(",")?;
                }
            }
            return match (name.as_str(), args.as_slice()) {
                ("succ", [arg]) => Ok(Term::Succ(Box::new(arg.clone()))),
                ("add", [left, right]) => {
                    Ok(Term::Add(Box::new(left.clone()), Box::new(right.clone())))
                }
                ("singleton", [arg]) => Ok(Term::Singleton(Box::new(arg.clone()))),
                ("union", [left, right]) => {
                    Ok(Term::Union(Box::new(left.clone()), Box::new(right.clone())))
                }
                ("inter", [left, right]) => {
                    Ok(Term::Inter(Box::new(left.clone()), Box::new(right.clone())))
                }
                ("diff", [left, right]) => {
                    Ok(Term::Diff(Box::new(left.clone()), Box::new(right.clone())))
                }
                ("succ" | "singleton", _) => Err(ParseError::new(format!(
                    "`{name}` expects exactly one argument"
                ))),
                ("add" | "union" | "inter" | "diff", _) => Err(ParseError::new(format!(
                    "`{name}` expects exactly two arguments"
                ))),
                _ => Ok(Term::App(name, args)),
            };
        }
        Ok(Term::Var(name))
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
        if self.eat_ident("forall") {
            let var = self.expect_ident()?;
            self.expect_sym(":")?;
            let var_type = self.parse_type()?;
            self.expect_sym(",")?;
            let body = self.parse_formula()?;
            return Ok(Formula::forall(var, var_type, body));
        }
        if self.eat_ident("exists") {
            let var = self.expect_ident()?;
            self.expect_sym(":")?;
            let var_type = self.parse_type()?;
            self.expect_sym(",")?;
            let body = self.parse_formula()?;
            return Ok(Formula::exists(var, var_type, body));
        }
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
        let term = self.parse_term()?;
        if self.eat_sym("=") {
            let right = self.parse_term()?;
            return Ok(Formula::eq(term, right));
        }
        if self.eat_ident("in") {
            let set = self.parse_term()?;
            return Ok(Formula::membership(term, set));
        }
        if self.eat_ident("subset") {
            let right = self.parse_term()?;
            return Ok(Formula::subset(term, right));
        }
        match term {
            Term::Var(name) => Ok(Formula::Atom(name)),
            Term::App(name, args) => Ok(Formula::PredApp(name, args)),
            Term::Zero
            | Term::Succ(_)
            | Term::Add(_, _)
            | Term::EmptySet(_)
            | Term::Singleton(_)
            | Term::Union(_, _)
            | Term::Inter(_, _)
            | Term::Diff(_, _) => Err(ParseError::new(format!("term `{term}` is not a formula"))),
        }
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
        if ch == '0' {
            tokens.push(Token {
                kind: TokenKind::Sym("0".to_string()),
            });
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
                '=' => Some("="),
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

        if let Some(rest) = trimmed.strip_prefix("sort ") {
            let name = rest.trim();
            if name.is_empty() {
                return Err(ParseError::new("sort declaration needs a name"));
            }
            commands.push(Command::Sort(name.to_string()));
            i += 1;
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("const ") {
            let Some((name, ty)) = rest.split_once(':') else {
                return Err(ParseError::new("const declaration expects `name : Type`"));
            };
            commands.push(Command::Const(
                name.trim().to_string(),
                parse_type_str(ty.trim())?,
            ));
            i += 1;
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("func ") {
            let Some((name, ty)) = rest.split_once(':') else {
                return Err(ParseError::new("func declaration expects `name : A -> B`"));
            };
            let (args, result) = parse_function_type_str(ty.trim())?;
            commands.push(Command::Func(name.trim().to_string(), args, result));
            i += 1;
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("pred ") {
            let (name, args) = parse_pred_decl(rest.trim())?;
            commands.push(Command::Pred(name, args));
            i += 1;
            continue;
        }

        if trimmed.starts_with("def ") {
            let mut header = String::from(trimmed);
            while !header.contains(":=") {
                i += 1;
                if i >= lines.len() {
                    return Err(ParseError::new("unterminated definition"));
                }
                header.push(' ');
                header.push_str(strip_comment(lines[i]).trim());
            }

            let Some((header, body)) = header.split_once(":=") else {
                return Err(ParseError::new("expected `:=` in definition"));
            };
            let (name, params) = parse_def_header(header)?;
            commands.push(Command::Def(DefDecl {
                name,
                params,
                body: parse_formula_str(body.trim())?,
            }));
            i += 1;
            continue;
        }

        if trimmed.starts_with("axiom ") {
            let mut header = String::from(trimmed);
            i += 1;
            while i < lines.len() {
                let next = strip_comment(lines[i]).trim();
                if is_command_start(next) {
                    break;
                }
                header.push(' ');
                header.push_str(next);
                i += 1;
            }
            let (name, params, statement) = parse_axiom_header(&header)?;
            commands.push(Command::Axiom(AxiomDecl {
                name,
                params,
                statement,
            }));
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
    let params = parse_decl_params(&mut tokens)?;

    tokens.expect_sym(":")?;
    let statement = tokens.parse_formula()?;
    tokens.expect_eof()?;
    Ok((name, params, statement))
}

fn parse_axiom_header(header: &str) -> Result<(Name, Vec<Param>, Formula), ParseError> {
    let mut tokens = Tokens::new(header)?;
    tokens.expect_keyword("axiom")?;
    let name = tokens.expect_ident()?;
    let params = parse_decl_params(&mut tokens)?;
    tokens.expect_sym(":")?;
    let statement = tokens.parse_formula()?;
    tokens.expect_eof()?;
    Ok((name, params, statement))
}

fn parse_def_header(header: &str) -> Result<(Name, Vec<Param>), ParseError> {
    let mut tokens = Tokens::new(header)?;
    tokens.expect_keyword("def")?;
    let name = tokens.expect_ident()?;
    let params = parse_decl_params(&mut tokens)?;
    tokens.expect_sym(":")?;
    tokens.expect_keyword("Prop")?;
    tokens.expect_eof()?;
    Ok((name, params))
}

fn parse_decl_params(tokens: &mut Tokens) -> Result<Vec<Param>, ParseError> {
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
        let kind = tokens.parse_param_kind()?;
        tokens.expect_sym(")")?;
        for name in names {
            params.push(Param {
                name,
                kind: kind.clone(),
            });
        }
    }

    Ok(params)
}

fn parse_type_str(input: &str) -> Result<Type, ParseError> {
    let mut tokens = Tokens::new(input)?;
    let ty = tokens.parse_type()?;
    tokens.expect_eof()?;
    Ok(ty)
}

fn parse_function_type_str(input: &str) -> Result<(Vec<Type>, Type), ParseError> {
    let mut tokens = Tokens::new(input)?;
    let parsed = tokens.parse_function_type()?;
    tokens.expect_eof()?;
    Ok(parsed)
}

fn parse_formula_str(input: &str) -> Result<Formula, ParseError> {
    let mut tokens = Tokens::new(input)?;
    let formula = tokens.parse_formula()?;
    tokens.expect_eof()?;
    Ok(formula)
}

fn parse_term_str(input: &str) -> Result<Term, ParseError> {
    let mut tokens = Tokens::new(input)?;
    let term = tokens.parse_term()?;
    tokens.expect_eof()?;
    Ok(term)
}

fn parse_pred_decl(input: &str) -> Result<(Name, Vec<Type>), ParseError> {
    let mut tokens = Tokens::new(input)?;
    let name = tokens.expect_ident()?;
    tokens.expect_sym("(")?;
    let mut args = Vec::new();
    if !tokens.eat_sym(")") {
        loop {
            args.push(tokens.parse_type()?);
            if tokens.eat_sym(")") {
                break;
            }
            tokens.expect_sym(",")?;
        }
    }
    tokens.expect_eof()?;
    Ok((name, args))
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
                return Err(ParseError::new("expected case arm"));
            }

            if lines[i].trim().starts_with("| intro ") {
                let (witness_name, hyp_name) = parse_exists_case_arm(lines[i].trim())?;
                i += 1;
                let body_tactics = parse_tactic_lines(&lines[i..])?;
                i = lines.len();

                tactics.push(Tactic::CasesExists {
                    expr: parse_proof_expr(expr.trim())?,
                    witness_name,
                    hyp_name,
                    body_tactics,
                });
                continue;
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

            tactics.push(Tactic::CasesOr {
                expr: parse_proof_expr(expr.trim())?,
                left_name,
                left_tactics,
                right_name,
                right_tactics,
            });
            continue;
        }

        if let Some(var_name) = trimmed
            .strip_prefix("induction ")
            .and_then(|rest| rest.strip_suffix(" with"))
        {
            i += 1;
            if i >= lines.len() {
                return Err(ParseError::new("expected zero case arm"));
            }
            parse_zero_case_arm(lines[i].trim())?;
            i += 1;
            let zero_start = i;
            while i < lines.len() && !lines[i].trim().starts_with("| succ ") {
                i += 1;
            }
            if i >= lines.len() {
                return Err(ParseError::new("expected successor case arm"));
            }
            let zero_tactics = parse_tactic_lines(&lines[zero_start..i])?;
            let (step_var, ih_name) = parse_succ_case_arm(lines[i].trim())?;
            i += 1;
            let step_tactics = parse_tactic_lines(&lines[i..])?;
            i = lines.len();

            tactics.push(Tactic::Induction {
                var_name: expect_single_name(var_name, "induction")?,
                zero_tactics,
                step_var,
                ih_name,
                step_tactics,
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

fn parse_exists_case_arm(line: &str) -> Result<(Name, Name), ParseError> {
    let Some(rest) = line.strip_prefix("| intro ") else {
        return Err(ParseError::new("expected existential intro case arm"));
    };
    let Some(names) = rest.strip_suffix("=>") else {
        return Err(ParseError::new("case arm must end with `=>`"));
    };
    let names: Vec<&str> = names.split_whitespace().collect();
    if names.len() != 2 {
        return Err(ParseError::new(
            "existential case arm expects witness and hypothesis names",
        ));
    }
    Ok((names[0].to_string(), names[1].to_string()))
}

fn parse_zero_case_arm(line: &str) -> Result<(), ParseError> {
    if line == "| zero =>" {
        Ok(())
    } else {
        Err(ParseError::new("expected `| zero =>` case arm"))
    }
}

fn parse_succ_case_arm(line: &str) -> Result<(Name, Name), ParseError> {
    let Some(rest) = line.strip_prefix("| succ ") else {
        return Err(ParseError::new("expected successor case arm"));
    };
    let Some(names) = rest.strip_suffix("=>") else {
        return Err(ParseError::new("case arm must end with `=>`"));
    };
    let names: Vec<&str> = names.split_whitespace().collect();
    if names.len() != 2 {
        return Err(ParseError::new(
            "successor case arm expects variable and induction hypothesis names",
        ));
    }
    Ok((names[0].to_string(), names[1].to_string()))
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
    if let Some(rest) = line.strip_prefix("exists ") {
        return Ok(Tactic::Exists(parse_term_str(rest.trim())?));
    }
    if line == "refl" {
        return Ok(Tactic::Refl);
    }
    if let Some(rest) = line.strip_prefix("rewrite ") {
        return Ok(Tactic::Rewrite(parse_proof_expr(rest.trim())?));
    }
    if let Some(rest) = line.strip_prefix("unfold ") {
        return Ok(Tactic::Unfold(expect_single_name(rest, "unfold")?));
    }
    if line == "simp" {
        return Ok(Tactic::Simp);
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
    let input = input.trim();
    if input.is_empty() {
        return Err(ParseError::new("expected proof expression"));
    }

    if let Some(rest) = input.strip_prefix('(') {
        let close = matching_close_paren(rest)?;
        let inner = &rest[..close];
        let suffix = rest[close + 1..].trim();
        let mut expr = parse_proof_expr(inner)?;
        append_projection_suffix(&mut expr, suffix)?;
        return Ok(expr);
    }

    let mut parts = input.split('.');
    let head = parts
        .next()
        .ok_or_else(|| ParseError::new("expected proof expression"))?
        .trim();
    let (base, explicit_args, remaining) = parse_proof_expr_head(head)?;
    let mut steps = Vec::new();
    for word in remaining.split_whitespace() {
        steps.push(ProofStep::Arg(parse_term_str(word)?));
    }

    for part in parts {
        match part.trim() {
            "left" => steps.push(ProofStep::Projection(Projection::Left)),
            "right" => steps.push(ProofStep::Projection(Projection::Right)),
            other => {
                return Err(ParseError::new(format!(
                    "unknown proof projection `.{other}`"
                )))
            }
        }
    }

    Ok(ProofExpr {
        base,
        explicit_args,
        steps,
    })
}

fn parse_proof_expr_head(input: &str) -> Result<(Name, Vec<ExplicitArg>, String), ParseError> {
    let input = input.trim();
    let Some((base, rest)) = split_first_word(input) else {
        return Err(ParseError::new("expected proof expression"));
    };
    let mut rest = rest.trim();
    let mut explicit_args = Vec::new();

    if let Some(after_open) = rest.strip_prefix('{') {
        let close = matching_close_brace(after_open)?;
        let body = &after_open[..close];
        explicit_args = parse_explicit_args(body)?;
        rest = after_open[close + 1..].trim();
    }

    Ok((base.to_string(), explicit_args, rest.to_string()))
}

fn split_first_word(input: &str) -> Option<(&str, &str)> {
    let input = input.trim_start();
    if input.is_empty() {
        return None;
    }
    let end = input.find(char::is_whitespace).unwrap_or(input.len());
    Some((&input[..end], &input[end..]))
}

fn parse_explicit_args(input: &str) -> Result<Vec<ExplicitArg>, ParseError> {
    let mut args = Vec::new();
    for item in split_top_level(input, ';') {
        let item = item.trim();
        if item.is_empty() {
            continue;
        }
        let Some((name, value)) = item.split_once(":=") else {
            return Err(ParseError::new(
                "explicit theorem arguments use `name := value`",
            ));
        };
        let name = name.trim();
        let value = value.trim();
        if name.is_empty() || value.is_empty() {
            return Err(ParseError::new("explicit theorem argument is incomplete"));
        }
        args.push(ExplicitArg {
            name: name.to_string(),
            value: value.to_string(),
        });
    }
    Ok(args)
}

fn split_top_level(input: &str, sep: char) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (idx, ch) in input.char_indices() {
        match ch {
            '(' | '{' => depth += 1,
            ')' | '}' => depth = depth.saturating_sub(1),
            _ if ch == sep && depth == 0 => {
                parts.push(&input[start..idx]);
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }
    parts.push(&input[start..]);
    parts
}

fn matching_close_paren(input_after_open: &str) -> Result<usize, ParseError> {
    let mut depth = 1usize;
    for (idx, ch) in input_after_open.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(idx);
                }
            }
            _ => {}
        }
    }
    Err(ParseError::new("unclosed parenthesized proof expression"))
}

fn matching_close_brace(input_after_open: &str) -> Result<usize, ParseError> {
    let mut depth = 1usize;
    for (idx, ch) in input_after_open.char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(idx);
                }
            }
            _ => {}
        }
    }
    Err(ParseError::new("unclosed theorem-instantiation block"))
}

fn append_projection_suffix(expr: &mut ProofExpr, suffix: &str) -> Result<(), ParseError> {
    if suffix.is_empty() {
        return Ok(());
    }
    let Some(rest) = suffix.strip_prefix('.') else {
        return Err(ParseError::new("unexpected text after proof expression"));
    };
    for part in rest.split('.') {
        match part.trim() {
            "left" => expr.steps.push(ProofStep::Projection(Projection::Left)),
            "right" => expr.steps.push(ProofStep::Projection(Projection::Right)),
            other => {
                return Err(ParseError::new(format!(
                    "unknown proof projection `.{other}`"
                )))
            }
        }
    }
    Ok(())
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
    EqSubst {
        eq_proof: Box<PartialProof>,
        proof_body: Box<PartialProof>,
        target: Formula,
    },
    Convert {
        proof_body: Box<PartialProof>,
        target: Formula,
    },
    ForallIntro {
        var: Name,
        var_type: Type,
        body: Box<PartialProof>,
    },
    ForallElim {
        proof_forall: Box<PartialProof>,
        arg: Term,
    },
    ExistsIntro {
        witness: Term,
        proof_body: Box<PartialProof>,
        exists_formula: Formula,
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
            PartialProof::EqSubst {
                eq_proof,
                proof_body,
                ..
            } => eq_proof.replace_hole(id, replacement) || proof_body.replace_hole(id, replacement),
            PartialProof::Convert { proof_body, .. } => proof_body.replace_hole(id, replacement),
            PartialProof::ForallIntro { body, .. } => body.replace_hole(id, replacement),
            PartialProof::ForallElim { proof_forall, .. } => {
                proof_forall.replace_hole(id, replacement)
            }
            PartialProof::ExistsIntro { proof_body, .. } => {
                proof_body.replace_hole(id, replacement)
            }
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
            PartialProof::EqSubst {
                eq_proof,
                proof_body,
                target,
            } => Ok(Proof::EqSubst {
                eq_proof: Box::new(eq_proof.complete()?),
                proof_body: Box::new(proof_body.complete()?),
                target,
            }),
            PartialProof::Convert { proof_body, target } => Ok(Proof::Convert {
                proof_body: Box::new(proof_body.complete()?),
                target,
            }),
            PartialProof::ForallIntro {
                var,
                var_type,
                body,
            } => Ok(Proof::ForallIntro {
                var,
                var_type,
                body: Box::new(body.complete()?),
            }),
            PartialProof::ForallElim { proof_forall, arg } => Ok(Proof::ForallElim {
                proof_forall: Box::new(proof_forall.complete()?),
                arg,
            }),
            PartialProof::ExistsIntro {
                witness,
                proof_body,
                exists_formula,
            } => Ok(Proof::ExistsIntro {
                witness,
                proof_body: Box::new(proof_body.complete()?),
                exists_formula,
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
        Tactic::Intro(name) => match goal.target {
            Formula::Implies(premise, conclusion) => {
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
            Formula::Forall {
                var,
                var_type,
                body,
            } => {
                let mut context = goal.context;
                context.add_term(name.clone(), var_type.clone());
                let body_id = fresh_goal(next_goal_id);
                let target = subst_formula_term(&body, &var, &Term::Var(name.clone()));
                Ok(StepResult {
                    replacement: PartialProof::ForallIntro {
                        var: name.clone(),
                        var_type,
                        body: Box::new(PartialProof::Hole(body_id)),
                    },
                    new_goals: vec![Goal {
                        id: body_id,
                        context,
                        target,
                    }],
                })
            }
            _ => Err(TacticError::new(
                "intro expects an implication or universal goal",
            )),
        },
        Tactic::Exact(expr) => {
            let proof = proof_expr_for_expected(env, &goal.context, expr, &goal.target)?;
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
            let mut matched = None;
            for binding in goal.context.proofs().iter().rev() {
                if formulas_def_eq(env, &goal.context, &binding.formula, &goal.target)
                    .map_err(|err| TacticError::new(err.message))?
                {
                    matched = Some(binding);
                    break;
                }
            }
            let Some(binding) = matched else {
                return Err(TacticError::new("no matching assumption found"));
            };
            Ok(StepResult {
                replacement: PartialProof::Done(Proof::Hyp(binding.name.clone())),
                new_goals: Vec::new(),
            })
        }
        Tactic::Apply(expr) => {
            let (proof, forall_args, premises) =
                proof_expr_for_apply(env, &goal.context, expr, &goal.target, allowed_mode)?;
            let mut replacement = PartialProof::Done(proof);
            let mut new_goals = Vec::new();

            for arg in forall_args {
                replacement = PartialProof::ForallElim {
                    proof_forall: Box::new(replacement),
                    arg,
                };
            }

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
        Tactic::CasesOr {
            expr,
            left_name,
            left_tactics,
            right_name,
            right_tactics,
        } => {
            let proof_or = expr.to_proof(env, &goal.context);
            let checked = infer_proof(env, &goal.context, &proof_or, allowed_mode)
                .map_err(|err| TacticError::new(format!("cannot case split: {}", err.message)))?;
            let formula = normalize_formula_defs(env, &goal.context, &checked.formula)
                .map_err(|err| TacticError::new(err.message))?;
            let Formula::Or(left_formula, right_formula) = formula else {
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
        Tactic::CasesExists {
            expr,
            witness_name,
            hyp_name,
            body_tactics,
        } => {
            let proof_exists = expr.to_proof(env, &goal.context);
            let checked = infer_proof(env, &goal.context, &proof_exists, allowed_mode)
                .map_err(|err| TacticError::new(format!("cannot case split: {}", err.message)))?;
            let formula = normalize_formula_defs(env, &goal.context, &checked.formula)
                .map_err(|err| TacticError::new(err.message))?;
            let Formula::Exists {
                var,
                var_type,
                body,
            } = formula
            else {
                return Err(TacticError::new("cases expects an existential proof"));
            };

            let mut body_ctx = goal.context.clone();
            body_ctx.add_term(witness_name.clone(), var_type);
            body_ctx.add_proof(
                hyp_name.clone(),
                subst_formula_term(&body, &var, &Term::Var(witness_name.clone())),
            );
            let body_proof = prove(
                env,
                body_ctx,
                goal.target.clone(),
                body_tactics,
                allowed_mode,
            )?;

            Ok(StepResult {
                replacement: PartialProof::Done(Proof::ExistsElim {
                    proof_exists: Box::new(proof_exists),
                    witness_name: witness_name.clone(),
                    hyp_name: hyp_name.clone(),
                    body: Box::new(body_proof),
                    target: goal.target,
                }),
                new_goals: Vec::new(),
            })
        }
        Tactic::Exists(witness) => {
            let Formula::Exists {
                var,
                var_type: _,
                body,
            } = &goal.target
            else {
                return Err(TacticError::new("exists expects an existential goal"));
            };
            let id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::ExistsIntro {
                    witness: witness.clone(),
                    proof_body: Box::new(PartialProof::Hole(id)),
                    exists_formula: goal.target.clone(),
                },
                new_goals: vec![Goal {
                    id,
                    context: goal.context,
                    target: subst_formula_term(body, var, witness),
                }],
            })
        }
        Tactic::Refl => {
            let Formula::Eq(left, right) = &goal.target else {
                return Err(TacticError::new("refl expects an equality goal"));
            };
            if left != right {
                return Err(TacticError::new(format!(
                    "refl cannot prove `{left} = {right}` because the sides are not identical"
                )));
            }
            Ok(StepResult {
                replacement: PartialProof::Done(Proof::EqRefl(left.clone())),
                new_goals: Vec::new(),
            })
        }
        Tactic::Rewrite(expr) => {
            let eq_proof = proof_expr_for_inferred(env, &goal.context, expr)?;
            let checked = infer_proof(env, &goal.context, &eq_proof, allowed_mode)
                .map_err(|err| TacticError::new(format!("cannot rewrite: {}", err.message)))?;
            let formula = normalize_formula_defs(env, &goal.context, &checked.formula)
                .map_err(|err| TacticError::new(err.message))?;
            let Formula::Eq(left, right) = formula else {
                return Err(TacticError::new("rewrite expects an equality proof"));
            };
            let Some(source_target) = formula_rewrite_sources(&goal.target, &left, &right)
                .into_iter()
                .min_by_key(rewrite_source_score)
            else {
                return Err(TacticError::new(format!(
                    "rewrite could not find `{right}` in goal `{}`",
                    goal.target
                )));
            };

            let body_id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::EqSubst {
                    eq_proof: Box::new(PartialProof::Done(eq_proof)),
                    proof_body: Box::new(PartialProof::Hole(body_id)),
                    target: goal.target.clone(),
                },
                new_goals: vec![Goal {
                    id: body_id,
                    context: goal.context,
                    target: source_target,
                }],
            })
        }
        Tactic::Unfold(name) => {
            if env.formula_def(name).is_none() {
                return Err(TacticError::new(format!("unknown definition `{name}`")));
            }
            let (target, changed) =
                unfold_named_formula_def(env, &goal.context, &goal.target, name).map_err(
                    |err| TacticError::new(format!("cannot unfold `{name}`: {}", err.message)),
                )?;
            if !changed {
                return Err(TacticError::new(format!(
                    "no occurrence of definition `{name}` in goal `{}`",
                    goal.target
                )));
            }
            let id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::Convert {
                    proof_body: Box::new(PartialProof::Hole(id)),
                    target: goal.target,
                },
                new_goals: vec![Goal {
                    id,
                    context: goal.context,
                    target,
                }],
            })
        }
        Tactic::Simp => {
            let (target, changed) = unfold_formula_defs(env, &goal.context, &goal.target, None)
                .map_err(|err| TacticError::new(format!("cannot simplify: {}", err.message)))?;
            if !changed {
                return Err(TacticError::new(format!(
                    "simp made no progress on goal `{}`",
                    goal.target
                )));
            }
            let id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::Convert {
                    proof_body: Box::new(PartialProof::Hole(id)),
                    target: goal.target,
                },
                new_goals: vec![Goal {
                    id,
                    context: goal.context,
                    target,
                }],
            })
        }
        Tactic::Induction {
            var_name,
            zero_tactics,
            step_var,
            ih_name,
            step_tactics,
        } => {
            let Some(var_type) = goal.context.lookup_term(var_name) else {
                return Err(TacticError::new(format!(
                    "induction variable `{var_name}` is not in scope"
                )));
            };
            if var_type != &Type::Nat {
                return Err(TacticError::new(format!(
                    "induction variable `{var_name}` has type `{var_type}`, but expected `Nat`"
                )));
            }
            if let Some(binding) = goal
                .context
                .proofs()
                .iter()
                .find(|binding| formula_has_free_term(&binding.formula, var_name))
            {
                return Err(TacticError::new(format!(
                    "cannot induct on `{var_name}` while hypothesis `{}` depends on it",
                    binding.name
                )));
            }

            let base_target = subst_formula_term(&goal.target, var_name, &Term::Zero);
            let base_case = prove(
                env,
                goal.context.clone(),
                base_target,
                zero_tactics,
                allowed_mode,
            )?;

            let mut step_ctx = goal.context.clone();
            step_ctx.add_term(step_var.clone(), Type::Nat);
            let step_var_term = Term::Var(step_var.clone());
            let ih_formula = subst_formula_term(&goal.target, var_name, &step_var_term);
            step_ctx.add_proof(ih_name.clone(), ih_formula);
            let step_target =
                subst_formula_term(&goal.target, var_name, &Term::Succ(Box::new(step_var_term)));
            let step_case = prove(env, step_ctx, step_target, step_tactics, allowed_mode)?;

            Ok(StepResult {
                replacement: PartialProof::Done(Proof::NatInd {
                    var_name: var_name.clone(),
                    target: goal.target,
                    base_case: Box::new(base_case),
                    step_var: step_var.clone(),
                    ih_name: ih_name.clone(),
                    step_case: Box::new(step_case),
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
        Tactic::Contradiction => contradiction_step(env, goal),
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

fn proof_expr_for_inferred(
    env: &Env,
    ctx: &Context,
    expr: &ProofExpr,
) -> Result<Proof, TacticError> {
    if expr.is_bare_theorem_ref(env, ctx) {
        let theorem = env
            .theorem(&expr.base)
            .ok_or_else(|| TacticError::new(format!("unknown theorem `{}`", expr.base)))?;
        let subst = explicit_schema_subst(env, ctx, theorem, &expr.explicit_args)?;
        ensure_schema_subst_complete(&theorem.params, &subst)?;
        return Ok(Proof::TheoremRef {
            name: expr.base.clone(),
            subst,
        });
    }

    if expr.has_explicit_args() {
        return Err(TacticError::new(
            "explicit theorem arguments can only be used with theorem references",
        ));
    }

    Ok(expr.to_proof(env, ctx))
}

fn explicit_schema_subst(
    env: &Env,
    ctx: &Context,
    theorem: &Theorem,
    explicit_args: &[ExplicitArg],
) -> Result<SchemaSubst, TacticError> {
    let mut subst = SchemaSubst::default();
    let mut seen = Vec::new();

    for arg in explicit_args {
        if seen.iter().any(|name: &Name| name == &arg.name) {
            return Err(TacticError::new(format!(
                "schema argument `{}` was provided more than once",
                arg.name
            )));
        }
        seen.push(arg.name.clone());

        let Some(param) = theorem.params.iter().find(|param| param.name == arg.name) else {
            return Err(TacticError::new(format!(
                "theorem `{}` has no schema argument `{}`",
                theorem.name, arg.name
            )));
        };

        match &param.kind {
            ParamKind::Type => {
                let ty = parse_type_str(&arg.value).map_err(|err| TacticError::new(err.message))?;
                validate_type(env, ctx, &ty).map_err(|err| TacticError::new(err.message))?;
                subst.type_args.insert(arg.name.clone(), ty);
            }
            ParamKind::Prop => {
                let formula =
                    parse_formula_str(&arg.value).map_err(|err| TacticError::new(err.message))?;
                validate_formula(env, ctx, &formula)
                    .map_err(|err| TacticError::new(err.message))?;
                subst.formula_args.insert(arg.name.clone(), formula);
            }
            ParamKind::Predicate(_) => {
                let name = parse_predicate_arg_name(&arg.value)?;
                if predicate_signature(env, ctx, &name).is_none() {
                    return Err(TacticError::new(format!("unknown predicate `{name}`")));
                }
                subst.predicate_args.insert(arg.name.clone(), name);
            }
            ParamKind::Term(_) => {
                let term =
                    parse_term_str(&arg.value).map_err(|err| TacticError::new(err.message))?;
                validate_term(env, ctx, &term).map_err(|err| TacticError::new(err.message))?;
                subst.term_args.insert(arg.name.clone(), term);
            }
        }
    }

    Ok(subst)
}

fn parse_predicate_arg_name(input: &str) -> Result<Name, TacticError> {
    let input = input.trim();
    if input.is_empty() {
        return Err(TacticError::new("predicate argument cannot be empty"));
    }
    if input.chars().enumerate().all(|(idx, ch)| {
        if idx == 0 {
            ch.is_ascii_alphabetic() || ch == '_'
        } else {
            ch.is_ascii_alphanumeric() || ch == '_'
        }
    }) {
        Ok(input.to_string())
    } else {
        Err(TacticError::new(format!(
            "predicate argument `{input}` must be a predicate name"
        )))
    }
}

fn proof_expr_for_expected(
    env: &Env,
    ctx: &Context,
    expr: &ProofExpr,
    expected: &Formula,
) -> Result<Proof, TacticError> {
    if expr.is_bare_theorem_ref(env, ctx) {
        let theorem = env
            .theorem(&expr.base)
            .ok_or_else(|| TacticError::new(format!("unknown theorem `{}`", expr.base)))?;
        let explicit = explicit_schema_subst(env, ctx, theorem, &expr.explicit_args)?;
        let subst = infer_schema_subst_for_formula(
            env,
            ctx,
            &theorem.params,
            &theorem.statement,
            expected,
            explicit,
        )?;
        return Ok(Proof::TheoremRef {
            name: expr.base.clone(),
            subst,
        });
    }

    if expr.has_explicit_args() {
        return Err(TacticError::new(
            "explicit theorem arguments can only be used with theorem references",
        ));
    }

    Ok(expr.to_proof(env, ctx))
}

fn proof_expr_for_apply(
    env: &Env,
    ctx: &Context,
    expr: &ProofExpr,
    target: &Formula,
    allowed_mode: LogicMode,
) -> Result<(Proof, Vec<Term>, Vec<Formula>), TacticError> {
    if expr.is_bare_theorem_ref(env, ctx) {
        let theorem = env
            .theorem(&expr.base)
            .ok_or_else(|| TacticError::new(format!("unknown theorem `{}`", expr.base)))?;
        let explicit = explicit_schema_subst(env, ctx, theorem, &expr.explicit_args)?;
        let plan = apply_plan_for_goal(
            env,
            ctx,
            &theorem.statement,
            target,
            &theorem.params,
            explicit,
        )?;
        return Ok((
            Proof::TheoremRef {
                name: expr.base.clone(),
                subst: plan.schema_subst,
            },
            plan.forall_args,
            plan.premises,
        ));
    }

    if expr.has_explicit_args() {
        return Err(TacticError::new(
            "explicit theorem arguments can only be used with theorem references",
        ));
    }

    let proof = expr.to_proof(env, ctx);
    let checked = infer_proof(env, ctx, &proof, allowed_mode)
        .map_err(|err| TacticError::new(format!("cannot apply expression: {}", err.message)))?;
    let plan = apply_plan_for_goal(
        env,
        ctx,
        &checked.formula,
        target,
        &[],
        SchemaSubst::default(),
    )?;
    Ok((proof, plan.forall_args, plan.premises))
}

fn fresh_goal(next_goal_id: &mut usize) -> usize {
    let id = *next_goal_id;
    *next_goal_id += 1;
    id
}

struct ApplyPlan {
    schema_subst: SchemaSubst,
    forall_args: Vec<Term>,
    premises: Vec<Formula>,
}

fn apply_plan_for_goal(
    env: &Env,
    ctx: &Context,
    formula: &Formula,
    target: &Formula,
    schema_params: &[Param],
    initial_schema_subst: SchemaSubst,
) -> Result<ApplyPlan, TacticError> {
    let normalized_formula =
        normalize_formula_defs(env, ctx, formula).map_err(|err| TacticError::new(err.message))?;
    let normalized_target =
        normalize_formula_defs(env, ctx, target).map_err(|err| TacticError::new(err.message))?;

    let mut forall_vars = Vec::new();
    let mut cursor = &normalized_formula;
    while let Formula::Forall {
        var,
        var_type,
        body,
    } = cursor
    {
        forall_vars.push((var.clone(), var_type.clone()));
        cursor = body;
    }

    let mut premises = Vec::new();
    while let Formula::Implies(premise, conclusion) = cursor {
        premises.push(*premise.clone());
        cursor = conclusion;
    }

    let quantified: Vec<Name> = forall_vars.iter().map(|(name, _)| name.clone()).collect();
    let mut term_subst = HashMap::new();
    let mut schema_subst = initial_schema_subst;
    {
        let mut unify = UnifyState {
            env,
            ctx,
            term_metas: &quantified,
            schema_params,
            term_subst: &mut term_subst,
            schema_subst: &mut schema_subst,
        };
        unify_formula(cursor, &normalized_target, &mut unify).map_err(|_| {
            TacticError::new(format!(
                "cannot apply expression with conclusion `{cursor}` to goal `{target}`"
            ))
        })?;
    }
    ensure_schema_subst_complete(schema_params, &schema_subst)?;

    let mut forall_args = Vec::new();
    for (var, _) in forall_vars {
        let Some(arg) = term_subst.get(&var) else {
            return Err(TacticError::new(format!(
                "cannot infer instantiation for `{var}`"
            )));
        };
        forall_args.push(arg.clone());
    }

    let premises = premises
        .into_iter()
        .map(|premise| {
            subst_formula_terms(&subst_formula_schema(&premise, &schema_subst), &term_subst)
        })
        .collect();

    Ok(ApplyPlan {
        schema_subst,
        forall_args,
        premises,
    })
}

fn infer_schema_subst_for_formula(
    env: &Env,
    ctx: &Context,
    params: &[Param],
    pattern: &Formula,
    target: &Formula,
    initial_schema_subst: SchemaSubst,
) -> Result<SchemaSubst, TacticError> {
    let mut schema_subst = initial_schema_subst;
    let mut term_subst = HashMap::new();
    {
        let mut unify = UnifyState {
            env,
            ctx,
            term_metas: &[],
            schema_params: params,
            term_subst: &mut term_subst,
            schema_subst: &mut schema_subst,
        };
        unify_formula(pattern, target, &mut unify).map_err(|_| {
            TacticError::new(format!("cannot instantiate theorem for goal `{target}`"))
        })?;
    }
    ensure_schema_subst_complete(params, &schema_subst)?;
    Ok(schema_subst)
}

fn ensure_schema_subst_complete(params: &[Param], subst: &SchemaSubst) -> Result<(), TacticError> {
    for param in params {
        let complete = match &param.kind {
            ParamKind::Type => subst.type_args.contains_key(&param.name),
            ParamKind::Prop => subst.formula_args.contains_key(&param.name),
            ParamKind::Predicate(_) => subst.predicate_args.contains_key(&param.name),
            ParamKind::Term(_) => subst.term_args.contains_key(&param.name),
        };
        if !complete {
            return Err(TacticError::new(format!(
                "cannot infer schema argument `{}`",
                param.name
            )));
        }
    }
    Ok(())
}

fn subst_formula_terms(formula: &Formula, subst: &HashMap<Name, Term>) -> Formula {
    match formula {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Atom(name) => Formula::Atom(name.clone()),
        Formula::Eq(left, right) => Formula::eq(
            subst_term_terms(left, subst),
            subst_term_terms(right, subst),
        ),
        Formula::In(elem, set) => {
            Formula::membership(subst_term_terms(elem, subst), subst_term_terms(set, subst))
        }
        Formula::Subset(left, right) => Formula::subset(
            subst_term_terms(left, subst),
            subst_term_terms(right, subst),
        ),
        Formula::PredApp(name, args) => Formula::PredApp(
            name.clone(),
            args.iter()
                .map(|arg| subst_term_terms(arg, subst))
                .collect(),
        ),
        Formula::And(left, right) => Formula::and(
            subst_formula_terms(left, subst),
            subst_formula_terms(right, subst),
        ),
        Formula::Or(left, right) => Formula::or(
            subst_formula_terms(left, subst),
            subst_formula_terms(right, subst),
        ),
        Formula::Implies(left, right) => Formula::implies(
            subst_formula_terms(left, subst),
            subst_formula_terms(right, subst),
        ),
        Formula::Forall {
            var,
            var_type,
            body,
        } => {
            let mut scoped = subst.clone();
            scoped.remove(var);
            Formula::forall(
                var.clone(),
                var_type.clone(),
                subst_formula_terms(body, &scoped),
            )
        }
        Formula::Exists {
            var,
            var_type,
            body,
        } => {
            let mut scoped = subst.clone();
            scoped.remove(var);
            Formula::exists(
                var.clone(),
                var_type.clone(),
                subst_formula_terms(body, &scoped),
            )
        }
    }
}

fn subst_term_terms(term: &Term, subst: &HashMap<Name, Term>) -> Term {
    match term {
        Term::Var(name) => subst
            .get(name)
            .cloned()
            .unwrap_or_else(|| Term::Var(name.clone())),
        Term::App(name, args) => Term::App(
            name.clone(),
            args.iter()
                .map(|arg| subst_term_terms(arg, subst))
                .collect(),
        ),
        Term::Zero => Term::Zero,
        Term::Succ(term) => Term::Succ(Box::new(subst_term_terms(term, subst))),
        Term::Add(left, right) => Term::Add(
            Box::new(subst_term_terms(left, subst)),
            Box::new(subst_term_terms(right, subst)),
        ),
        Term::EmptySet(ty) => Term::EmptySet(ty.clone()),
        Term::Singleton(term) => Term::Singleton(Box::new(subst_term_terms(term, subst))),
        Term::Union(left, right) => Term::Union(
            Box::new(subst_term_terms(left, subst)),
            Box::new(subst_term_terms(right, subst)),
        ),
        Term::Inter(left, right) => Term::Inter(
            Box::new(subst_term_terms(left, subst)),
            Box::new(subst_term_terms(right, subst)),
        ),
        Term::Diff(left, right) => Term::Diff(
            Box::new(subst_term_terms(left, subst)),
            Box::new(subst_term_terms(right, subst)),
        ),
    }
}

struct UnifyState<'a> {
    env: &'a Env,
    ctx: &'a Context,
    term_metas: &'a [Name],
    schema_params: &'a [Param],
    term_subst: &'a mut HashMap<Name, Term>,
    schema_subst: &'a mut SchemaSubst,
}

fn unify_formula(
    pattern: &Formula,
    target: &Formula,
    unify: &mut UnifyState<'_>,
) -> Result<(), ()> {
    match (pattern, target) {
        (Formula::True, Formula::True) | (Formula::False, Formula::False) => Ok(()),
        (Formula::Atom(name), _) if schema_prop_param(unify.schema_params, name) => {
            unify_schema_prop(name, target, unify.schema_subst)
        }
        (Formula::Atom(p_name), Formula::Atom(t_name)) if p_name == t_name => Ok(()),
        (Formula::Eq(p_left, p_right), Formula::Eq(t_left, t_right)) => {
            unify_term(p_left, t_left, unify)?;
            unify_term(p_right, t_right, unify)
        }
        (Formula::In(p_left, p_right), Formula::In(t_left, t_right))
        | (Formula::Subset(p_left, p_right), Formula::Subset(t_left, t_right)) => {
            unify_term(p_left, t_left, unify)?;
            unify_term(p_right, t_right, unify)
        }
        (Formula::PredApp(p_name, p_args), Formula::PredApp(t_name, t_args))
            if schema_predicate_param(unify.schema_params, p_name).is_some() =>
        {
            let param_args = schema_predicate_param(unify.schema_params, p_name).ok_or(())?;
            unify_schema_predicate(
                unify.env,
                unify.ctx,
                p_name,
                param_args,
                t_name,
                unify.schema_params,
                unify.schema_subst,
            )?;
            if p_args.len() != t_args.len() {
                return Err(());
            }
            for (p_arg, t_arg) in p_args.iter().zip(t_args) {
                unify_term(p_arg, t_arg, unify)?;
            }
            Ok(())
        }
        (Formula::PredApp(p_name, p_args), Formula::PredApp(t_name, t_args))
            if p_name == t_name && p_args.len() == t_args.len() =>
        {
            for (p_arg, t_arg) in p_args.iter().zip(t_args) {
                unify_term(p_arg, t_arg, unify)?;
            }
            Ok(())
        }
        (Formula::And(p_left, p_right), Formula::And(t_left, t_right))
        | (Formula::Or(p_left, p_right), Formula::Or(t_left, t_right))
        | (Formula::Implies(p_left, p_right), Formula::Implies(t_left, t_right)) => {
            unify_formula(p_left, t_left, unify)?;
            unify_formula(p_right, t_right, unify)
        }
        (
            Formula::Forall {
                var: p_var,
                var_type: p_ty,
                body: p_body,
            },
            Formula::Forall {
                var: t_var,
                var_type: t_ty,
                body: t_body,
            },
        )
        | (
            Formula::Exists {
                var: p_var,
                var_type: p_ty,
                body: p_body,
            },
            Formula::Exists {
                var: t_var,
                var_type: t_ty,
                body: t_body,
            },
        ) => {
            let renamed = subst_formula_term(t_body, t_var, &Term::Var(p_var.clone()));
            unify_type(p_ty, t_ty, unify.schema_params, unify.schema_subst)?;
            unify_formula(p_body, &renamed, unify)
        }
        _ => Err(()),
    }
}

fn unify_term(pattern: &Term, target: &Term, unify: &mut UnifyState<'_>) -> Result<(), ()> {
    match pattern {
        Term::Var(name) if unify.term_metas.contains(name) => {
            if let Some(existing) = unify.term_subst.get(name) {
                if existing == target {
                    Ok(())
                } else {
                    Err(())
                }
            } else {
                unify.term_subst.insert(name.clone(), target.clone());
                Ok(())
            }
        }
        Term::Var(name) if schema_term_param(unify.schema_params, name).is_some() => {
            let param_ty = schema_term_param(unify.schema_params, name).ok_or(())?;
            if let Some(existing) = unify.schema_subst.term_args.get(name) {
                if existing == target {
                    Ok(())
                } else {
                    Err(())
                }
            } else {
                let actual_ty = validate_term(unify.env, unify.ctx, target).map_err(|_| ())?;
                unify_type(
                    param_ty,
                    &actual_ty,
                    unify.schema_params,
                    unify.schema_subst,
                )?;
                unify
                    .schema_subst
                    .term_args
                    .insert(name.clone(), target.clone());
                Ok(())
            }
        }
        Term::Var(_) => {
            if pattern == target {
                Ok(())
            } else {
                Err(())
            }
        }
        Term::App(p_name, p_args) => {
            let Term::App(t_name, t_args) = target else {
                return Err(());
            };
            if p_name != t_name || p_args.len() != t_args.len() {
                return Err(());
            }
            for (p_arg, t_arg) in p_args.iter().zip(t_args) {
                unify_term(p_arg, t_arg, unify)?;
            }
            Ok(())
        }
        Term::Zero => {
            if matches!(target, Term::Zero) {
                Ok(())
            } else {
                Err(())
            }
        }
        Term::Succ(pattern) => {
            let Term::Succ(target) = target else {
                return Err(());
            };
            unify_term(pattern, target, unify)
        }
        Term::Add(p_left, p_right) => {
            let Term::Add(t_left, t_right) = target else {
                return Err(());
            };
            unify_term(p_left, t_left, unify)?;
            unify_term(p_right, t_right, unify)
        }
        Term::EmptySet(pattern_ty) => {
            let Term::EmptySet(target_ty) = target else {
                return Err(());
            };
            unify_type(
                pattern_ty,
                target_ty,
                unify.schema_params,
                unify.schema_subst,
            )
        }
        Term::Singleton(pattern) => {
            let Term::Singleton(target) = target else {
                return Err(());
            };
            unify_term(pattern, target, unify)
        }
        Term::Union(p_left, p_right) => {
            let Term::Union(t_left, t_right) = target else {
                return Err(());
            };
            unify_term(p_left, t_left, unify)?;
            unify_term(p_right, t_right, unify)
        }
        Term::Inter(p_left, p_right) => {
            let Term::Inter(t_left, t_right) = target else {
                return Err(());
            };
            unify_term(p_left, t_left, unify)?;
            unify_term(p_right, t_right, unify)
        }
        Term::Diff(p_left, p_right) => {
            let Term::Diff(t_left, t_right) = target else {
                return Err(());
            };
            unify_term(p_left, t_left, unify)?;
            unify_term(p_right, t_right, unify)
        }
    }
}

fn schema_prop_param(params: &[Param], name: &str) -> bool {
    params
        .iter()
        .any(|param| param.name == name && matches!(param.kind, ParamKind::Prop))
}

fn schema_predicate_param<'a>(params: &'a [Param], name: &str) -> Option<&'a [Type]> {
    params.iter().find_map(|param| match &param.kind {
        ParamKind::Predicate(args) if param.name == name => Some(args.as_slice()),
        _ => None,
    })
}

fn schema_type_param(params: &[Param], name: &str) -> bool {
    params
        .iter()
        .any(|param| param.name == name && matches!(param.kind, ParamKind::Type))
}

fn schema_term_param<'a>(params: &'a [Param], name: &str) -> Option<&'a Type> {
    params.iter().find_map(|param| match &param.kind {
        ParamKind::Term(ty) if param.name == name => Some(ty),
        _ => None,
    })
}

fn unify_schema_prop(
    name: &str,
    target: &Formula,
    schema_subst: &mut SchemaSubst,
) -> Result<(), ()> {
    if let Some(existing) = schema_subst.formula_args.get(name) {
        if existing == target {
            Ok(())
        } else {
            Err(())
        }
    } else {
        schema_subst
            .formula_args
            .insert(name.to_string(), target.clone());
        Ok(())
    }
}

fn unify_schema_predicate(
    env: &Env,
    ctx: &Context,
    name: &str,
    param_args: &[Type],
    target_name: &str,
    schema_params: &[Param],
    schema_subst: &mut SchemaSubst,
) -> Result<(), ()> {
    if let Some(existing) = schema_subst.predicate_args.get(name) {
        if existing != target_name {
            return Err(());
        }
    } else {
        schema_subst
            .predicate_args
            .insert(name.to_string(), target_name.to_string());
    }

    let signature = predicate_signature(env, ctx, target_name).ok_or(())?;
    if signature.len() != param_args.len() {
        return Err(());
    }
    for (pattern, target) in param_args.iter().zip(signature.iter()) {
        unify_type(pattern, target, schema_params, schema_subst)?;
    }
    Ok(())
}

fn unify_type(
    pattern: &Type,
    target: &Type,
    schema_params: &[Param],
    schema_subst: &mut SchemaSubst,
) -> Result<(), ()> {
    match pattern {
        Type::Set(pattern_elem) => {
            let Type::Set(target_elem) = target else {
                return Err(());
            };
            unify_type(pattern_elem, target_elem, schema_params, schema_subst)
        }
        Type::Named(name) if schema_type_param(schema_params, name) => {
            if let Some(existing) = schema_subst.type_args.get(name) {
                if existing == target {
                    Ok(())
                } else {
                    Err(())
                }
            } else {
                schema_subst.type_args.insert(name.clone(), target.clone());
                Ok(())
            }
        }
        _ => {
            if pattern == target {
                Ok(())
            } else {
                Err(())
            }
        }
    }
}

fn contradiction_step(env: &Env, goal: Goal) -> Result<StepResult, TacticError> {
    for binding in goal.context.proofs().iter().rev() {
        if !formulas_def_eq(env, &goal.context, &binding.formula, &Formula::False)
            .map_err(|err| TacticError::new(err.message))?
        {
            continue;
        }
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
        let mut pos = None;
        for binding in goal.context.proofs() {
            if formulas_def_eq(env, &goal.context, &binding.formula, premise)
                .map_err(|err| TacticError::new(err.message))?
            {
                pos = Some(binding);
                break;
            }
        }
        if let Some(pos) = pos {
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

    fn check_err_contains(source: &str, needle: &str) {
        let result = check_file(source);
        assert!(
            !result.diagnostics.is_empty(),
            "expected diagnostics, but file checked successfully"
        );
        let rendered = format!("{:#?}", result.diagnostics);
        assert!(
            rendered.contains(needle),
            "diagnostics did not contain `{needle}`:\n{rendered}"
        );
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

    #[test]
    fn forall_and_left_succeeds_constructively() {
        check_ok(
            r#"
mode constructive

sort Person

theorem forall_and_left
  (P : Person -> Prop)
  (Q : Person -> Prop)
  : (forall x : Person, P(x) /\ Q(x)) -> forall x : Person, P(x) := by
  intro h
  intro x
  exact (h x).left
"#,
        );
    }

    #[test]
    fn generic_type_parameter_succeeds_constructively() {
        check_ok(
            r#"
mode constructive

theorem forall_and_left
  (A : Type)
  (P : A -> Prop)
  (Q : A -> Prop)
  : (forall x : A, P(x) /\ Q(x)) -> forall x : A, P(x) := by
  intro h
  intro x
  exact (h x).left
"#,
        );
    }

    #[test]
    fn existential_witness_can_be_a_declared_const() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
pred Student(Person)

theorem student_exists : Student(alice) -> exists x : Person, Student(x) := by
  intro h
  exists alice
  exact h
"#,
        );
    }

    #[test]
    fn exists_and_left_succeeds_constructively() {
        check_ok(
            r#"
mode constructive

sort Person

theorem exists_and_left
  (P : Person -> Prop)
  (Q : Person -> Prop)
  : (exists x : Person, P(x) /\ Q(x)) -> exists x : Person, P(x) := by
  intro h
  cases h with
  | intro x hx =>
      exists x
      exact hx.left
"#,
        );
    }

    #[test]
    fn not_exists_to_forall_not_succeeds_constructively() {
        check_ok(
            r#"
mode constructive

sort Person

theorem not_exists_to_forall_not
  (P : Person -> Prop)
  : not (exists x : Person, P(x)) -> forall x : Person, not P(x) := by
  intro h
  intro x
  intro hp
  apply h
  exists x
  exact hp
"#,
        );
    }

    #[test]
    fn apply_instantiates_forall_from_goal() {
        check_ok(
            r#"
mode constructive

sort Person

theorem forall_apply
  (P : Person -> Prop)
  (Q : Person -> Prop)
  (a : Person)
  : (forall x : Person, P(x) -> Q(x)) -> P(a) -> Q(a) := by
  intro h
  intro hp
  apply h
  exact hp
"#,
        );
    }

    #[test]
    fn exact_instantiates_proposition_schema_theorem() {
        check_ok(
            r#"
mode constructive

theorem id (P : Prop) : P -> P := by
  intro h
  exact h

theorem use_id (Q : Prop) : Q -> Q := by
  exact id
"#,
        );
    }

    #[test]
    fn apply_instantiates_proposition_schema_theorem() {
        check_ok(
            r#"
mode constructive

theorem id (P : Prop) : P -> P := by
  intro h
  exact h

theorem use_id (Q : Prop) : Q -> Q := by
  intro h
  apply id
  exact h
"#,
        );
    }

    #[test]
    fn exact_accepts_explicit_proposition_schema_argument() {
        check_ok(
            r#"
mode constructive

theorem id (P : Prop) : P -> P := by
  intro h
  exact h

theorem use_id (Q : Prop) : Q -> Q := by
  exact id {P := Q}
"#,
        );
    }

    #[test]
    fn apply_accepts_explicit_proposition_schema_argument() {
        check_ok(
            r#"
mode constructive

theorem id (P : Prop) : P -> P := by
  intro h
  exact h

theorem use_id (Q : Prop) : Q -> Q := by
  intro h
  apply id {P := Q}
  exact h
"#,
        );
    }

    #[test]
    fn exact_instantiates_type_and_predicate_schema_theorem() {
        check_ok(
            r#"
mode constructive

sort Person

theorem forall_self
  (A : Type)
  (P : A -> Prop)
  : (forall x : A, P(x)) -> forall x : A, P(x) := by
  intro h
  exact h

theorem use_forall_self
  (P : Person -> Prop)
  : (forall x : Person, P(x)) -> forall x : Person, P(x) := by
  exact forall_self
"#,
        );
    }

    #[test]
    fn exact_accepts_explicit_type_predicate_and_term_schema_arguments() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
pred Happy(Person)

theorem term_id
  (A : Type)
  (P : A -> Prop)
  (a : A)
  : P(a) -> P(a) := by
  intro h
  exact h

theorem use_term_id : Happy(alice) -> Happy(alice) := by
  exact term_id {A := Person; P := Happy; a := alice}
"#,
        );
    }

    #[test]
    fn multi_argument_predicate_schema_type_checks() {
        check_ok(
            r#"
mode constructive

sort Person

theorem rel_self
  (R : Person -> Person -> Prop)
  (a : Person)
  : R(a, a) -> R(a, a) := by
  intro h
  exact h
"#,
        );
    }

    #[test]
    fn function_application_type_checks() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

theorem happy_mother : Happy(mother(alice)) -> Happy(mother(alice)) := by
  intro h
  exact h
"#,
        );
    }

    #[test]
    fn refl_proves_term_equality() {
        check_ok(
            r#"
mode constructive

sort Person

theorem eq_refl_person (a : Person) : a = a := by
  refl
"#,
        );
    }

    #[test]
    fn refl_proves_function_application_equality() {
        check_ok(
            r#"
mode constructive

sort Person
func mother : Person -> Person

theorem eq_refl_mother (a : Person) : mother(a) = mother(a) := by
  refl
"#,
        );
    }

    #[test]
    fn rewrite_proves_predicate_goal() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

theorem rewrite_predicate
  : alice = mother(alice) -> Happy(alice) -> Happy(mother(alice)) := by
  intro h
  intro ha
  rewrite h
  exact ha
"#,
        );
    }

    #[test]
    fn rewrite_proves_equality_goal() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person

theorem rewrite_equality
  : alice = mother(alice) -> alice = alice -> alice = mother(alice) := by
  intro h
  intro ha
  rewrite h
  exact ha
"#,
        );
    }

    #[test]
    fn rewrite_can_descend_under_quantifier_without_capture() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Likes(Person, Person)

theorem rewrite_under_forall
  : alice = mother(alice)
    -> (forall x : Person, Likes(x, alice))
    -> forall x : Person, Likes(x, mother(alice)) := by
  intro h
  intro ha
  rewrite h
  exact ha
"#,
        );
    }

    #[test]
    fn rewrite_rejects_non_equality_proof() {
        check_err_contains(
            r#"
mode constructive

theorem bad (P : Prop) : P -> P := by
  intro h
  rewrite h
"#,
            "rewrite expects an equality proof",
        );
    }

    #[test]
    fn rewrite_rejects_capture_under_quantifier() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person
pred Happy(Person)

theorem bad
  (x : Person)
  : alice = x -> (forall x : Person, Happy(alice)) -> forall x : Person, Happy(x) := by
  intro h
  intro ha
  rewrite h
"#,
            "rewrite could not find `x` in goal `forall x : Person, Happy(x)`",
        );
    }

    #[test]
    fn rewrite_rejects_missing_rhs_occurrence() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

theorem bad : alice = mother(alice) -> Happy(alice) -> Happy(alice) := by
  intro h
  intro ha
  rewrite h
"#,
            "rewrite could not find `mother(alice)` in goal `Happy(alice)`",
        );
    }

    #[test]
    fn formula_definition_can_be_used_by_exact() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

def HappyMother (x : Person) : Prop := Happy(mother(x))

theorem def_elim : HappyMother(alice) -> Happy(mother(alice)) := by
  intro h
  exact h

theorem def_intro : Happy(mother(alice)) -> HappyMother(alice) := by
  intro h
  exact h
"#,
        );
    }

    #[test]
    fn unfold_expands_definition_in_goal() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

def HappyMother (x : Person) : Prop := Happy(mother(x))

theorem unfold_goal : Happy(mother(alice)) -> HappyMother(alice) := by
  intro h
  unfold HappyMother
  exact h
"#,
        );
    }

    #[test]
    fn simp_unfolds_formula_definitions_in_goal() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

def HappyMother (x : Person) : Prop := Happy(mother(x))
def VeryHappyMother (x : Person) : Prop := HappyMother(x)

theorem simp_goal : Happy(mother(alice)) -> VeryHappyMother(alice) := by
  intro h
  simp
  exact h
"#,
        );
    }

    #[test]
    fn formula_definition_infers_type_parameter_from_term_argument() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person

def SelfEq (A : Type) (x : A) : Prop := x = x

theorem self_eq_alice : SelfEq(alice) := by
  simp
  refl
"#,
        );
    }

    #[test]
    fn formula_definition_arity_mismatch_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person
pred Happy(Person)

def PairHappy (x y : Person) : Prop := Happy(x)

theorem bad : PairHappy(alice) := by
"#,
            "definition `PairHappy` expects 2 argument(s), but got 1",
        );
    }

    #[test]
    fn formula_definition_rejects_uninferrable_type_parameter() {
        check_err_contains(
            r#"
mode constructive

def Mystery (A : Type) : Prop := True

theorem bad : Mystery := by
"#,
            "cannot infer type argument `A` for definition `Mystery`",
        );
    }

    #[test]
    fn unfold_rejects_missing_definition_occurrence() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person
pred Happy(Person)

def HappyAlice : Prop := Happy(alice)

theorem bad : True := by
  unfold HappyAlice
"#,
            "no occurrence of definition `HappyAlice` in goal `True`",
        );
    }

    #[test]
    fn simp_rejects_no_progress() {
        check_err_contains(
            r#"
mode constructive

theorem bad : True := by
  simp
"#,
            "simp made no progress on goal `True`",
        );
    }

    #[test]
    fn nat_addition_computes_under_simp() {
        check_ok(
            r#"
mode constructive

theorem add_zero_left (n : Nat) : add(0, n) = n := by
  simp
  refl

theorem add_succ_left (n m : Nat) : add(succ(n), m) = succ(add(n, m)) := by
  simp
  refl

theorem add_one_zero : add(succ(0), 0) = succ(0) := by
  simp
  refl
"#,
        );
    }

    #[test]
    fn nat_induction_proves_add_zero_right() {
        check_ok(
            r#"
mode constructive

theorem add_zero_right (n : Nat) : add(n, 0) = n := by
  induction n with
  | zero =>
      simp
      refl
  | succ k ih =>
      simp
      rewrite ih
      refl
"#,
        );
    }

    #[test]
    fn induction_rejects_hypothesis_depending_on_variable() {
        check_err_contains(
            r#"
mode constructive

pred P(Nat)

theorem bad (n : Nat) : P(n) -> P(n) := by
  intro h
  induction n with
  | zero =>
      exact h
  | succ k ih =>
      exact h
"#,
            "cannot induct on `n` while hypothesis `h` depends on it",
        );
    }

    #[test]
    fn set_membership_computes_under_simp() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person

theorem singleton_member : alice in singleton(alice) := by
  simp
  refl

theorem empty_member_implies_false : alice in empty(Person) -> False := by
  intro h
  exact h
"#,
        );
    }

    #[test]
    fn subset_computes_under_simp() {
        check_ok(
            r#"
mode constructive

sort Person

theorem inter_subset_left (A B : Set Person) : inter(A, B) subset A := by
  simp
  intro x
  intro hx
  exact hx.left

theorem subset_refl (A : Set Person) : A subset A := by
  simp
  intro x
  intro hx
  exact hx
"#,
        );
    }

    #[test]
    fn subset_hypothesis_can_be_applied_after_normalization() {
        check_ok(
            r#"
mode constructive

sort Person

theorem subset_apply
  (A B : Set Person)
  (a : Person)
  : A subset B -> a in A -> a in B := by
  intro h
  intro ha
  apply h
  exact ha
"#,
        );
    }

    #[test]
    fn axiom_can_be_referenced_like_a_theorem() {
        check_ok(
            r#"
mode constructive

axiom ax_id (P : Prop) : P -> P

theorem use_axiom (P : Prop) : P -> P := by
  exact ax_id
"#,
        );
    }

    #[test]
    fn set_extensionality_axiom_proves_inter_comm() {
        check_ok(
            r#"
mode constructive

axiom set_ext
  (T : Type)
  (A B : Set T)
  : (forall x : T, x in A <-> x in B) -> A = B

theorem inter_comm
  (T : Type)
  (A B : Set T)
  : inter(A, B) = inter(B, A) := by
  apply set_ext
  intro x
  simp
  split
  intro hx
  split
  exact hx.right
  exact hx.left
  intro hx
  split
  exact hx.right
  exact hx.left
"#,
        );
    }

    #[test]
    fn axiom_redeclaration_is_rejected() {
        check_err_contains(
            r#"
mode constructive

axiom trusted : True
theorem trusted : True := by
"#,
            "cannot redeclare `trusted` as a theorem",
        );
    }

    #[test]
    fn set_type_parameter_works_with_subset_simp() {
        check_ok(
            r#"
mode constructive

theorem subset_refl
  (T : Type)
  (A : Set T)
  : A subset A := by
  simp
  intro x
  intro hx
  exact hx
"#,
        );
    }

    #[test]
    fn membership_type_mismatch_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
sort Color
const alice : Person
const red : Color

theorem bad : alice in singleton(red) := by
"#,
            "membership compares `alice` of type `Person` with a set of `Color`",
        );
    }

    #[test]
    fn unknown_type_in_parameter_is_rejected() {
        check_err_contains(
            r#"
mode constructive

theorem bad (x : Person) : True := by
"#,
            "unknown type `Person`",
        );
    }

    #[test]
    fn unknown_proposition_atom_is_rejected() {
        check_err_contains(
            r#"
mode constructive

theorem bad : P -> P := by
  intro h
  exact h
"#,
            "unknown proposition variable `P`",
        );
    }

    #[test]
    fn unknown_predicate_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person

theorem bad : Missing(alice) := by
"#,
            "unknown predicate `Missing`",
        );
    }

    #[test]
    fn predicate_arity_mismatch_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person
pred Student(Person)

theorem bad : Student(alice, alice) := by
"#,
            "expects 1 argument(s), but got 2",
        );
    }

    #[test]
    fn predicate_argument_type_mismatch_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
sort Color
const red : Color
pred Student(Person)

theorem bad : Student(red) := by
"#,
            "has type `Color`, but expected `Person`",
        );
    }

    #[test]
    fn schema_theorem_ref_that_cannot_be_instantiated_is_rejected() {
        check_err_contains(
            r#"
mode constructive

theorem id (P : Prop) : P -> P := by
  intro h
  exact h

theorem bad : True := by
  exact id
"#,
            "cannot instantiate theorem for goal `True`",
        );
    }

    #[test]
    fn unknown_explicit_schema_argument_is_rejected() {
        check_err_contains(
            r#"
mode constructive

theorem id (P : Prop) : P -> P := by
  intro h
  exact h

theorem bad (Q : Prop) : Q -> Q := by
  exact id {Missing := Q}
"#,
            "has no schema argument `Missing`",
        );
    }

    #[test]
    fn duplicate_explicit_schema_argument_is_rejected() {
        check_err_contains(
            r#"
mode constructive

theorem id (P : Prop) : P -> P := by
  intro h
  exact h

theorem bad (Q : Prop) : Q -> Q := by
  exact id {P := Q; P := Q}
"#,
            "was provided more than once",
        );
    }

    #[test]
    fn unknown_function_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person
pred Happy(Person)

theorem bad : Happy(parent(alice)) := by
"#,
            "unknown function `parent`",
        );
    }

    #[test]
    fn function_arity_mismatch_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

theorem bad : Happy(mother(alice, alice)) := by
"#,
            "expects 1 argument(s), but got 2",
        );
    }

    #[test]
    fn function_argument_type_mismatch_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
sort Color
const red : Color
func mother : Person -> Person
pred Happy(Person)

theorem bad : Happy(mother(red)) := by
"#,
            "has type `Color`, but expected `Person`",
        );
    }

    #[test]
    fn equality_type_mismatch_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
sort Color
const alice : Person
const red : Color

theorem bad : alice = red := by
  refl
"#,
            "equality compares `alice` of type `Person` with `red` of type `Color`",
        );
    }

    #[test]
    fn refl_rejects_non_equality_goal() {
        check_err_contains(
            r#"
mode constructive

theorem bad : True := by
  refl
"#,
            "refl expects an equality goal",
        );
    }

    #[test]
    fn refl_rejects_non_identical_sides() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person

theorem bad : mother(alice) = alice := by
  refl
"#,
            "the sides are not identical",
        );
    }
}
