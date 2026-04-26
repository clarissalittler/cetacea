use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

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
    PredLambda {
        params: Vec<LambdaParam>,
        body: Box<Formula>,
    },
    Zero,
    Succ(Box<Term>),
    Add(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    EmptySet(Type),
    Singleton(Box<Term>),
    Union(Box<Term>, Box<Term>),
    Inter(Box<Term>, Box<Term>),
    Diff(Box<Term>, Box<Term>),
    Powerset(Box<Term>),
    SetBuilder {
        var: Name,
        var_type: Type,
        body: Box<Formula>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LambdaParam {
    pub name: Name,
    pub ty: Option<Type>,
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
            Term::PredLambda { params, body } => {
                write!(f, "fun ")?;
                for (idx, param) in params.iter().enumerate() {
                    if idx > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", param.name)?;
                }
                if let Some(ty) = params.first().and_then(|param| param.ty.as_ref()) {
                    write!(f, " : {ty}")?;
                }
                write!(f, " => {body}")
            }
            Term::Zero => write!(f, "0"),
            Term::Succ(term) => write!(f, "succ({term})"),
            Term::Add(left, right) => write!(f, "add({left}, {right})"),
            Term::Mul(left, right) => write!(f, "mul({left}, {right})"),
            Term::Sub(left, right) => write!(f, "sub({left}, {right})"),
            Term::EmptySet(ty) => write!(f, "empty({ty})"),
            Term::Singleton(term) => write!(f, "singleton({term})"),
            Term::Union(left, right) => write!(f, "union({left}, {right})"),
            Term::Inter(left, right) => write!(f, "inter({left}, {right})"),
            Term::Diff(left, right) => write!(f, "diff({left}, {right})"),
            Term::Powerset(term) => write!(f, "powerset({term})"),
            Term::SetBuilder {
                var,
                var_type,
                body,
            } => write!(f, "{{ {var} : {var_type} | {body} }}"),
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
    pub predicate_args: HashMap<Name, PredicateArg>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PredicateArg {
    Named(Name),
    Lambda {
        params: Vec<LambdaParam>,
        body: Formula,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClassicalRule {
    ExcludedMiddle,
    ByContra,
    DoubleNegationElim,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RewriteDirection {
    Backward,
    Forward,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TermDef {
    pub name: Name,
    pub params: Vec<Param>,
    pub ty: Type,
    pub body: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecDef {
    pub name: Name,
    pub param: Name,
    pub result_type: Type,
    pub zero_body: Term,
    pub step_var: Name,
    pub rec_name: Name,
    pub succ_body: Term,
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
    term_defs: HashMap<Name, TermDef>,
    rec_defs: HashMap<Name, RecDef>,
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

    pub fn add_term_def(&mut self, def: TermDef) {
        self.term_defs.insert(def.name.clone(), def);
    }

    pub fn add_rec_def(&mut self, def: RecDef) {
        self.rec_defs.insert(def.name.clone(), def);
    }

    fn formula_def(&self, name: &str) -> Option<&FormulaDef> {
        self.defs.get(name)
    }

    fn term_def(&self, name: &str) -> Option<&TermDef> {
        self.term_defs.get(name)
    }

    fn rec_def(&self, name: &str) -> Option<&RecDef> {
        self.rec_defs.get(name)
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
            || self.term_defs.contains_key(name)
            || self.rec_defs.contains_key(name)
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
        "Nat"
            | "Set"
            | "succ"
            | "add"
            | "mul"
            | "sub"
            | "le"
            | "empty"
            | "singleton"
            | "union"
            | "inter"
            | "diff"
            | "powerset"
    )
}

static BUILTIN_LE_SIGNATURE: [Type; 2] = [Type::Nat, Type::Nat];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceLocation {
    pub path: Option<String>,
    pub line: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Option<Span>,
    pub location: Option<SourceLocation>,
    pub message: String,
    pub notes: Vec<String>,
}

impl Diagnostic {
    fn error(message: impl Into<String>) -> Self {
        Self {
            span: None,
            location: None,
            message: message.into(),
            notes: Vec::new(),
        }
    }

    fn with_location(mut self, path: Option<&Path>, line: usize) -> Self {
        self.location = Some(SourceLocation {
            path: path.map(|path| path.display().to_string()),
            line,
        });
        self
    }

    fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }
}

fn diagnostic_at(
    source_path: Option<&Path>,
    line: usize,
    message: impl Into<String>,
) -> Diagnostic {
    Diagnostic::error(message).with_location(source_path, line)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckedTheorem {
    pub name: Name,
    pub mode_used: LogicMode,
    pub is_axiom: bool,
    pub is_imported: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CheckResult {
    pub theorems: Vec<CheckedTheorem>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn check_file(source: &str) -> CheckResult {
    let mut checker = FileChecker::new();
    checker.check_source(source, None);
    checker.finish()
}

pub fn check_file_at_path(path: impl AsRef<Path>) -> CheckResult {
    let mut checker = FileChecker::new();
    checker.check_path(path.as_ref());
    checker.finish()
}

struct FileChecker {
    env: Env,
    result: CheckResult,
    loaded_files: HashSet<PathBuf>,
    import_stack: Vec<PathBuf>,
}

impl FileChecker {
    fn new() -> Self {
        Self {
            env: Env::new(),
            result: CheckResult::default(),
            loaded_files: HashSet::new(),
            import_stack: Vec::new(),
        }
    }

    fn finish(self) -> CheckResult {
        self.result
    }

    fn check_source(&mut self, source: &str, base_dir: Option<&Path>) {
        let file = match parse_file(source) {
            Ok(file) => file,
            Err(err) => {
                self.result
                    .diagnostics
                    .push(parse_diagnostic(None, err, None));
                return;
            }
        };
        self.check_commands(file.commands, base_dir, false, None);
    }

    fn check_path(&mut self, path: &Path) {
        let canonical_path = match path.canonicalize() {
            Ok(path) => path,
            Err(err) => {
                self.result.diagnostics.push(
                    Diagnostic::error(format!("could not read `{}`", path.display()))
                        .with_note(err.to_string()),
                );
                return;
            }
        };
        self.check_canonical_path(canonical_path, false);
    }

    fn check_import(
        &mut self,
        import_path: &str,
        base_dir: Option<&Path>,
        source_path: Option<&Path>,
        line: usize,
    ) {
        let canonical_path = match self.resolve_import_path(import_path, base_dir) {
            Ok(path) => path,
            Err(mut diagnostic) => {
                diagnostic = diagnostic.with_location(source_path, line);
                self.result.diagnostics.push(diagnostic);
                return;
            }
        };
        self.check_canonical_path(canonical_path, true);
    }

    fn resolve_import_path(
        &self,
        import_path: &str,
        base_dir: Option<&Path>,
    ) -> Result<PathBuf, Diagnostic> {
        let raw = Path::new(import_path);
        let mut candidates = Vec::new();
        if raw.is_absolute() {
            candidates.push(raw.to_path_buf());
        } else {
            if let Some(base_dir) = base_dir {
                candidates.push(base_dir.join(raw));
            }
            candidates.push(raw.to_path_buf());
        }

        let mut last_error = None;
        for candidate in candidates {
            match candidate.canonicalize() {
                Ok(path) => return Ok(path),
                Err(err) => last_error = Some((candidate, err)),
            }
        }

        let mut diagnostic = Diagnostic::error(format!("could not read import `{import_path}`"));
        if let Some((candidate, err)) = last_error {
            diagnostic = diagnostic.with_note(format!("{}: {err}", candidate.display()));
        }
        Err(diagnostic)
    }

    fn check_canonical_path(&mut self, path: PathBuf, is_imported: bool) {
        if self.loaded_files.contains(&path) {
            return;
        }
        if self.import_stack.contains(&path) {
            self.result.diagnostics.push(
                Diagnostic::error(format!("import cycle involving `{}`", path.display()))
                    .with_note("the file is already being checked"),
            );
            return;
        }

        let source = match fs::read_to_string(&path) {
            Ok(source) => source,
            Err(err) => {
                self.result.diagnostics.push(
                    Diagnostic::error(format!("could not read `{}`", path.display()))
                        .with_note(err.to_string()),
                );
                return;
            }
        };
        let file = match parse_file(&source) {
            Ok(file) => file,
            Err(err) => {
                self.result.diagnostics.push(parse_diagnostic(
                    Some(path.as_path()),
                    err,
                    Some(format!("could not parse `{}`", path.display())),
                ));
                return;
            }
        };

        self.import_stack.push(path.clone());
        let base_dir = path.parent().map(Path::to_path_buf);
        self.check_commands(
            file.commands,
            base_dir.as_deref(),
            is_imported,
            Some(path.as_path()),
        );
        self.import_stack.pop();
        self.loaded_files.insert(path);
    }

    fn check_commands(
        &mut self,
        commands: Vec<LocatedCommand>,
        base_dir: Option<&Path>,
        is_imported: bool,
        source_path: Option<&Path>,
    ) {
        let mut mode = LogicMode::Constructive;

        for located in commands {
            let line = located.line;
            let command = located.command;
            match command {
                Command::Import(path) => self.check_import(&path, base_dir, source_path, line),
                Command::Mode(next_mode) => mode = next_mode,
                Command::Sort(name) => {
                    if self.env.has_top_level_name(&name) {
                        self.result.diagnostics.push(diagnostic_at(
                            source_path,
                            line,
                            format!("cannot redeclare `{name}` as a sort"),
                        ));
                        continue;
                    }
                    self.env.add_sort(name);
                }
                Command::Const(name, ty) => {
                    if self.env.has_top_level_name(&name) {
                        self.result.diagnostics.push(diagnostic_at(
                            source_path,
                            line,
                            format!("cannot redeclare `{name}` as a constant"),
                        ));
                        continue;
                    }
                    if let Err(err) = validate_type(&self.env, &Context::new(), &ty) {
                        self.result.diagnostics.push(
                            diagnostic_at(
                                source_path,
                                line,
                                format!("constant `{name}` has invalid type"),
                            )
                            .with_note(err.message),
                        );
                        continue;
                    }
                    self.env.add_const(name, ty);
                }
                Command::Func(name, args, result_type) => {
                    if self.env.has_top_level_name(&name) {
                        self.result.diagnostics.push(diagnostic_at(
                            source_path,
                            line,
                            format!("cannot redeclare `{name}` as a function"),
                        ));
                        continue;
                    }
                    let empty_ctx = Context::new();
                    let mut invalid_type = None;
                    for ty in args.iter().chain(std::iter::once(&result_type)) {
                        if let Err(err) = validate_type(&self.env, &empty_ctx, ty) {
                            invalid_type = Some(err);
                            break;
                        }
                    }
                    if let Some(err) = invalid_type {
                        self.result.diagnostics.push(
                            diagnostic_at(
                                source_path,
                                line,
                                format!("function `{name}` has invalid type"),
                            )
                            .with_note(err.message),
                        );
                        continue;
                    }
                    self.env.add_func(name, args, result_type);
                }
                Command::Pred(name, args) => {
                    if self.env.has_top_level_name(&name) {
                        self.result.diagnostics.push(diagnostic_at(
                            source_path,
                            line,
                            format!("cannot redeclare `{name}` as a predicate"),
                        ));
                        continue;
                    }
                    let empty_ctx = Context::new();
                    if let Err(err) = args
                        .iter()
                        .try_for_each(|arg| validate_type(&self.env, &empty_ctx, arg))
                    {
                        self.result.diagnostics.push(
                            diagnostic_at(
                                source_path,
                                line,
                                format!("predicate `{name}` has invalid argument type"),
                            )
                            .with_note(err.message),
                        );
                        continue;
                    }
                    self.env.add_pred(name, args);
                }
                Command::Def(decl) => {
                    if self.env.has_top_level_name(&decl.name) {
                        self.result.diagnostics.push(diagnostic_at(
                            source_path,
                            line,
                            format!("cannot redeclare `{}` as a definition", decl.name),
                        ));
                        continue;
                    }
                    let def_ctx = match build_theorem_context(&self.env, &decl.params) {
                        Ok(ctx) => ctx,
                        Err(err) => {
                            self.result.diagnostics.push(
                                diagnostic_at(
                                    source_path,
                                    line,
                                    format!("definition `{}` has invalid parameters", decl.name),
                                )
                                .with_note(err.message),
                            );
                            continue;
                        }
                    };
                    match (decl.result, decl.body) {
                        (DefResult::Formula, DefBody::Formula(body)) => {
                            if let Err(err) = validate_formula(&self.env, &def_ctx, &body) {
                                self.result.diagnostics.push(
                                    diagnostic_at(
                                        source_path,
                                        line,
                                        format!("definition `{}` has invalid body", decl.name),
                                    )
                                    .with_note(err.message)
                                    .with_note(format!("body: {body}")),
                                );
                                continue;
                            }
                            self.env.add_def(FormulaDef {
                                name: decl.name,
                                params: decl.params,
                                body,
                            });
                        }
                        (DefResult::Term(ty), DefBody::Term(body)) => {
                            if let Err(err) = validate_type(&self.env, &def_ctx, &ty) {
                                self.result.diagnostics.push(
                                    diagnostic_at(
                                        source_path,
                                        line,
                                        format!("definition `{}` has invalid type", decl.name),
                                    )
                                    .with_note(err.message),
                                );
                                continue;
                            }
                            match validate_term(&self.env, &def_ctx, &body) {
                                Ok(actual) if actual == ty => {
                                    self.env.add_term_def(TermDef {
                                        name: decl.name,
                                        params: decl.params,
                                        ty,
                                        body,
                                    });
                                }
                                Ok(actual) => {
                                    self.result.diagnostics.push(
                                        diagnostic_at(
                                            source_path,
                                            line,
                                            format!("definition `{}` has invalid body", decl.name),
                                        )
                                        .with_note(format!(
                                            "body has type `{actual}`, but expected `{ty}`"
                                        ))
                                        .with_note(format!("body: {body}")),
                                    );
                                    continue;
                                }
                                Err(err) => {
                                    self.result.diagnostics.push(
                                        diagnostic_at(
                                            source_path,
                                            line,
                                            format!("definition `{}` has invalid body", decl.name),
                                        )
                                        .with_note(err.message)
                                        .with_note(format!("body: {body}")),
                                    );
                                    continue;
                                }
                            }
                        }
                        (DefResult::Formula, DefBody::Term(_))
                        | (DefResult::Term(_), DefBody::Formula(_)) => {
                            unreachable!("definition parser pairs result and body")
                        }
                    }
                }
                Command::RecDef(decl) => {
                    if self.env.has_top_level_name(&decl.name) {
                        self.result.diagnostics.push(diagnostic_at(
                            source_path,
                            line,
                            format!("cannot redeclare `{}` as a recursive definition", decl.name),
                        ));
                        continue;
                    }
                    if let Err(err) = validate_type(&self.env, &Context::new(), &decl.result_type) {
                        self.result.diagnostics.push(
                            diagnostic_at(
                                source_path,
                                line,
                                format!(
                                    "recursive definition `{}` has invalid result type",
                                    decl.name
                                ),
                            )
                            .with_note(err.message),
                        );
                        continue;
                    }
                    match validate_term(&self.env, &Context::new(), &decl.zero_body) {
                        Ok(actual) if actual == decl.result_type => {}
                        Ok(actual) => {
                            self.result.diagnostics.push(
                                diagnostic_at(
                                    source_path,
                                    line,
                                    format!(
                                        "recursive definition `{}` has invalid zero case",
                                        decl.name
                                    ),
                                )
                                .with_note(format!(
                                    "zero case has type `{actual}`, but expected `{}`",
                                    decl.result_type
                                )),
                            );
                            continue;
                        }
                        Err(err) => {
                            self.result.diagnostics.push(
                                diagnostic_at(
                                    source_path,
                                    line,
                                    format!(
                                        "recursive definition `{}` has invalid zero case",
                                        decl.name
                                    ),
                                )
                                .with_note(err.message),
                            );
                            continue;
                        }
                    }

                    let mut step_ctx = Context::new();
                    step_ctx.add_term(decl.step_var.clone(), Type::Nat);
                    step_ctx.add_term(decl.rec_name.clone(), decl.result_type.clone());
                    match validate_term(&self.env, &step_ctx, &decl.succ_body) {
                        Ok(actual) if actual == decl.result_type => {}
                        Ok(actual) => {
                            self.result.diagnostics.push(
                                diagnostic_at(
                                    source_path,
                                    line,
                                    format!(
                                        "recursive definition `{}` has invalid successor case",
                                        decl.name
                                    ),
                                )
                                .with_note(format!(
                                    "successor case has type `{actual}`, but expected `{}`",
                                    decl.result_type
                                )),
                            );
                            continue;
                        }
                        Err(err) => {
                            self.result.diagnostics.push(
                                diagnostic_at(
                                    source_path,
                                    line,
                                    format!(
                                        "recursive definition `{}` has invalid successor case",
                                        decl.name
                                    ),
                                )
                                .with_note(err.message),
                            );
                            continue;
                        }
                    }

                    self.env.add_rec_def(RecDef {
                        name: decl.name,
                        param: decl.param,
                        result_type: decl.result_type,
                        zero_body: decl.zero_body,
                        step_var: decl.step_var,
                        rec_name: decl.rec_name,
                        succ_body: decl.succ_body,
                    });
                }
                Command::Axiom(decl) => {
                    if self.env.has_top_level_name(&decl.name) {
                        self.result.diagnostics.push(diagnostic_at(
                            source_path,
                            line,
                            format!("cannot redeclare `{}` as an axiom", decl.name),
                        ));
                        continue;
                    }
                    let axiom_ctx = match build_theorem_context(&self.env, &decl.params) {
                        Ok(ctx) => ctx,
                        Err(err) => {
                            self.result.diagnostics.push(
                                diagnostic_at(
                                    source_path,
                                    line,
                                    format!("axiom `{}` has invalid parameters", decl.name),
                                )
                                .with_note(err.message),
                            );
                            continue;
                        }
                    };
                    if let Err(err) = validate_formula(&self.env, &axiom_ctx, &decl.statement) {
                        self.result.diagnostics.push(
                            diagnostic_at(
                                source_path,
                                line,
                                format!("axiom `{}` has invalid statement", decl.name),
                            )
                            .with_note(err.message)
                            .with_note(format!("target: {}", decl.statement)),
                        );
                        continue;
                    }

                    self.env.add_theorem(Theorem {
                        name: decl.name.clone(),
                        params: decl.params,
                        statement: decl.statement,
                        proof: None,
                        mode_used: mode,
                        is_axiom: true,
                    });
                    self.result.theorems.push(CheckedTheorem {
                        name: decl.name,
                        mode_used: mode,
                        is_axiom: true,
                        is_imported,
                    });
                }
                Command::Theorem(decl) => {
                    if self.env.has_top_level_name(&decl.name) {
                        self.result.diagnostics.push(diagnostic_at(
                            source_path,
                            line,
                            format!("cannot redeclare `{}` as a theorem", decl.name),
                        ));
                        continue;
                    }
                    let theorem_ctx = match build_theorem_context(&self.env, &decl.params) {
                        Ok(ctx) => ctx,
                        Err(err) => {
                            self.result.diagnostics.push(
                                diagnostic_at(
                                    source_path,
                                    line,
                                    format!("theorem `{}` has invalid parameters", decl.name),
                                )
                                .with_note(err.message),
                            );
                            continue;
                        }
                    };
                    if let Err(err) = validate_formula(&self.env, &theorem_ctx, &decl.statement) {
                        self.result.diagnostics.push(
                            diagnostic_at(
                                source_path,
                                line,
                                format!("theorem `{}` has invalid statement", decl.name),
                            )
                            .with_note(err.message)
                            .with_note(format!("target: {}", decl.statement)),
                        );
                        continue;
                    }
                    let proof = match prove(
                        &self.env,
                        theorem_ctx.clone(),
                        decl.statement.clone(),
                        &decl.tactics,
                        mode,
                    ) {
                        Ok(proof) => proof,
                        Err(err) => {
                            let target = err.target.as_ref().unwrap_or(&decl.statement);
                            self.result.diagnostics.push(
                                diagnostic_at(
                                    source_path,
                                    err.line.unwrap_or(line),
                                    format!("theorem `{}` failed: {}", decl.name, err.message),
                                )
                                .with_note(format!("target: {target}")),
                            );
                            continue;
                        }
                    };

                    let mode_used =
                        match check_proof(&self.env, &theorem_ctx, &proof, &decl.statement, mode) {
                            Ok(mode_used) => mode_used,
                            Err(err) => {
                                self.result.diagnostics.push(
                                    diagnostic_at(
                                        source_path,
                                        line,
                                        format!(
                                            "theorem `{}` was rejected by the kernel: {}",
                                            decl.name, err.message
                                        ),
                                    )
                                    .with_note(format!("target: {}", decl.statement)),
                                );
                                continue;
                            }
                        };

                    if matches!(mode, LogicMode::Constructive)
                        && matches!(mode_used, LogicMode::Classical)
                    {
                        self.result.diagnostics.push(
                            diagnostic_at(
                                source_path,
                                line,
                                format!(
                                    "theorem `{}` uses classical reasoning in constructive mode",
                                    decl.name
                                ),
                            )
                            .with_note("change to `mode classical` or use a constructive proof"),
                        );
                        continue;
                    }

                    self.env.add_theorem(Theorem {
                        name: decl.name.clone(),
                        params: decl.params,
                        statement: decl.statement,
                        proof: Some(proof),
                        mode_used,
                        is_axiom: false,
                    });
                    self.result.theorems.push(CheckedTheorem {
                        name: decl.name,
                        mode_used,
                        is_axiom: false,
                        is_imported,
                    });
                }
            }
        }
    }
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
            if !formula_rewrite_matches(&checked_body.formula, target, &left, &right)
                && !formula_rewrite_matches(&checked_body.formula, target, &right, &left)
            {
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
                let expected: Vec<Type> =
                    args.iter().map(|ty| subst_type_schema(ty, subst)).collect();
                validate_predicate_arg(env, ctx, arg, &expected)?;
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
        Term::Var(name) => {
            if let Some(ty) = ctx.lookup_term(name).or_else(|| env.consts.get(name)) {
                return Ok(ty.clone());
            }
            if let Some(def) = env.term_def(name) {
                let expected = term_def_expected_args(def);
                if expected == 0 {
                    return Ok(def.ty.clone());
                }
                return Err(ValidationError::new(format!(
                    "definition `{name}` expects {expected} argument(s), but got 0"
                )));
            }
            if env.rec_def(name).is_some() {
                return Err(ValidationError::new(format!(
                    "recursive definition `{name}` expects 1 argument(s), but got 0"
                )));
            }
            Err(ValidationError::new(format!("unknown term `{name}`")))
        }
        Term::App(name, args) => {
            if let Some(func) = env.funcs.get(name) {
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
                return Ok(func.result.clone());
            }

            let Some(def) = env.term_def(name) else {
                if let Some(def) = env.rec_def(name) {
                    if args.len() != 1 {
                        return Err(ValidationError::new(format!(
                            "recursive definition `{name}` expects 1 argument(s), but got {}",
                            args.len()
                        )));
                    }
                    let actual = validate_term(env, ctx, &args[0])?;
                    if actual != Type::Nat {
                        return Err(ValidationError::new(format!(
                            "argument 1 of `{name}` has type `{actual}`, but expected `Nat`"
                        )));
                    }
                    return Ok(def.result_type.clone());
                }
                return Err(ValidationError::new(format!("unknown function `{name}`")));
            };
            let (_, ty) = instantiate_term_def(env, ctx, def, args)?;
            Ok(ty)
        }
        Term::PredLambda { .. } => Err(ValidationError::new(
            "predicate lambda cannot be used as a first-order term",
        )),
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
        Term::Add(left, right) | Term::Mul(left, right) | Term::Sub(left, right) => {
            let name = match term {
                Term::Add(_, _) => "add",
                Term::Mul(_, _) => "mul",
                Term::Sub(_, _) => "sub",
                _ => unreachable!("matched Nat binary term"),
            };
            for (idx, term) in [left.as_ref(), right.as_ref()].iter().enumerate() {
                let actual = validate_term(env, ctx, term)?;
                if actual != Type::Nat {
                    return Err(ValidationError::new(format!(
                        "argument {} of `{name}` has type `{actual}`, but expected `Nat`",
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
        Term::Powerset(set) => {
            let set_ty = validate_term(env, ctx, set)?;
            let Type::Set(elem_ty) = set_ty else {
                return Err(ValidationError::new(format!(
                    "powerset argument has type `{set_ty}`, but expected a set"
                )));
            };
            Ok(Type::Set(Box::new(Type::Set(elem_ty))))
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
        Term::SetBuilder {
            var,
            var_type,
            body,
        } => {
            validate_type(env, ctx, var_type)?;
            let mut body_ctx = ctx.clone();
            body_ctx.add_term(var.clone(), var_type.clone());
            validate_formula(env, &body_ctx, body)?;
            Ok(Type::Set(Box::new(var_type.clone())))
        }
    }
}

fn predicate_signature<'a>(env: &'a Env, ctx: &'a Context, name: &str) -> Option<&'a [Type]> {
    if name == "le" {
        return Some(&BUILTIN_LE_SIGNATURE);
    }
    ctx.lookup_predicate_var(name)
        .or_else(|| env.preds.get(name).map(Vec::as_slice))
}

fn validate_predicate_arg(
    env: &Env,
    ctx: &Context,
    arg: &PredicateArg,
    expected: &[Type],
) -> Result<(), ValidationError> {
    match arg {
        PredicateArg::Named(name) => {
            let Some(signature) = predicate_signature(env, ctx, name) else {
                return Err(ValidationError::new(format!("unknown predicate `{name}`")));
            };
            if signature == expected {
                Ok(())
            } else {
                Err(ValidationError::new(format!(
                    "predicate `{name}` does not match expected type `{}`",
                    predicate_type_display(expected)
                )))
            }
        }
        PredicateArg::Lambda { params, body } => {
            if params.len() != expected.len() {
                return Err(ValidationError::new(format!(
                    "predicate lambda expects {} argument(s), but target predicate type has {}",
                    params.len(),
                    expected.len()
                )));
            }
            let mut body_ctx = ctx.clone();
            for (param, ty) in params.iter().zip(expected) {
                if let Some(annotation) = &param.ty {
                    validate_type(env, ctx, annotation)?;
                    if annotation != ty {
                        return Err(ValidationError::new(format!(
                            "predicate lambda parameter `{}` has type `{annotation}`, but expected `{ty}`",
                            param.name
                        )));
                    }
                }
                validate_type(env, ctx, ty)?;
                body_ctx.add_term(param.name.clone(), ty.clone());
            }
            validate_formula(env, &body_ctx, body)
        }
    }
}

fn predicate_type_display(args: &[Type]) -> String {
    let mut parts = args.iter().map(ToString::to_string).collect::<Vec<_>>();
    parts.push("Prop".to_string());
    parts.join(" -> ")
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
        .filter(|param| !matches!(param.kind, ParamKind::Type))
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
            ParamKind::Prop => {
                let Some(arg) = args.next() else {
                    return Err(ValidationError::new(format!(
                        "definition `{}` expects {expected_args} argument(s)",
                        def.name
                    )));
                };
                let formula = formula_def_prop_argument(arg)?;
                validate_formula(env, ctx, &formula)?;
                schema_subst
                    .formula_args
                    .insert(param.name.clone(), formula);
                arg_idx += 1;
            }
            ParamKind::Predicate(param_args) => {
                let Some(arg) = args.next() else {
                    return Err(ValidationError::new(format!(
                        "definition `{}` expects {expected_args} argument(s)",
                        def.name
                    )));
                };
                let pred_arg = formula_def_predicate_argument(arg)?;
                validate_predicate_schema_arg(
                    env,
                    ctx,
                    &pred_arg,
                    param_args,
                    &def.params,
                    &mut schema_subst,
                )?;
                schema_subst
                    .predicate_args
                    .insert(param.name.clone(), pred_arg);
                arg_idx += 1;
            }
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

fn formula_def_prop_argument(arg: &Term) -> Result<Formula, ValidationError> {
    match arg {
        Term::Var(name) => Ok(Formula::Atom(name.clone())),
        other => Err(ValidationError::new(format!(
            "proposition definition argument must be a proposition name, got `{other}`"
        ))),
    }
}

fn formula_def_predicate_argument(arg: &Term) -> Result<PredicateArg, ValidationError> {
    match arg {
        Term::Var(name) => Ok(PredicateArg::Named(name.clone())),
        Term::PredLambda { params, body } => Ok(PredicateArg::Lambda {
            params: params.clone(),
            body: *body.clone(),
        }),
        other => Err(ValidationError::new(format!(
            "predicate definition argument must be a predicate name, got `{other}`"
        ))),
    }
}

fn validate_predicate_schema_arg(
    env: &Env,
    ctx: &Context,
    arg: &PredicateArg,
    param_args: &[Type],
    schema_params: &[Param],
    schema_subst: &mut SchemaSubst,
) -> Result<(), ValidationError> {
    match arg {
        PredicateArg::Named(name) => {
            let Some(signature) = predicate_signature(env, ctx, name) else {
                return Err(ValidationError::new(format!("unknown predicate `{name}`")));
            };
            if signature.len() != param_args.len() {
                return Err(ValidationError::new(format!(
                    "predicate `{name}` expects {} argument(s), but definition parameter expects {}",
                    signature.len(),
                    param_args.len()
                )));
            }
            for (pattern, actual) in param_args.iter().zip(signature.iter()) {
                unify_type(pattern, actual, schema_params, schema_subst).map_err(|_| {
                    let expected = subst_type_schema(pattern, schema_subst);
                    ValidationError::new(format!(
                        "predicate argument `{name}` has incompatible type `{actual}`, expected `{expected}`"
                    ))
                })?;
            }
            Ok(())
        }
        PredicateArg::Lambda { params, body } => {
            if params.len() != param_args.len() {
                return Err(ValidationError::new(format!(
                    "predicate lambda expects {} argument(s), but target predicate type has {}",
                    params.len(),
                    param_args.len()
                )));
            }
            let mut body_ctx = ctx.clone();
            for (param, pattern) in params.iter().zip(param_args) {
                if let Some(annotation) = &param.ty {
                    validate_type(env, ctx, annotation)?;
                    unify_type(pattern, annotation, schema_params, schema_subst).map_err(|_| {
                        let expected = subst_type_schema(pattern, schema_subst);
                        ValidationError::new(format!(
                            "predicate lambda parameter `{}` has type `{annotation}`, but expected `{expected}`",
                            param.name
                        ))
                    })?;
                }
                let param_ty = subst_type_schema(pattern, schema_subst);
                validate_type(env, ctx, &param_ty)?;
                body_ctx.add_term(param.name.clone(), param_ty);
            }
            validate_formula(env, &body_ctx, body)
        }
    }
}

fn term_def_expected_args(def: &TermDef) -> usize {
    def.params
        .iter()
        .filter(|param| !matches!(param.kind, ParamKind::Type))
        .count()
}

fn instantiate_term_def(
    env: &Env,
    ctx: &Context,
    def: &TermDef,
    args: &[Term],
) -> Result<(Term, Type), ValidationError> {
    let expected_args = term_def_expected_args(def);
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
            ParamKind::Prop => {
                let Some(arg) = args.next() else {
                    return Err(ValidationError::new(format!(
                        "definition `{}` expects {expected_args} argument(s)",
                        def.name
                    )));
                };
                let formula = formula_def_prop_argument(arg)?;
                validate_formula(env, ctx, &formula)?;
                schema_subst
                    .formula_args
                    .insert(param.name.clone(), formula);
                arg_idx += 1;
            }
            ParamKind::Predicate(param_args) => {
                let Some(arg) = args.next() else {
                    return Err(ValidationError::new(format!(
                        "definition `{}` expects {expected_args} argument(s)",
                        def.name
                    )));
                };
                let pred_arg = formula_def_predicate_argument(arg)?;
                validate_predicate_schema_arg(
                    env,
                    ctx,
                    &pred_arg,
                    param_args,
                    &def.params,
                    &mut schema_subst,
                )?;
                schema_subst
                    .predicate_args
                    .insert(param.name.clone(), pred_arg);
                arg_idx += 1;
            }
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

    let ty = subst_type_schema(&def.ty, &schema_subst);
    validate_type(env, ctx, &ty)?;
    let body = subst_term_terms(&subst_term_schema(&def.body, &schema_subst), &term_subst);
    let actual = validate_term(env, ctx, &body)?;
    if actual != ty {
        return Err(ValidationError::new(format!(
            "definition `{}` instantiated to type `{actual}`, but expected `{ty}`",
            def.name
        )));
    }
    Ok((body, ty))
}

fn formulas_def_eq(
    env: &Env,
    ctx: &Context,
    left: &Formula,
    right: &Formula,
) -> Result<bool, ValidationError> {
    Ok(alpha_eq_formula(
        &normalize_formula_defs(env, ctx, left)?,
        &normalize_formula_defs(env, ctx, right)?,
    ))
}

#[derive(Default)]
struct AlphaEnv {
    left_to_right: HashMap<Name, Name>,
    right_to_left: HashMap<Name, Name>,
}

fn alpha_eq_formula(left: &Formula, right: &Formula) -> bool {
    alpha_eq_formula_with(left, right, &mut AlphaEnv::default())
}

fn with_alpha_binding(
    env: &mut AlphaEnv,
    left: &Name,
    right: &Name,
    check: impl FnOnce(&mut AlphaEnv) -> bool,
) -> bool {
    let old_left = env.left_to_right.insert(left.clone(), right.clone());
    let old_right = env.right_to_left.insert(right.clone(), left.clone());
    let result = check(env);
    if let Some(old) = old_left {
        env.left_to_right.insert(left.clone(), old);
    } else {
        env.left_to_right.remove(left);
    }
    if let Some(old) = old_right {
        env.right_to_left.insert(right.clone(), old);
    } else {
        env.right_to_left.remove(right);
    }
    result
}

fn alpha_eq_var(left: &Name, right: &Name, env: &AlphaEnv) -> bool {
    if let Some(mapped) = env.left_to_right.get(left) {
        mapped == right
    } else if env.right_to_left.contains_key(right) {
        false
    } else {
        left == right
    }
}

fn alpha_eq_terms(left: &[Term], right: &[Term], env: &mut AlphaEnv) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| alpha_eq_term(left, right, env))
}

fn alpha_eq_term(left: &Term, right: &Term, env: &mut AlphaEnv) -> bool {
    match (left, right) {
        (Term::Var(left), Term::Var(right)) => alpha_eq_var(left, right, env),
        (Term::App(left_name, left_args), Term::App(right_name, right_args)) => {
            left_name == right_name && alpha_eq_terms(left_args, right_args, env)
        }
        (
            Term::PredLambda {
                params: left_params,
                body: left_body,
            },
            Term::PredLambda {
                params: right_params,
                body: right_body,
            },
        ) => alpha_eq_predicate_lambda(left_params, left_body, right_params, right_body, env),
        (Term::Zero, Term::Zero) => true,
        (Term::Succ(left), Term::Succ(right)) => alpha_eq_term(left, right, env),
        (Term::Add(left_a, left_b), Term::Add(right_a, right_b))
        | (Term::Mul(left_a, left_b), Term::Mul(right_a, right_b))
        | (Term::Sub(left_a, left_b), Term::Sub(right_a, right_b))
        | (Term::Union(left_a, left_b), Term::Union(right_a, right_b))
        | (Term::Inter(left_a, left_b), Term::Inter(right_a, right_b))
        | (Term::Diff(left_a, left_b), Term::Diff(right_a, right_b)) => {
            alpha_eq_term(left_a, right_a, env) && alpha_eq_term(left_b, right_b, env)
        }
        (Term::EmptySet(left_ty), Term::EmptySet(right_ty)) => left_ty == right_ty,
        (Term::Singleton(left), Term::Singleton(right))
        | (Term::Powerset(left), Term::Powerset(right)) => alpha_eq_term(left, right, env),
        (
            Term::SetBuilder {
                var: left_var,
                var_type: left_ty,
                body: left_body,
            },
            Term::SetBuilder {
                var: right_var,
                var_type: right_ty,
                body: right_body,
            },
        ) => {
            left_ty == right_ty
                && with_alpha_binding(env, left_var, right_var, |env| {
                    alpha_eq_formula_with(left_body, right_body, env)
                })
        }
        _ => false,
    }
}

fn alpha_eq_predicate_lambda(
    left_params: &[LambdaParam],
    left_body: &Formula,
    right_params: &[LambdaParam],
    right_body: &Formula,
    env: &mut AlphaEnv,
) -> bool {
    if left_params.len() != right_params.len()
        || left_params
            .iter()
            .zip(right_params)
            .any(|(left, right)| left.ty != right.ty)
    {
        return false;
    }

    fn bind_next(
        idx: usize,
        left_params: &[LambdaParam],
        left_body: &Formula,
        right_params: &[LambdaParam],
        right_body: &Formula,
        env: &mut AlphaEnv,
    ) -> bool {
        if idx == left_params.len() {
            alpha_eq_formula_with(left_body, right_body, env)
        } else {
            with_alpha_binding(
                env,
                &left_params[idx].name,
                &right_params[idx].name,
                |env| {
                    bind_next(
                        idx + 1,
                        left_params,
                        left_body,
                        right_params,
                        right_body,
                        env,
                    )
                },
            )
        }
    }

    bind_next(0, left_params, left_body, right_params, right_body, env)
}

fn alpha_eq_formula_with(left: &Formula, right: &Formula, env: &mut AlphaEnv) -> bool {
    match (left, right) {
        (Formula::True, Formula::True) | (Formula::False, Formula::False) => true,
        (Formula::Atom(left), Formula::Atom(right)) => left == right,
        (Formula::PredApp(left_name, left_args), Formula::PredApp(right_name, right_args)) => {
            left_name == right_name && alpha_eq_terms(left_args, right_args, env)
        }
        (Formula::Eq(left_a, left_b), Formula::Eq(right_a, right_b))
        | (Formula::In(left_a, left_b), Formula::In(right_a, right_b))
        | (Formula::Subset(left_a, left_b), Formula::Subset(right_a, right_b)) => {
            alpha_eq_term(left_a, right_a, env) && alpha_eq_term(left_b, right_b, env)
        }
        (Formula::And(left_a, left_b), Formula::And(right_a, right_b))
        | (Formula::Or(left_a, left_b), Formula::Or(right_a, right_b))
        | (Formula::Implies(left_a, left_b), Formula::Implies(right_a, right_b)) => {
            alpha_eq_formula_with(left_a, right_a, env)
                && alpha_eq_formula_with(left_b, right_b, env)
        }
        (
            Formula::Forall {
                var: left_var,
                var_type: left_ty,
                body: left_body,
            },
            Formula::Forall {
                var: right_var,
                var_type: right_ty,
                body: right_body,
            },
        )
        | (
            Formula::Exists {
                var: left_var,
                var_type: left_ty,
                body: left_body,
            },
            Formula::Exists {
                var: right_var,
                var_type: right_ty,
                body: right_body,
            },
        ) => {
            left_ty == right_ty
                && with_alpha_binding(env, left_var, right_var, |env| {
                    alpha_eq_formula_with(left_body, right_body, env)
                })
        }
        _ => false,
    }
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
            if only.is_none() && name == "le" && args.len() == 2 {
                let left = normalize_term(env, ctx, &args[0])?;
                let right = normalize_term(env, ctx, &args[1])?;
                let simplified = simplify_le_formula(left, right);
                let changed = &simplified != formula;
                if changed {
                    let (simplified, _) = unfold_formula_defs(env, ctx, &simplified, only)?;
                    return Ok((simplified, true));
                }
                return Ok((simplified, false));
            }
            if only.is_none() {
                let simplified_args: Vec<Term> = args
                    .iter()
                    .map(|arg| normalize_term(env, ctx, arg))
                    .collect::<Result<_, _>>()?;
                let simplified = Formula::PredApp(name.clone(), simplified_args);
                return Ok((simplified.clone(), &simplified != formula));
            }
            Ok((formula.clone(), false))
        }
        Formula::Eq(left, right) => {
            if only.is_some() {
                return Ok((formula.clone(), false));
            }
            let simplified = Formula::eq(
                normalize_term(env, ctx, left)?,
                normalize_term(env, ctx, right)?,
            );
            Ok((simplified.clone(), &simplified != formula))
        }
        Formula::In(elem, set) => {
            if only.is_some() {
                return Ok((formula.clone(), false));
            }
            let elem = normalize_term(env, ctx, elem)?;
            let set = normalize_term(env, ctx, set)?;
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
                Term::Powerset(base) => Formula::subset(elem, *base),
                Term::SetBuilder {
                    var,
                    var_type: _,
                    body,
                } => subst_formula_term(&body, &var, &elem),
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
            let left = normalize_term(env, ctx, left)?;
            let right = normalize_term(env, ctx, right)?;
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

fn simplify_le_formula(left: Term, right: Term) -> Formula {
    match (left, right) {
        (Term::Zero, _) => Formula::True,
        (Term::Succ(_), Term::Zero) => Formula::False,
        (Term::Succ(left), Term::Succ(right)) => simplify_le_formula(*left, *right),
        (left, right) => Formula::PredApp("le".to_string(), vec![left, right]),
    }
}

fn normalize_term_compute(term: &Term) -> Term {
    match term {
        Term::Var(_) | Term::Zero | Term::EmptySet(_) => term.clone(),
        Term::App(name, args) => Term::App(
            name.clone(),
            args.iter().map(normalize_term_compute).collect(),
        ),
        Term::PredLambda { .. } => term.clone(),
        Term::Succ(term) => Term::Succ(Box::new(normalize_term_compute(term))),
        Term::Add(left, right) => {
            let left = normalize_term_compute(left);
            let right = normalize_term_compute(right);
            match (left, right) {
                (Term::Zero, right) => right,
                (left, Term::Zero) => left,
                (Term::Succ(pred), right) => {
                    normalize_term_compute(&Term::Succ(Box::new(Term::Add(pred, Box::new(right)))))
                }
                (left, Term::Succ(pred)) => {
                    normalize_term_compute(&Term::Succ(Box::new(Term::Add(Box::new(left), pred))))
                }
                (left, right) => Term::Add(Box::new(left), Box::new(right)),
            }
        }
        Term::Mul(left, right) => {
            let left = normalize_term_compute(left);
            let right = normalize_term_compute(right);
            match (left, right) {
                (Term::Zero, _) | (_, Term::Zero) => Term::Zero,
                (Term::Succ(pred), right) => normalize_term_compute(&Term::Add(
                    Box::new(right.clone()),
                    Box::new(Term::Mul(pred, Box::new(right))),
                )),
                (left, Term::Succ(pred)) => normalize_term_compute(&Term::Add(
                    Box::new(left.clone()),
                    Box::new(Term::Mul(Box::new(left), pred)),
                )),
                (left, right) => Term::Mul(Box::new(left), Box::new(right)),
            }
        }
        Term::Sub(left, right) => {
            let left = normalize_term_compute(left);
            let right = normalize_term_compute(right);
            match (left, right) {
                (left, Term::Zero) => left,
                (Term::Zero, _) => Term::Zero,
                (Term::Succ(left), Term::Succ(right)) => {
                    normalize_term_compute(&Term::Sub(left, right))
                }
                (left, right) => Term::Sub(Box::new(left), Box::new(right)),
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
        Term::Powerset(term) => Term::Powerset(Box::new(normalize_term_compute(term))),
        Term::SetBuilder {
            var,
            var_type,
            body,
        } => Term::SetBuilder {
            var: var.clone(),
            var_type: var_type.clone(),
            body: body.clone(),
        },
    }
}

fn normalize_term(env: &Env, ctx: &Context, term: &Term) -> Result<Term, ValidationError> {
    match term {
        Term::Var(name) => {
            if let Some(def) = env.term_def(name) {
                let (body, _) = instantiate_term_def(env, ctx, def, &[])?;
                return normalize_term(env, ctx, &body);
            }
            Ok(term.clone())
        }
        Term::App(name, args) => {
            if let Some(def) = env.term_def(name) {
                let (body, _) = instantiate_term_def(env, ctx, def, args)?;
                return normalize_term(env, ctx, &body);
            }
            if let Some(def) = env.rec_def(name) {
                if args.len() == 1 {
                    let arg = normalize_term(env, ctx, &args[0])?;
                    return normalize_rec_def(env, ctx, def, arg);
                }
            }
            Ok(Term::App(
                name.clone(),
                args.iter()
                    .map(|arg| normalize_term(env, ctx, arg))
                    .collect::<Result<_, _>>()?,
            ))
        }
        Term::PredLambda { .. } => Ok(term.clone()),
        Term::Zero | Term::EmptySet(_) => Ok(term.clone()),
        Term::Succ(term) => Ok(Term::Succ(Box::new(normalize_term(env, ctx, term)?))),
        Term::Add(left, right) => {
            let computed = Term::Add(
                Box::new(normalize_term(env, ctx, left)?),
                Box::new(normalize_term(env, ctx, right)?),
            );
            Ok(normalize_term_compute(&computed))
        }
        Term::Mul(left, right) => {
            let computed = Term::Mul(
                Box::new(normalize_term(env, ctx, left)?),
                Box::new(normalize_term(env, ctx, right)?),
            );
            Ok(normalize_term_compute(&computed))
        }
        Term::Sub(left, right) => {
            let computed = Term::Sub(
                Box::new(normalize_term(env, ctx, left)?),
                Box::new(normalize_term(env, ctx, right)?),
            );
            Ok(normalize_term_compute(&computed))
        }
        Term::Singleton(term) => Ok(Term::Singleton(Box::new(normalize_term(env, ctx, term)?))),
        Term::Union(left, right) => Ok(Term::Union(
            Box::new(normalize_term(env, ctx, left)?),
            Box::new(normalize_term(env, ctx, right)?),
        )),
        Term::Inter(left, right) => Ok(Term::Inter(
            Box::new(normalize_term(env, ctx, left)?),
            Box::new(normalize_term(env, ctx, right)?),
        )),
        Term::Diff(left, right) => Ok(Term::Diff(
            Box::new(normalize_term(env, ctx, left)?),
            Box::new(normalize_term(env, ctx, right)?),
        )),
        Term::Powerset(term) => Ok(Term::Powerset(Box::new(normalize_term(env, ctx, term)?))),
        Term::SetBuilder {
            var,
            var_type,
            body,
        } => {
            let mut body_ctx = ctx.clone();
            body_ctx.add_term(var.clone(), var_type.clone());
            let (body, _) = unfold_formula_defs(env, &body_ctx, body, None)?;
            Ok(Term::SetBuilder {
                var: var.clone(),
                var_type: var_type.clone(),
                body: Box::new(body),
            })
        }
    }
}

fn normalize_rec_def(
    env: &Env,
    ctx: &Context,
    def: &RecDef,
    arg: Term,
) -> Result<Term, ValidationError> {
    match arg {
        Term::Zero => normalize_term(env, ctx, &def.zero_body),
        Term::Succ(pred) => {
            let pred_term = *pred;
            let recursive = normalize_term(
                env,
                ctx,
                &Term::App(def.name.clone(), vec![pred_term.clone()]),
            )?;
            let with_step = subst_term(&def.succ_body, &def.step_var, &pred_term);
            let with_rec = subst_term(&with_step, &def.rec_name, &recursive);
            normalize_term(env, ctx, &with_rec)
        }
        other => Ok(Term::App(def.name.clone(), vec![other])),
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
        Term::PredLambda { params, body } => {
            let mut scoped = subst.clone();
            for param in params {
                scoped.term_args.remove(&param.name);
            }
            Term::PredLambda {
                params: params
                    .iter()
                    .map(|param| LambdaParam {
                        name: param.name.clone(),
                        ty: param.ty.as_ref().map(|ty| subst_type_schema(ty, subst)),
                    })
                    .collect(),
                body: Box::new(subst_formula_schema(body, &scoped)),
            }
        }
        Term::Zero => Term::Zero,
        Term::Succ(term) => Term::Succ(Box::new(subst_term_schema(term, subst))),
        Term::Add(left, right) => Term::Add(
            Box::new(subst_term_schema(left, subst)),
            Box::new(subst_term_schema(right, subst)),
        ),
        Term::Mul(left, right) => Term::Mul(
            Box::new(subst_term_schema(left, subst)),
            Box::new(subst_term_schema(right, subst)),
        ),
        Term::Sub(left, right) => Term::Sub(
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
        Term::Powerset(term) => Term::Powerset(Box::new(subst_term_schema(term, subst))),
        Term::SetBuilder {
            var,
            var_type,
            body,
        } => {
            let scoped = subst_without_term_arg(subst, var);
            Term::SetBuilder {
                var: var.clone(),
                var_type: subst_type_schema(var_type, subst),
                body: Box::new(subst_formula_schema(body, &scoped)),
            }
        }
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
        Formula::PredApp(name, args) => {
            let args: Vec<Term> = args
                .iter()
                .map(|arg| subst_term_schema(arg, subst))
                .collect();
            match subst.predicate_args.get(name) {
                Some(PredicateArg::Named(name)) => Formula::PredApp(name.clone(), args),
                Some(PredicateArg::Lambda { params, body }) => {
                    apply_predicate_lambda(params, body, &args)
                }
                None => Formula::PredApp(name.clone(), args),
            }
        }
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

fn apply_predicate_lambda(params: &[LambdaParam], body: &Formula, args: &[Term]) -> Formula {
    let mut formula = body.clone();
    for (param, arg) in params.iter().zip(args) {
        formula = subst_formula_term(&formula, &param.name, arg);
    }
    formula
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
        Term::PredLambda { params, body } if params.iter().any(|param| param.name == var) => {
            Term::PredLambda {
                params: params.clone(),
                body: body.clone(),
            }
        }
        Term::PredLambda { params, body } => Term::PredLambda {
            params: params.clone(),
            body: Box::new(subst_formula_term(body, var, replacement)),
        },
        Term::Zero => Term::Zero,
        Term::Succ(term) => Term::Succ(Box::new(subst_term(term, var, replacement))),
        Term::Add(left, right) => Term::Add(
            Box::new(subst_term(left, var, replacement)),
            Box::new(subst_term(right, var, replacement)),
        ),
        Term::Mul(left, right) => Term::Mul(
            Box::new(subst_term(left, var, replacement)),
            Box::new(subst_term(right, var, replacement)),
        ),
        Term::Sub(left, right) => Term::Sub(
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
        Term::Powerset(term) => Term::Powerset(Box::new(subst_term(term, var, replacement))),
        Term::SetBuilder {
            var: bound,
            var_type,
            body,
        } if bound == var => Term::SetBuilder {
            var: bound.clone(),
            var_type: var_type.clone(),
            body: body.clone(),
        },
        Term::SetBuilder {
            var: bound,
            var_type,
            body,
        } => Term::SetBuilder {
            var: bound.clone(),
            var_type: var_type.clone(),
            body: Box::new(subst_formula_term(body, var, replacement)),
        },
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
        Term::PredLambda { params, body } => {
            !params.iter().any(|param| param.name == name) && formula_has_free_term(body, name)
        }
        Term::Zero | Term::EmptySet(_) => false,
        Term::Succ(term) | Term::Singleton(term) | Term::Powerset(term) => {
            term_has_free_var(term, name)
        }
        Term::Add(left, right)
        | Term::Mul(left, right)
        | Term::Sub(left, right)
        | Term::Union(left, right)
        | Term::Inter(left, right)
        | Term::Diff(left, right) => {
            term_has_free_var(left, name) || term_has_free_var(right, name)
        }
        Term::SetBuilder { var, body, .. } if var == name => false,
        Term::SetBuilder { body, .. } => formula_has_free_term(body, name),
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
        Term::Mul(left, right) => {
            for replaced in replace_term_once(left, from, to) {
                results.push(Term::Mul(Box::new(replaced), right.clone()));
            }
            for replaced in replace_term_once(right, from, to) {
                results.push(Term::Mul(left.clone(), Box::new(replaced)));
            }
        }
        Term::Sub(left, right) => {
            for replaced in replace_term_once(left, from, to) {
                results.push(Term::Sub(Box::new(replaced), right.clone()));
            }
            for replaced in replace_term_once(right, from, to) {
                results.push(Term::Sub(left.clone(), Box::new(replaced)));
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
        Term::Powerset(inner) => {
            for replaced in replace_term_once(inner, from, to) {
                results.push(Term::Powerset(Box::new(replaced)));
            }
        }
        Term::SetBuilder {
            var,
            var_type,
            body,
        } => {
            if !term_has_free_var(from, var) && !term_has_free_var(to, var) {
                for replaced_body in replace_formula_once(body, from, to) {
                    results.push(Term::SetBuilder {
                        var: var.clone(),
                        var_type: var_type.clone(),
                        body: Box::new(replaced_body),
                    });
                }
            }
        }
        Term::PredLambda { params, body } => {
            if !params.iter().any(|param| {
                term_has_free_var(from, &param.name) || term_has_free_var(to, &param.name)
            }) {
                for replaced_body in replace_formula_once(body, from, to) {
                    results.push(Term::PredLambda {
                        params: params.clone(),
                        body: Box::new(replaced_body),
                    });
                }
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

fn formula_rewrite_sources(target: &Formula, needle: &Term, replacement: &Term) -> Vec<Formula> {
    replace_formula_once(target, needle, replacement)
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
        Term::PredLambda { body, .. } => 1 + formula_size(body),
        Term::Succ(term) | Term::Singleton(term) | Term::Powerset(term) => 1 + term_size(term),
        Term::Add(left, right)
        | Term::Mul(left, right)
        | Term::Sub(left, right)
        | Term::Union(left, right)
        | Term::Inter(left, right)
        | Term::Diff(left, right) => 1 + term_size(left) + term_size(right),
        Term::SetBuilder { body, .. } => 1 + formula_size(body),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TheoremDecl {
    name: Name,
    params: Vec<Param>,
    statement: Formula,
    tactics: Vec<LocatedTactic>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DefDecl {
    name: Name,
    params: Vec<Param>,
    result: DefResult,
    body: DefBody,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RecDefDecl {
    name: Name,
    param: Name,
    result_type: Type,
    zero_body: Term,
    step_var: Name,
    rec_name: Name,
    succ_body: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum DefResult {
    Formula,
    Term(Type),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum DefBody {
    Formula(Formula),
    Term(Term),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AxiomDecl {
    name: Name,
    params: Vec<Param>,
    statement: Formula,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Command {
    Import(String),
    Mode(LogicMode),
    Sort(Name),
    Const(Name, Type),
    Func(Name, Vec<Type>, Type),
    Pred(Name, Vec<Type>),
    Def(DefDecl),
    RecDef(RecDefDecl),
    Axiom(AxiomDecl),
    Theorem(TheoremDecl),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct File {
    commands: Vec<LocatedCommand>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LocatedCommand {
    line: usize,
    command: Command,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RawTacticLine {
    line: usize,
    text: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ParseError {
    message: String,
    line: Option<usize>,
    span: Option<Span>,
}

impl ParseError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            line: None,
            span: None,
        }
    }

    fn with_line(mut self, line: usize) -> Self {
        if self.line.is_none() {
            self.line = Some(line);
        }
        self
    }

    fn with_span(mut self, span: Span) -> Self {
        if self.span.is_none() {
            self.span = Some(span);
        }
        self
    }

    fn with_offset(mut self, offset: usize) -> Self {
        if let Some(span) = &mut self.span {
            span.start += offset;
            span.end += offset;
        }
        self
    }
}

fn parse_diagnostic(path: Option<&Path>, err: ParseError, message: Option<String>) -> Diagnostic {
    let has_context = message.is_some();
    let mut diagnostic = Diagnostic::error(message.unwrap_or_else(|| err.message.clone()));
    diagnostic.span = err.span;
    if let Some(line) = err.line {
        diagnostic = diagnostic.with_location(path, line);
    }
    if has_context {
        diagnostic = diagnostic.with_note(err.message);
    }
    diagnostic
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
    Arg(String),
    Projection(Projection),
}

enum PendingProofStep {
    ForallArg(Term),
    ImpArg(Proof),
    Projection(Projection),
}

impl ProofExpr {
    fn is_true_intro(&self) -> bool {
        self.base == "True" && self.explicit_args.is_empty() && self.steps.is_empty()
    }

    fn is_bare_theorem_ref(&self, env: &Env, ctx: &Context) -> bool {
        self.steps.is_empty()
            && ctx.lookup(&self.base).is_none()
            && env.theorem(&self.base).is_some()
    }

    fn has_explicit_args(&self) -> bool {
        !self.explicit_args.is_empty()
    }

    fn base_proof(&self, env: &Env, ctx: &Context) -> Result<Proof, TacticError> {
        if self.is_true_intro() {
            return Ok(Proof::TrueIntro);
        }
        if ctx.lookup(&self.base).is_some() {
            if self.has_explicit_args() {
                return Err(TacticError::new(
                    "explicit theorem arguments can only be used with theorem references",
                ));
            }
            Ok(Proof::Hyp(self.base.clone()))
        } else if let Some(theorem) = env.theorem(&self.base) {
            let subst = if self.has_explicit_args() {
                let subst = explicit_schema_subst(env, ctx, theorem, &self.explicit_args)?;
                ensure_schema_subst_complete(&theorem.params, &subst, Some(theorem.name.as_str()))?;
                subst
            } else {
                SchemaSubst::default()
            };
            Ok(Proof::TheoremRef {
                name: self.base.clone(),
                subst,
            })
        } else {
            if self.has_explicit_args() {
                return Err(TacticError::new(
                    "explicit theorem arguments can only be used with theorem references",
                ));
            }
            Ok(Proof::Hyp(self.base.clone()))
        }
    }

    fn to_proof(
        &self,
        env: &Env,
        ctx: &Context,
        allowed_mode: LogicMode,
    ) -> Result<Proof, TacticError> {
        if ctx.lookup(&self.base).is_none() {
            if let Some(theorem) = env.theorem(&self.base) {
                if !self.steps.is_empty() {
                    return self.theorem_application_to_proof(env, ctx, theorem, allowed_mode);
                }
            }
        }

        let mut proof = self.base_proof(env, ctx)?;

        for step in &self.steps {
            proof = match step {
                ProofStep::Arg(arg) => {
                    let checked = infer_proof(env, ctx, &proof, allowed_mode).map_err(|err| {
                        TacticError::new(format!(
                            "cannot apply proof expression `{}`: {}",
                            self.base, err.message
                        ))
                    })?;
                    let formula = normalize_formula_defs(env, ctx, &checked.formula)
                        .map_err(|err| TacticError::new(err.message))?;
                    match formula {
                        Formula::Forall { .. } => {
                            let term = parse_term_str(arg)
                                .map_err(|err| TacticError::new(err.message))?;
                            Proof::ForallElim {
                                proof_forall: Box::new(proof),
                                arg: term,
                            }
                        }
                        Formula::Implies(_, _) => {
                            let arg_expr = parse_proof_expr(arg)
                                .map_err(|err| TacticError::new(err.message))?;
                            let proof_arg =
                                proof_expr_for_inferred(env, ctx, &arg_expr, allowed_mode)?;
                            Proof::ImpElim {
                                proof_imp: Box::new(proof),
                                proof_arg: Box::new(proof_arg),
                            }
                        }
                        other => {
                            return Err(TacticError::new(format!(
                                "proof application expects a universal or implication proof, got `{other}`"
                            )))
                        }
                    }
                }
                ProofStep::Projection(Projection::Left) => Proof::AndElimLeft(Box::new(proof)),
                ProofStep::Projection(Projection::Right) => Proof::AndElimRight(Box::new(proof)),
            };
        }

        Ok(proof)
    }

    fn theorem_application_to_proof(
        &self,
        env: &Env,
        ctx: &Context,
        theorem: &Theorem,
        allowed_mode: LogicMode,
    ) -> Result<Proof, TacticError> {
        let mut schema_subst = explicit_schema_subst(env, ctx, theorem, &self.explicit_args)?;
        let mut term_subst = HashMap::new();
        let mut cursor = theorem.statement.clone();
        let mut pending = Vec::new();

        for step in &self.steps {
            match step {
                ProofStep::Arg(arg) => {
                    let cursor_inst = subst_formula_terms(
                        &subst_formula_schema(&cursor, &schema_subst),
                        &term_subst,
                    );
                    let cursor_norm = normalize_formula_defs(env, ctx, &cursor_inst)
                        .map_err(|err| TacticError::new(err.message))?;
                    match cursor_norm {
                        Formula::Forall {
                            var,
                            var_type,
                            body,
                        } => {
                            let term = parse_term_str(arg)
                                .map_err(|err| TacticError::new(err.message))?;
                            let actual =
                                validate_term(env, ctx, &term).map_err(|err| TacticError::new(err.message))?;
                            unify_type(&var_type, &actual, &theorem.params, &mut schema_subst)
                                .map_err(|_| {
                                    let expected = subst_type_schema(&var_type, &schema_subst);
                                    TacticError::new(format!(
                                        "term `{term}` has type `{actual}`, but expected `{expected}`"
                                    ))
                                })?;
                            term_subst.insert(var, term.clone());
                            pending.push(PendingProofStep::ForallArg(term));
                            cursor = *body;
                        }
                        Formula::Implies(premise, conclusion) => {
                            let arg_expr = parse_proof_expr(arg)
                                .map_err(|err| TacticError::new(err.message))?;
                            let proof_arg =
                                proof_expr_for_inferred(env, ctx, &arg_expr, allowed_mode)?;
                            let checked_arg =
                                infer_proof(env, ctx, &proof_arg, allowed_mode).map_err(|err| {
                                    TacticError::new(format!(
                                        "cannot apply theorem `{}`: {}",
                                        theorem.name, err.message
                                    ))
                                })?;
                            let arg_formula = normalize_formula_defs(env, ctx, &checked_arg.formula)
                                .map_err(|err| TacticError::new(err.message))?;
                            let premise_pattern =
                                subst_formula_terms(&premise, &term_subst);
                            {
                                let mut ignored_term_subst = HashMap::new();
                                let mut unify = UnifyState {
                                    env,
                                    ctx,
                                    term_metas: &[],
                                    schema_params: &theorem.params,
                                    term_subst: &mut ignored_term_subst,
                                    schema_subst: &mut schema_subst,
                                };
                                unify_formula(&premise_pattern, &arg_formula, &mut unify)
                                    .map_err(|_| {
                                        TacticError::new(format!(
                                            "proof argument has type `{}`, but expected `{}`",
                                            checked_arg.formula, premise_pattern
                                        ))
                                    })?;
                            }
                            pending.push(PendingProofStep::ImpArg(proof_arg));
                            cursor = *conclusion;
                        }
                        other => {
                            return Err(TacticError::new(format!(
                                "theorem application expects a universal or implication proof, got `{other}`"
                            )))
                        }
                    }
                }
                ProofStep::Projection(projection) => {
                    pending.push(PendingProofStep::Projection(projection.clone()));
                }
            }
        }

        ensure_schema_subst_complete(&theorem.params, &schema_subst, Some(theorem.name.as_str()))?;
        let mut proof = Proof::TheoremRef {
            name: theorem.name.clone(),
            subst: schema_subst,
        };
        for step in pending {
            proof = match step {
                PendingProofStep::ForallArg(arg) => Proof::ForallElim {
                    proof_forall: Box::new(proof),
                    arg,
                },
                PendingProofStep::ImpArg(proof_arg) => Proof::ImpElim {
                    proof_imp: Box::new(proof),
                    proof_arg: Box::new(proof_arg),
                },
                PendingProofStep::Projection(Projection::Left) => {
                    Proof::AndElimLeft(Box::new(proof))
                }
                PendingProofStep::Projection(Projection::Right) => {
                    Proof::AndElimRight(Box::new(proof))
                }
            };
        }
        Ok(proof)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tactic {
    Intro(Name),
    Exact(ProofExpr),
    Trivial,
    Assumption,
    Apply(ProofExpr),
    Split,
    Left,
    Right,
    CasesOr {
        expr: ProofExpr,
        left_name: Name,
        left_tactics: Vec<LocatedTactic>,
        right_name: Name,
        right_tactics: Vec<LocatedTactic>,
    },
    CasesExists {
        expr: ProofExpr,
        witness_name: Name,
        hyp_name: Name,
        body_tactics: Vec<LocatedTactic>,
    },
    Exists(Term),
    Refl,
    Rewrite {
        expr: ProofExpr,
        direction: RewriteDirection,
    },
    Unfold(Name),
    Simp,
    SimpAt(Name),
    SimpAll,
    SimpWith(Vec<Name>),
    Induction {
        var_name: Name,
        zero_tactics: Vec<LocatedTactic>,
        step_var: Name,
        ih_name: Name,
        step_tactics: Vec<LocatedTactic>,
    },
    Exfalso,
    Contradiction,
    ByCases {
        name: Name,
        formula: Formula,
    },
    ByContra(Name),
    ShowGoal,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LocatedTactic {
    line: usize,
    tactic: Tactic,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Token {
    kind: TokenKind,
    span: Span,
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

    fn current_span(&self) -> Span {
        self.tokens[self.pos].span
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
            Err(ParseError::new(format!("expected `{sym}`")).with_span(self.current_span()))
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
            _ => Err(ParseError::new("expected identifier").with_span(self.current_span())),
        }
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<(), ParseError> {
        if self.eat_ident(keyword) {
            Ok(())
        } else {
            Err(ParseError::new(format!("expected `{keyword}`")).with_span(self.current_span()))
        }
    }

    fn expect_eof(&self) -> Result<(), ParseError> {
        if matches!(self.peek(), TokenKind::Eof) {
            Ok(())
        } else {
            Err(ParseError::new("unexpected trailing input").with_span(self.current_span()))
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
        if self.eat_ident("fun") {
            let mut names = Vec::new();
            loop {
                names.push(self.expect_ident()?);
                if self.eat_sym("=>") {
                    let body = self.parse_formula()?;
                    return Ok(Term::PredLambda {
                        params: names
                            .into_iter()
                            .map(|name| LambdaParam { name, ty: None })
                            .collect(),
                        body: Box::new(body),
                    });
                }
                if self.eat_sym(":") {
                    let ty = self.parse_type()?;
                    self.expect_sym("=>")?;
                    let body = self.parse_formula()?;
                    return Ok(Term::PredLambda {
                        params: names
                            .into_iter()
                            .map(|name| LambdaParam {
                                name,
                                ty: Some(ty.clone()),
                            })
                            .collect(),
                        body: Box::new(body),
                    });
                }
            }
        }
        if self.eat_sym("{") {
            let var = self.expect_ident()?;
            self.expect_sym(":")?;
            let var_type = self.parse_type()?;
            self.expect_sym("|")?;
            let body = self.parse_formula()?;
            self.expect_sym("}")?;
            return Ok(Term::SetBuilder {
                var,
                var_type,
                body: Box::new(body),
            });
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
                ("mul", [left, right]) => {
                    Ok(Term::Mul(Box::new(left.clone()), Box::new(right.clone())))
                }
                ("sub", [left, right]) => {
                    Ok(Term::Sub(Box::new(left.clone()), Box::new(right.clone())))
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
                ("powerset", [arg]) => Ok(Term::Powerset(Box::new(arg.clone()))),
                ("succ" | "singleton" | "powerset", _) => Err(ParseError::new(format!(
                    "`{name}` expects exactly one argument"
                ))),
                ("add" | "mul" | "sub" | "union" | "inter" | "diff", _) => Err(ParseError::new(
                    format!("`{name}` expects exactly two arguments"),
                )),
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
            let vars = self.parse_binder_names()?;
            self.expect_sym(":")?;
            let var_type = self.parse_type()?;
            self.expect_sym(",")?;
            let mut body = self.parse_formula()?;
            for var in vars.into_iter().rev() {
                body = Formula::forall(var, var_type.clone(), body);
            }
            return Ok(body);
        }
        if self.eat_ident("exists") {
            let vars = self.parse_binder_names()?;
            self.expect_sym(":")?;
            let var_type = self.parse_type()?;
            self.expect_sym(",")?;
            let mut body = self.parse_formula()?;
            for var in vars.into_iter().rev() {
                body = Formula::exists(var, var_type.clone(), body);
            }
            return Ok(body);
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
            | Term::Mul(_, _)
            | Term::Sub(_, _)
            | Term::EmptySet(_)
            | Term::Singleton(_)
            | Term::Union(_, _)
            | Term::Inter(_, _)
            | Term::Diff(_, _)
            | Term::Powerset(_)
            | Term::PredLambda { .. }
            | Term::SetBuilder { .. } => {
                Err(ParseError::new(format!("term `{term}` is not a formula")))
            }
        }
    }

    fn parse_binder_names(&mut self) -> Result<Vec<Name>, ParseError> {
        let mut vars = Vec::new();
        loop {
            vars.push(self.expect_ident()?);
            if matches!(self.peek(), TokenKind::Sym(sym) if sym == ":") {
                break;
            }
        }
        Ok(vars)
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
                span: Span {
                    start: i,
                    end: i + 1,
                },
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
                span: Span { start, end: i },
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
        } else if rest.starts_with("=>") {
            Some("=>")
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
                '{' => Some("{"),
                '}' => Some("}"),
                '|' => Some("|"),
                _ => None,
            }
        };

        let Some(sym) = sym else {
            return Err(
                ParseError::new(format!("unexpected character `{ch}`")).with_span(Span {
                    start: i,
                    end: i + 1,
                }),
            );
        };
        tokens.push(Token {
            kind: TokenKind::Sym(sym.to_string()),
            span: Span {
                start: i,
                end: i + sym.chars().count(),
            },
        });
        i += sym.chars().count();
    }

    tokens.push(Token {
        kind: TokenKind::Eof,
        span: Span {
            start: chars.len(),
            end: chars.len(),
        },
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
        let command_line = i + 1;

        if let Some(rest) = trimmed.strip_prefix("import ") {
            commands.push(located_command(
                command_line,
                Command::Import(
                    parse_import_path(rest).map_err(|err| err.with_line(command_line))?,
                ),
            ));
            i += 1;
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("mode ") {
            let mode = match rest.trim() {
                "constructive" => LogicMode::Constructive,
                "classical" => LogicMode::Classical,
                other => {
                    return Err(
                        ParseError::new(format!("unknown mode `{other}`")).with_line(command_line)
                    )
                }
            };
            commands.push(located_command(command_line, Command::Mode(mode)));
            i += 1;
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("sort ") {
            let name = rest.trim();
            if name.is_empty() {
                return Err(
                    ParseError::new("sort declaration needs a name").with_line(command_line)
                );
            }
            commands.push(located_command(
                command_line,
                Command::Sort(name.to_string()),
            ));
            i += 1;
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("const ") {
            let Some((name, ty)) = rest.split_once(':') else {
                return Err(ParseError::new("const declaration expects `name : Type`")
                    .with_line(command_line));
            };
            commands.push(located_command(
                command_line,
                Command::Const(
                    name.trim().to_string(),
                    parse_type_str(ty.trim()).map_err(|err| err.with_line(command_line))?,
                ),
            ));
            i += 1;
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("func ") {
            let Some((name, ty)) = rest.split_once(':') else {
                return Err(ParseError::new("func declaration expects `name : A -> B`")
                    .with_line(command_line));
            };
            let (args, result) =
                parse_function_type_str(ty.trim()).map_err(|err| err.with_line(command_line))?;
            commands.push(located_command(
                command_line,
                Command::Func(name.trim().to_string(), args, result),
            ));
            i += 1;
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("pred ") {
            let (name, args) =
                parse_pred_decl(rest.trim()).map_err(|err| err.with_line(command_line))?;
            commands.push(located_command(command_line, Command::Pred(name, args)));
            i += 1;
            continue;
        }

        if trimmed.starts_with("defrec ") {
            let (name, param, result_type) =
                parse_defrec_header(trimmed).map_err(|err| err.with_line(command_line))?;

            i += 1;
            while i < lines.len() && strip_comment(lines[i]).trim().is_empty() {
                i += 1;
            }
            if i >= lines.len() {
                return Err(ParseError::new("recursive definition needs a zero case")
                    .with_line(command_line));
            }
            let zero_line = i + 1;
            let zero_body = parse_defrec_zero_arm(strip_comment(lines[i]).trim())
                .map_err(|err| err.with_line(zero_line))?;

            i += 1;
            while i < lines.len() && strip_comment(lines[i]).trim().is_empty() {
                i += 1;
            }
            if i >= lines.len() {
                return Err(
                    ParseError::new("recursive definition needs a successor case")
                        .with_line(command_line),
                );
            }
            let succ_line = i + 1;
            let (step_var, rec_name, succ_body) =
                parse_defrec_succ_arm(strip_comment(lines[i]).trim())
                    .map_err(|err| err.with_line(succ_line))?;

            commands.push(located_command(
                command_line,
                Command::RecDef(RecDefDecl {
                    name,
                    param,
                    result_type,
                    zero_body,
                    step_var,
                    rec_name,
                    succ_body,
                }),
            ));
            i += 1;
            continue;
        }

        if trimmed.starts_with("def ") {
            let mut header = String::from(trimmed);
            while !header.contains(":=") {
                i += 1;
                if i >= lines.len() {
                    return Err(ParseError::new("unterminated definition").with_line(command_line));
                }
                header.push(' ');
                header.push_str(strip_comment(lines[i]).trim());
            }

            let Some((header, body)) = header.split_once(":=") else {
                return Err(ParseError::new("expected `:=` in definition").with_line(command_line));
            };
            let (name, params, result) =
                parse_def_header(header).map_err(|err| err.with_line(command_line))?;
            let body = match &result {
                DefResult::Formula => DefBody::Formula(
                    parse_formula_str(body.trim()).map_err(|err| err.with_line(command_line))?,
                ),
                DefResult::Term(_) => DefBody::Term(
                    parse_term_str(body.trim()).map_err(|err| err.with_line(command_line))?,
                ),
            };
            commands.push(located_command(
                command_line,
                Command::Def(DefDecl {
                    name,
                    params,
                    result,
                    body,
                }),
            ));
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
            let (name, params, statement) =
                parse_axiom_header(&header).map_err(|err| err.with_line(command_line))?;
            commands.push(located_command(
                command_line,
                Command::Axiom(AxiomDecl {
                    name,
                    params,
                    statement,
                }),
            ));
            continue;
        }

        if trimmed.starts_with("theorem ") {
            let mut header = String::from(trimmed);
            while !header.contains(":= by") {
                i += 1;
                if i >= lines.len() {
                    return Err(
                        ParseError::new("unterminated theorem header").with_line(command_line)
                    );
                }
                header.push(' ');
                header.push_str(strip_comment(lines[i]).trim());
            }

            let Some((header, _)) = header.split_once(":= by") else {
                return Err(ParseError::new("expected `:= by` in theorem declaration")
                    .with_line(command_line));
            };
            let (name, params, statement) =
                parse_theorem_header(header).map_err(|err| err.with_line(command_line))?;

            i += 1;
            let mut tactic_lines = Vec::new();
            while i < lines.len() {
                let next = strip_comment(lines[i]).trim();
                if is_command_start(next) {
                    break;
                }
                tactic_lines.push(RawTacticLine {
                    line: i + 1,
                    text: strip_comment(lines[i]).to_string(),
                });
                i += 1;
            }

            commands.push(located_command(
                command_line,
                Command::Theorem(TheoremDecl {
                    name,
                    params,
                    statement,
                    tactics: parse_tactic_lines(&tactic_lines)
                        .map_err(|err| err.with_line(command_line))?,
                }),
            ));
            continue;
        }

        return Err(
            ParseError::new(format!("unsupported command `{trimmed}`")).with_line(command_line)
        );
    }

    Ok(File { commands })
}

fn located_command(line: usize, command: Command) -> LocatedCommand {
    LocatedCommand { line, command }
}

fn strip_comment(line: &str) -> &str {
    line.split_once("--")
        .map(|(before, _)| before)
        .unwrap_or(line)
}

fn is_command_start(trimmed: &str) -> bool {
    trimmed.starts_with("import ")
        || trimmed.starts_with("mode ")
        || trimmed.starts_with("theorem ")
        || trimmed.starts_with("sort ")
        || trimmed.starts_with("const ")
        || trimmed.starts_with("func ")
        || trimmed.starts_with("pred ")
        || trimmed.starts_with("defrec ")
        || trimmed.starts_with("def ")
        || trimmed.starts_with("axiom ")
}

fn parse_import_path(rest: &str) -> Result<String, ParseError> {
    let path = rest.trim();
    if path.is_empty() {
        return Err(ParseError::new("import declaration needs a path"));
    }

    if let Some(quoted) = path.strip_prefix('"') {
        let Some(quoted) = quoted.strip_suffix('"') else {
            return Err(ParseError::new("quoted import path must end with `\"`"));
        };
        if quoted.is_empty() {
            return Err(ParseError::new("import declaration needs a path"));
        }
        return Ok(quoted.to_string());
    }

    if path.contains(char::is_whitespace) {
        return Err(ParseError::new(
            "unquoted import paths cannot contain whitespace",
        ));
    }
    Ok(path.to_string())
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

fn parse_def_header(header: &str) -> Result<(Name, Vec<Param>, DefResult), ParseError> {
    let mut tokens = Tokens::new(header)?;
    tokens.expect_keyword("def")?;
    let name = tokens.expect_ident()?;
    let params = parse_decl_params(&mut tokens)?;
    tokens.expect_sym(":")?;
    let result = if tokens.eat_ident("Prop") {
        DefResult::Formula
    } else {
        DefResult::Term(tokens.parse_type()?)
    };
    tokens.expect_eof()?;
    Ok((name, params, result))
}

fn parse_defrec_header(header: &str) -> Result<(Name, Name, Type), ParseError> {
    let mut tokens = Tokens::new(header)?;
    tokens.expect_keyword("defrec")?;
    let name = tokens.expect_ident()?;
    tokens.expect_sym("(")?;
    let param = tokens.expect_ident()?;
    tokens.expect_sym(":")?;
    let param_type = tokens.parse_type()?;
    if param_type != Type::Nat {
        return Err(
            ParseError::new("recursive definition parameter must have type `Nat`")
                .with_span(tokens.current_span()),
        );
    }
    tokens.expect_sym(")")?;
    tokens.expect_sym(":")?;
    let result_type = tokens.parse_type()?;
    tokens.expect_eof()?;
    Ok((name, param, result_type))
}

fn parse_defrec_zero_arm(line: &str) -> Result<Term, ParseError> {
    let Some(body) = line.strip_prefix("| zero =>") else {
        return Err(ParseError::new(
            "recursive definition zero case expects `| zero => term`",
        ));
    };
    parse_term_str(body.trim())
}

fn parse_defrec_succ_arm(line: &str) -> Result<(Name, Name, Term), ParseError> {
    let Some(rest) = line.strip_prefix("| succ ") else {
        return Err(ParseError::new(
            "recursive definition successor case expects `| succ k rec => term`",
        ));
    };
    let Some((binders, body)) = rest.split_once("=>") else {
        return Err(ParseError::new(
            "recursive definition successor case expects `| succ k rec => term`",
        ));
    };
    let binders: Vec<&str> = binders.split_whitespace().collect();
    if binders.len() != 2 {
        return Err(ParseError::new(
            "recursive definition successor case expects exactly two binders",
        ));
    }
    if binders[0] == binders[1] {
        return Err(ParseError::new(
            "recursive definition successor case binders must be distinct",
        ));
    }
    Ok((
        binders[0].to_string(),
        binders[1].to_string(),
        parse_term_str(body.trim())?,
    ))
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

fn parse_tactic_lines(lines: &[RawTacticLine]) -> Result<Vec<LocatedTactic>, ParseError> {
    let mut tactics = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let line_no = lines[i].line;
        let trimmed = lines[i].text.trim();
        if trimmed.is_empty() {
            i += 1;
            continue;
        }
        if trimmed.starts_with('|') {
            return Err(ParseError::new("case arm appeared outside `cases`").with_line(line_no));
        }

        if let Some(expr) = trimmed
            .strip_prefix("cases ")
            .and_then(|rest| rest.strip_suffix(" with"))
        {
            i += 1;
            i = skip_empty_tactic_lines(lines, i);
            if i >= lines.len() {
                return Err(ParseError::new("expected case arm").with_line(line_no));
            }

            if lines[i].text.trim().starts_with("| intro ") {
                let arm_line = lines[i].line;
                let arm_indent = line_indent(&lines[i].text);
                let (witness_name, hyp_name) = parse_exists_case_arm(lines[i].text.trim())
                    .map_err(|err| err.with_line(arm_line))?;
                i += 1;
                let body_end = case_body_end(lines, i, arm_indent);
                let body_tactics = parse_tactic_lines(&lines[i..body_end])?;
                i = body_end;

                tactics.push(LocatedTactic {
                    line: line_no,
                    tactic: Tactic::CasesExists {
                        expr: parse_proof_expr(expr.trim())
                            .map_err(|err| err.with_line(line_no))?,
                        witness_name,
                        hyp_name,
                        body_tactics,
                    },
                });
                continue;
            }

            let left_line = lines[i].line;
            let left_indent = line_indent(&lines[i].text);
            let left_name = parse_case_arm(lines[i].text.trim(), "left")
                .map_err(|err| err.with_line(left_line))?;
            i += 1;
            let left_start = i;
            let left_end = case_body_end(lines, i, left_indent);
            i = skip_empty_tactic_lines(lines, left_end);
            if i >= lines.len() {
                return Err(ParseError::new("expected right case arm").with_line(left_line));
            }
            let left_tactics = parse_tactic_lines(&lines[left_start..left_end])?;

            let right_line = lines[i].line;
            let right_indent = line_indent(&lines[i].text);
            let right_name = parse_case_arm(lines[i].text.trim(), "right")
                .map_err(|err| err.with_line(right_line))?;
            i += 1;
            let right_start = i;
            let right_end = case_body_end(lines, i, right_indent);
            let right_tactics = parse_tactic_lines(&lines[right_start..right_end])?;
            i = right_end;

            tactics.push(LocatedTactic {
                line: line_no,
                tactic: Tactic::CasesOr {
                    expr: parse_proof_expr(expr.trim()).map_err(|err| err.with_line(line_no))?,
                    left_name,
                    left_tactics,
                    right_name,
                    right_tactics,
                },
            });
            continue;
        }

        if let Some(var_name) = trimmed
            .strip_prefix("induction ")
            .and_then(|rest| rest.strip_suffix(" with"))
        {
            i += 1;
            i = skip_empty_tactic_lines(lines, i);
            if i >= lines.len() {
                return Err(ParseError::new("expected zero case arm").with_line(line_no));
            }
            let zero_line = lines[i].line;
            let zero_indent = line_indent(&lines[i].text);
            parse_zero_case_arm(lines[i].text.trim()).map_err(|err| err.with_line(zero_line))?;
            i += 1;
            let zero_start = i;
            let zero_end = case_body_end(lines, i, zero_indent);
            i = skip_empty_tactic_lines(lines, zero_end);
            if i >= lines.len() {
                return Err(ParseError::new("expected successor case arm").with_line(zero_line));
            }
            let zero_tactics = parse_tactic_lines(&lines[zero_start..zero_end])?;
            let step_line = lines[i].line;
            let step_indent = line_indent(&lines[i].text);
            let (step_var, ih_name) = parse_succ_case_arm(lines[i].text.trim())
                .map_err(|err| err.with_line(step_line))?;
            i += 1;
            let step_start = i;
            let step_end = case_body_end(lines, i, step_indent);
            let step_tactics = parse_tactic_lines(&lines[step_start..step_end])?;
            i = step_end;

            tactics.push(LocatedTactic {
                line: line_no,
                tactic: Tactic::Induction {
                    var_name: expect_single_name(var_name, "induction")
                        .map_err(|err| err.with_line(line_no))?,
                    zero_tactics,
                    step_var,
                    ih_name,
                    step_tactics,
                },
            });
            continue;
        }

        let offset = lines[i].text.find(trimmed).unwrap_or(0);
        tactics.push(LocatedTactic {
            line: line_no,
            tactic: parse_tactic_line(trimmed)
                .map_err(|err| err.with_offset(offset).with_line(line_no))?,
        });
        i += 1;
    }

    Ok(tactics)
}

fn skip_empty_tactic_lines(lines: &[RawTacticLine], mut i: usize) -> usize {
    while i < lines.len() && lines[i].text.trim().is_empty() {
        i += 1;
    }
    i
}

fn case_body_end(lines: &[RawTacticLine], mut i: usize, arm_indent: usize) -> usize {
    while i < lines.len() {
        let trimmed = lines[i].text.trim();
        if !trimmed.is_empty() && line_indent(&lines[i].text) <= arm_indent {
            break;
        }
        i += 1;
    }
    i
}

fn line_indent(line: &str) -> usize {
    line.chars().take_while(|ch| ch.is_whitespace()).count()
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
        let expr = rest.trim();
        let offset = line.find(expr).unwrap_or(0);
        return Ok(Tactic::Exact(
            parse_proof_expr(expr).map_err(|err| err.with_offset(offset))?,
        ));
    }
    if line == "trivial" {
        return Ok(Tactic::Trivial);
    }
    if line == "assumption" {
        return Ok(Tactic::Assumption);
    }
    if let Some(rest) = line.strip_prefix("apply ") {
        let expr = rest.trim();
        let offset = line.find(expr).unwrap_or(0);
        return Ok(Tactic::Apply(
            parse_proof_expr(expr).map_err(|err| err.with_offset(offset))?,
        ));
    }
    if let Some(rest) = line.strip_prefix("exists ") {
        let term = rest.trim();
        let offset = line.find(term).unwrap_or(0);
        return Ok(Tactic::Exists(
            parse_term_str(term).map_err(|err| err.with_offset(offset))?,
        ));
    }
    if line == "refl" {
        return Ok(Tactic::Refl);
    }
    if let Some(rest) = line.strip_prefix("rewrite ") {
        let rest = rest.trim();
        let (direction, expr) = if let Some(expr) = rest.strip_prefix("->") {
            (RewriteDirection::Forward, expr.trim())
        } else if let Some(expr) = rest.strip_prefix("<-") {
            (RewriteDirection::Backward, expr.trim())
        } else {
            (RewriteDirection::Backward, rest)
        };
        return Ok(Tactic::Rewrite {
            expr: parse_proof_expr(expr)
                .map_err(|err| err.with_offset(line.find(expr).unwrap_or(0)))?,
            direction,
        });
    }
    if let Some(rest) = line.strip_prefix("unfold ") {
        return Ok(Tactic::Unfold(expect_single_name(rest, "unfold")?));
    }
    if line == "simp" {
        return Ok(Tactic::Simp);
    }
    if line == "simp at *" {
        return Ok(Tactic::SimpAll);
    }
    if let Some(rest) = line.strip_prefix("simp at ") {
        return Ok(Tactic::SimpAt(expect_single_name(rest, "simp at")?));
    }
    if let Some(rest) = line.strip_prefix("simp ") {
        return Ok(Tactic::SimpWith(parse_simp_rule_names(rest.trim())?));
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
            formula: {
                let formula = formula.trim();
                parse_formula_str(formula)
                    .map_err(|err| err.with_offset(line.find(formula).unwrap_or(0)))?
            },
        });
    }
    if let Some(rest) = line.strip_prefix("by_contra ") {
        return Ok(Tactic::ByContra(expect_single_name(rest, "by_contra")?));
    }
    if line == "show_goal" || line == "print_state" {
        return Ok(Tactic::ShowGoal);
    }

    Err(ParseError::new(format!("unknown tactic `{line}`")))
}

fn parse_simp_rule_names(input: &str) -> Result<Vec<Name>, ParseError> {
    let Some(body) = input
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
    else {
        return Err(ParseError::new("simp theorem rules use `[name, ...]`"));
    };
    let mut names = Vec::new();
    for item in body.split(',') {
        let name = item.trim();
        if name.is_empty() {
            return Err(ParseError::new("empty simp theorem name"));
        }
        names.push(name.to_string());
    }
    Ok(names)
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
        steps.push(ProofStep::Arg(word.to_string()));
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
    target: Option<Formula>,
    line: Option<usize>,
}

impl TacticError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            target: None,
            line: None,
        }
    }

    fn with_target(mut self, target: Formula) -> Self {
        if self.target.is_none() {
            self.target = Some(target);
        }
        self
    }

    fn with_line(mut self, line: usize) -> Self {
        if self.line.is_none() {
            self.line = Some(line);
        }
        self
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
    tactics: &[LocatedTactic],
    allowed_mode: LogicMode,
) -> Result<Proof, TacticError> {
    let mut root = PartialProof::Hole(0);
    let mut goals = vec![Goal {
        id: 0,
        context,
        target,
    }];
    let mut next_goal_id = 1;

    for located in tactics {
        if goals.is_empty() {
            return Err(
                TacticError::new("tactic was provided after all goals were solved")
                    .with_line(located.line),
            );
        }

        let goal = goals.remove(0);
        let goal_id = goal.id;
        let goal_target = goal.target.clone();
        let tactic = &located.tactic;
        let StepResult {
            replacement,
            new_goals,
        } = run_tactic(env, goal, tactic, allowed_mode, &mut next_goal_id)
            .map_err(|err| err.with_target(goal_target).with_line(located.line))?;
        if !root.replace_hole(goal_id, &replacement) {
            return Err(TacticError::new("internal error: missing proof hole"));
        }
        for new_goal in new_goals.into_iter().rev() {
            goals.insert(0, new_goal);
        }
    }

    if let Some(goal) = goals.first() {
        return Err(TacticError::new(format!("unsolved goal `{}`", goal.target))
            .with_target(goal.target.clone()));
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
                ensure_intro_name_unused(&goal.context, name)?;
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
                ensure_intro_name_unused(&goal.context, name)?;
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
            let proof =
                proof_expr_for_expected(env, &goal.context, expr, &goal.target, allowed_mode)?;
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
        Tactic::Trivial => {
            if !formulas_def_eq(env, &goal.context, &goal.target, &Formula::True)
                .map_err(|err| TacticError::new(err.message))?
            {
                return Err(TacticError::new(format!(
                    "trivial expects a `True` goal, but target is `{}`",
                    goal.target
                )));
            }
            Ok(StepResult {
                replacement: PartialProof::Done(Proof::TrueIntro),
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
            let proof_or = proof_expr_for_inferred(env, &goal.context, expr, allowed_mode)?;
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
            let proof_exists = proof_expr_for_inferred(env, &goal.context, expr, allowed_mode)?;
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
        Tactic::Rewrite { expr, direction } => {
            let eq_proof = proof_expr_for_inferred(env, &goal.context, expr, allowed_mode)?;
            let checked = infer_proof(env, &goal.context, &eq_proof, allowed_mode)
                .map_err(|err| TacticError::new(format!("cannot rewrite: {}", err.message)))?;
            let formula = normalize_formula_defs(env, &goal.context, &checked.formula)
                .map_err(|err| TacticError::new(err.message))?;
            let Formula::Eq(left, right) = formula else {
                return Err(TacticError::new("rewrite expects an equality proof"));
            };
            let (needle, replacement) = match direction {
                RewriteDirection::Backward => (&right, &left),
                RewriteDirection::Forward => (&left, &right),
            };
            let Some(source_target) = formula_rewrite_sources(&goal.target, needle, replacement)
                .into_iter()
                .min_by_key(rewrite_source_score)
            else {
                return Err(TacticError::new(format!(
                    "rewrite could not find `{needle}` in goal `{}`",
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
        Tactic::SimpWith(names) => {
            let rules = collect_simp_rules(env, names)?;
            let (builtin_target, builtin_changed) =
                unfold_formula_defs(env, &goal.context, &goal.target, None)
                    .map_err(|err| TacticError::new(format!("cannot simplify: {}", err.message)))?;
            let (target, rewrites) =
                rewrite_with_simp_rules(env, &goal.context, builtin_target, &rules)?;
            if !builtin_changed && rewrites.is_empty() {
                return Err(TacticError::new(format!(
                    "simp made no progress on goal `{}`",
                    goal.target
                )));
            }
            let id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: build_simp_replacement(
                    id,
                    goal.target.clone(),
                    builtin_changed,
                    &rewrites,
                ),
                new_goals: vec![Goal {
                    id,
                    context: goal.context,
                    target,
                }],
            })
        }
        Tactic::SimpAt(name) => {
            let Some(formula) = goal.context.lookup(name).cloned() else {
                return Err(TacticError::new(format!("unknown hypothesis `{name}`")));
            };
            let (formula, changed) = unfold_formula_defs(env, &goal.context, &formula, None)
                .map_err(|err| {
                    TacticError::new(format!("cannot simplify `{name}`: {}", err.message))
                })?;
            if !changed {
                return Err(TacticError::new(format!(
                    "simp made no progress on hypothesis `{name}`"
                )));
            }
            let mut context = goal.context;
            context.add_proof(name.clone(), formula);
            let id = fresh_goal(next_goal_id);
            Ok(StepResult {
                replacement: PartialProof::Hole(id),
                new_goals: vec![Goal {
                    id,
                    context,
                    target: goal.target,
                }],
            })
        }
        Tactic::SimpAll => {
            let (context, hypotheses_changed) = simplify_hypotheses(env, &goal.context)?;
            let (target, target_changed) = unfold_formula_defs(env, &context, &goal.target, None)
                .map_err(|err| {
                TacticError::new(format!("cannot simplify goal: {}", err.message))
            })?;
            if !hypotheses_changed && !target_changed {
                return Err(TacticError::new(format!(
                    "simp made no progress on goal or hypotheses for `{}`",
                    goal.target
                )));
            }
            let id = fresh_goal(next_goal_id);
            let replacement = if target_changed {
                PartialProof::Convert {
                    proof_body: Box::new(PartialProof::Hole(id)),
                    target: goal.target,
                }
            } else {
                PartialProof::Hole(id)
            };
            Ok(StepResult {
                replacement,
                new_goals: vec![Goal {
                    id,
                    context,
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
        Tactic::ShowGoal => Err(TacticError::new(format!(
            "current goal is `{}`",
            goal.target
        ))),
    }
}

fn ensure_intro_name_unused(ctx: &Context, name: &str) -> Result<(), TacticError> {
    if ctx.lookup(name).is_some() {
        return Err(TacticError::new(format!(
            "`intro` would shadow existing hypothesis `{name}`"
        )));
    }
    if ctx.lookup_term(name).is_some() {
        return Err(TacticError::new(format!(
            "`intro` would shadow existing variable `{name}`"
        )));
    }
    Ok(())
}

#[derive(Clone)]
struct SimpRule {
    theorem_name: Name,
    params: Vec<Param>,
    lhs: Term,
    rhs: Term,
}

#[derive(Clone)]
struct SimpRewrite {
    before: Formula,
    eq_proof: Proof,
}

fn collect_simp_rules(env: &Env, names: &[Name]) -> Result<Vec<SimpRule>, TacticError> {
    let mut rules = Vec::new();
    for name in names {
        let Some(theorem) = env.theorem(name) else {
            return Err(TacticError::new(format!("unknown theorem `{name}`")));
        };
        let Formula::Eq(lhs, rhs) = &theorem.statement else {
            return Err(TacticError::new(format!(
                "simp rule `{name}` must prove a term equality"
            )));
        };
        rules.push(SimpRule {
            theorem_name: name.clone(),
            params: theorem.params.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        });
    }
    Ok(rules)
}

fn build_simp_replacement(
    id: usize,
    original_target: Formula,
    builtin_changed: bool,
    rewrites: &[SimpRewrite],
) -> PartialProof {
    let mut replacement = PartialProof::Hole(id);
    for rewrite in rewrites.iter().rev() {
        replacement = PartialProof::EqSubst {
            eq_proof: Box::new(PartialProof::Done(rewrite.eq_proof.clone())),
            proof_body: Box::new(replacement),
            target: rewrite.before.clone(),
        };
    }
    if builtin_changed {
        PartialProof::Convert {
            proof_body: Box::new(replacement),
            target: original_target,
        }
    } else {
        replacement
    }
}

fn rewrite_with_simp_rules(
    env: &Env,
    ctx: &Context,
    mut formula: Formula,
    rules: &[SimpRule],
) -> Result<(Formula, Vec<SimpRewrite>), TacticError> {
    let mut rewrites = Vec::new();
    for _ in 0..32 {
        let Some((next, eq_proof)) =
            rewrite_formula_with_simp_rules_once(env, ctx, &formula, rules)?
        else {
            break;
        };
        let before = formula;
        formula = next;
        rewrites.push(SimpRewrite { before, eq_proof });
    }
    Ok((formula, rewrites))
}

fn rewrite_formula_with_simp_rules_once(
    env: &Env,
    ctx: &Context,
    formula: &Formula,
    rules: &[SimpRule],
) -> Result<Option<(Formula, Proof)>, TacticError> {
    match formula {
        Formula::True | Formula::False | Formula::Atom(_) => Ok(None),
        Formula::Eq(left, right) => {
            rewrite_binary_term_with_simp_rules(env, ctx, left, right, rules, Formula::eq)
        }
        Formula::In(left, right) => {
            rewrite_binary_term_with_simp_rules(env, ctx, left, right, rules, Formula::membership)
        }
        Formula::Subset(left, right) => {
            rewrite_binary_term_with_simp_rules(env, ctx, left, right, rules, Formula::subset)
        }
        Formula::PredApp(name, args) => {
            for (idx, arg) in args.iter().enumerate() {
                if let Some((rewritten, proof)) =
                    rewrite_term_with_simp_rules_once(env, ctx, arg, rules)?
                {
                    let mut args = args.clone();
                    args[idx] = rewritten;
                    return Ok(Some((Formula::PredApp(name.clone(), args), proof)));
                }
            }
            Ok(None)
        }
        Formula::And(left, right) => {
            rewrite_binary_formula_with_simp_rules(env, ctx, left, right, rules, Formula::and)
        }
        Formula::Or(left, right) => {
            rewrite_binary_formula_with_simp_rules(env, ctx, left, right, rules, Formula::or)
        }
        Formula::Implies(left, right) => {
            rewrite_binary_formula_with_simp_rules(env, ctx, left, right, rules, Formula::implies)
        }
        Formula::Forall {
            var,
            var_type,
            body,
        } => {
            if let Some((body, proof)) =
                rewrite_formula_with_simp_rules_once(env, ctx, body, rules)?
            {
                Ok(Some((
                    Formula::forall(var.clone(), var_type.clone(), body),
                    proof,
                )))
            } else {
                Ok(None)
            }
        }
        Formula::Exists {
            var,
            var_type,
            body,
        } => {
            if let Some((body, proof)) =
                rewrite_formula_with_simp_rules_once(env, ctx, body, rules)?
            {
                Ok(Some((
                    Formula::exists(var.clone(), var_type.clone(), body),
                    proof,
                )))
            } else {
                Ok(None)
            }
        }
    }
}

fn rewrite_binary_formula_with_simp_rules(
    env: &Env,
    ctx: &Context,
    left: &Formula,
    right: &Formula,
    rules: &[SimpRule],
    rebuild: fn(Formula, Formula) -> Formula,
) -> Result<Option<(Formula, Proof)>, TacticError> {
    if let Some((new_left, proof)) = rewrite_formula_with_simp_rules_once(env, ctx, left, rules)? {
        return Ok(Some((rebuild(new_left, right.clone()), proof)));
    }
    if let Some((new_right, proof)) = rewrite_formula_with_simp_rules_once(env, ctx, right, rules)?
    {
        return Ok(Some((rebuild(left.clone(), new_right), proof)));
    }
    Ok(None)
}

fn rewrite_binary_term_with_simp_rules(
    env: &Env,
    ctx: &Context,
    left: &Term,
    right: &Term,
    rules: &[SimpRule],
    rebuild: fn(Term, Term) -> Formula,
) -> Result<Option<(Formula, Proof)>, TacticError> {
    if let Some((new_left, proof)) = rewrite_term_with_simp_rules_once(env, ctx, left, rules)? {
        return Ok(Some((rebuild(new_left, right.clone()), proof)));
    }
    if let Some((new_right, proof)) = rewrite_term_with_simp_rules_once(env, ctx, right, rules)? {
        return Ok(Some((rebuild(left.clone(), new_right), proof)));
    }
    Ok(None)
}

fn rewrite_term_with_simp_rules_once(
    env: &Env,
    ctx: &Context,
    term: &Term,
    rules: &[SimpRule],
) -> Result<Option<(Term, Proof)>, TacticError> {
    for rule in rules {
        if let Some((term, proof)) = apply_simp_rule_to_term(env, ctx, term, rule)? {
            return Ok(Some((term, proof)));
        }
    }

    match term {
        Term::App(name, args) => {
            for (idx, arg) in args.iter().enumerate() {
                if let Some((rewritten, proof)) =
                    rewrite_term_with_simp_rules_once(env, ctx, arg, rules)?
                {
                    let mut args = args.clone();
                    args[idx] = rewritten;
                    return Ok(Some((Term::App(name.clone(), args), proof)));
                }
            }
            Ok(None)
        }
        Term::Succ(inner) => rewrite_unary_term_with_simp_rules(env, ctx, inner, rules, |inner| {
            Term::Succ(Box::new(inner))
        }),
        Term::Singleton(inner) => {
            rewrite_unary_term_with_simp_rules(env, ctx, inner, rules, |inner| {
                Term::Singleton(Box::new(inner))
            })
        }
        Term::Powerset(inner) => {
            rewrite_unary_term_with_simp_rules(env, ctx, inner, rules, |inner| {
                Term::Powerset(Box::new(inner))
            })
        }
        Term::Add(left, right) => {
            rewrite_binary_term_node_with_simp_rules(env, ctx, left, right, rules, |left, right| {
                Term::Add(Box::new(left), Box::new(right))
            })
        }
        Term::Mul(left, right) => {
            rewrite_binary_term_node_with_simp_rules(env, ctx, left, right, rules, |left, right| {
                Term::Mul(Box::new(left), Box::new(right))
            })
        }
        Term::Sub(left, right) => {
            rewrite_binary_term_node_with_simp_rules(env, ctx, left, right, rules, |left, right| {
                Term::Sub(Box::new(left), Box::new(right))
            })
        }
        Term::Union(left, right) => {
            rewrite_binary_term_node_with_simp_rules(env, ctx, left, right, rules, |left, right| {
                Term::Union(Box::new(left), Box::new(right))
            })
        }
        Term::Inter(left, right) => {
            rewrite_binary_term_node_with_simp_rules(env, ctx, left, right, rules, |left, right| {
                Term::Inter(Box::new(left), Box::new(right))
            })
        }
        Term::Diff(left, right) => {
            rewrite_binary_term_node_with_simp_rules(env, ctx, left, right, rules, |left, right| {
                Term::Diff(Box::new(left), Box::new(right))
            })
        }
        Term::SetBuilder {
            var,
            var_type,
            body,
        } => {
            if let Some((body, proof)) =
                rewrite_formula_with_simp_rules_once(env, ctx, body, rules)?
            {
                Ok(Some((
                    Term::SetBuilder {
                        var: var.clone(),
                        var_type: var_type.clone(),
                        body: Box::new(body),
                    },
                    proof,
                )))
            } else {
                Ok(None)
            }
        }
        Term::PredLambda { params, body } => {
            if let Some((body, proof)) =
                rewrite_formula_with_simp_rules_once(env, ctx, body, rules)?
            {
                Ok(Some((
                    Term::PredLambda {
                        params: params.clone(),
                        body: Box::new(body),
                    },
                    proof,
                )))
            } else {
                Ok(None)
            }
        }
        Term::Var(_) | Term::Zero | Term::EmptySet(_) => Ok(None),
    }
}

fn apply_simp_rule_to_term(
    env: &Env,
    ctx: &Context,
    term: &Term,
    rule: &SimpRule,
) -> Result<Option<(Term, Proof)>, TacticError> {
    let mut term_subst = HashMap::new();
    let mut schema_subst = SchemaSubst::default();
    {
        let mut unify = UnifyState {
            env,
            ctx,
            term_metas: &[],
            schema_params: &rule.params,
            term_subst: &mut term_subst,
            schema_subst: &mut schema_subst,
        };
        if unify_term(&rule.lhs, term, &mut unify).is_err() {
            return Ok(None);
        }
    }
    if ensure_schema_subst_complete(&rule.params, &schema_subst, Some(&rule.theorem_name)).is_err()
    {
        return Ok(None);
    }
    let replacement = subst_term_schema(&rule.rhs, &schema_subst);
    if &replacement == term {
        return Ok(None);
    }
    Ok(Some((
        replacement,
        Proof::TheoremRef {
            name: rule.theorem_name.clone(),
            subst: schema_subst,
        },
    )))
}

fn rewrite_unary_term_with_simp_rules(
    env: &Env,
    ctx: &Context,
    inner: &Term,
    rules: &[SimpRule],
    rebuild: fn(Term) -> Term,
) -> Result<Option<(Term, Proof)>, TacticError> {
    if let Some((inner, proof)) = rewrite_term_with_simp_rules_once(env, ctx, inner, rules)? {
        Ok(Some((rebuild(inner), proof)))
    } else {
        Ok(None)
    }
}

fn rewrite_binary_term_node_with_simp_rules(
    env: &Env,
    ctx: &Context,
    left: &Term,
    right: &Term,
    rules: &[SimpRule],
    rebuild: fn(Term, Term) -> Term,
) -> Result<Option<(Term, Proof)>, TacticError> {
    if let Some((left, proof)) = rewrite_term_with_simp_rules_once(env, ctx, left, rules)? {
        return Ok(Some((rebuild(left, right.clone()), proof)));
    }
    if let Some((right, proof)) = rewrite_term_with_simp_rules_once(env, ctx, right, rules)? {
        return Ok(Some((rebuild(left.clone(), right), proof)));
    }
    Ok(None)
}

fn simplify_hypotheses(env: &Env, ctx: &Context) -> Result<(Context, bool), TacticError> {
    let mut context = ctx.clone();
    let mut changed = false;
    for binding in ctx.proofs() {
        let (formula, binding_changed) = unfold_formula_defs(env, ctx, &binding.formula, None)
            .map_err(|err| {
                TacticError::new(format!(
                    "cannot simplify `{}`: {}",
                    binding.name, err.message
                ))
            })?;
        if binding_changed {
            context.add_proof(binding.name.clone(), formula);
            changed = true;
        }
    }
    Ok((context, changed))
}

fn proof_expr_for_inferred(
    env: &Env,
    ctx: &Context,
    expr: &ProofExpr,
    allowed_mode: LogicMode,
) -> Result<Proof, TacticError> {
    if expr.is_true_intro() {
        return Ok(Proof::TrueIntro);
    }

    if expr.is_bare_theorem_ref(env, ctx) {
        let theorem = env
            .theorem(&expr.base)
            .ok_or_else(|| TacticError::new(format!("unknown theorem `{}`", expr.base)))?;
        let subst = explicit_schema_subst(env, ctx, theorem, &expr.explicit_args)?;
        ensure_schema_subst_complete(&theorem.params, &subst, Some(theorem.name.as_str()))?;
        return Ok(Proof::TheoremRef {
            name: expr.base.clone(),
            subst,
        });
    }

    expr.to_proof(env, ctx, allowed_mode)
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
            let available = theorem_schema_arg_list(theorem);
            return Err(TacticError::new(format!(
                "theorem `{}` has no schema argument `{}`; available schema arguments: {}",
                theorem.name, arg.name, available
            )));
        };

        match &param.kind {
            ParamKind::Type => {
                let ty = parse_type_str(&arg.value)
                    .map_err(|err| explicit_schema_arg_error(theorem, arg, err.message))?;
                validate_type(env, ctx, &ty)
                    .map_err(|err| explicit_schema_arg_error(theorem, arg, err.message))?;
                subst.type_args.insert(arg.name.clone(), ty);
            }
            ParamKind::Prop => {
                let formula = parse_formula_str(&arg.value)
                    .map_err(|err| explicit_schema_arg_error(theorem, arg, err.message))?;
                validate_formula(env, ctx, &formula)
                    .map_err(|err| explicit_schema_arg_error(theorem, arg, err.message))?;
                subst.formula_args.insert(arg.name.clone(), formula);
            }
            ParamKind::Predicate(_) => {
                let pred_arg = parse_predicate_arg(&arg.value)
                    .map_err(|err| explicit_schema_arg_error(theorem, arg, err.message))?;
                subst.predicate_args.insert(arg.name.clone(), pred_arg);
            }
            ParamKind::Term(_) => {
                let term = parse_term_str(&arg.value)
                    .map_err(|err| explicit_schema_arg_error(theorem, arg, err.message))?;
                validate_term(env, ctx, &term)
                    .map_err(|err| explicit_schema_arg_error(theorem, arg, err.message))?;
                subst.term_args.insert(arg.name.clone(), term);
            }
        }
    }

    Ok(subst)
}

fn theorem_schema_arg_list(theorem: &Theorem) -> String {
    if theorem.params.is_empty() {
        "none".to_string()
    } else {
        theorem
            .params
            .iter()
            .map(|param| format!("`{}`", param.name))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn explicit_schema_arg_error(
    theorem: &Theorem,
    arg: &ExplicitArg,
    message: impl Into<String>,
) -> TacticError {
    TacticError::new(format!(
        "invalid value for schema argument `{}` of theorem `{}`: {}",
        arg.name,
        theorem.name,
        message.into()
    ))
}

fn parse_predicate_arg(input: &str) -> Result<PredicateArg, TacticError> {
    let input = input.trim();
    if input.is_empty() {
        return Err(TacticError::new("predicate argument cannot be empty"));
    }
    if let Ok(term) = parse_term_str(input) {
        return formula_def_predicate_argument(&term).map_err(|err| TacticError::new(err.message));
    }
    if input.chars().enumerate().all(|(idx, ch)| {
        if idx == 0 {
            ch.is_ascii_alphabetic() || ch == '_'
        } else {
            ch.is_ascii_alphanumeric() || ch == '_'
        }
    }) {
        Ok(PredicateArg::Named(input.to_string()))
    } else {
        Err(TacticError::new(format!(
            "predicate argument `{input}` must be a predicate name or lambda"
        )))
    }
}

fn proof_expr_for_expected(
    env: &Env,
    ctx: &Context,
    expr: &ProofExpr,
    expected: &Formula,
    allowed_mode: LogicMode,
) -> Result<Proof, TacticError> {
    if expr.is_true_intro() {
        return Ok(Proof::TrueIntro);
    }

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
            Some(theorem.name.as_str()),
        )?;
        return Ok(Proof::TheoremRef {
            name: expr.base.clone(),
            subst,
        });
    }

    expr.to_proof(env, ctx, allowed_mode)
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
            Some(theorem.name.as_str()),
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

    let proof = expr.to_proof(env, ctx, allowed_mode)?;
    let checked = infer_proof(env, ctx, &proof, allowed_mode)
        .map_err(|err| TacticError::new(format!("cannot apply expression: {}", err.message)))?;
    let plan = apply_plan_for_goal(
        env,
        ctx,
        &checked.formula,
        target,
        &[],
        SchemaSubst::default(),
        None,
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
    theorem_name: Option<&str>,
) -> Result<ApplyPlan, TacticError> {
    let schema_ctx;
    let formula_ctx = if schema_params.is_empty() {
        ctx
    } else {
        schema_ctx = build_theorem_context(env, schema_params)
            .map_err(|err| TacticError::new(err.message))?;
        &schema_ctx
    };
    let normalized_formula = normalize_formula_defs(env, formula_ctx, formula)
        .map_err(|err| TacticError::new(err.message))?;
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
    infer_apply_args_from_context(
        env,
        ctx,
        &premises,
        schema_params,
        &quantified,
        &mut term_subst,
        &mut schema_subst,
    )?;
    ensure_schema_subst_complete(schema_params, &schema_subst, theorem_name)?;

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

fn infer_apply_args_from_context(
    env: &Env,
    ctx: &Context,
    premises: &[Formula],
    schema_params: &[Param],
    term_metas: &[Name],
    term_subst: &mut HashMap<Name, Term>,
    schema_subst: &mut SchemaSubst,
) -> Result<(), TacticError> {
    if premises.is_empty() || ctx.proofs().is_empty() {
        return Ok(());
    }

    let mut normalized_hypotheses = Vec::new();
    for binding in ctx.proofs() {
        let formula = normalize_formula_defs(env, ctx, &binding.formula)
            .map_err(|err| TacticError::new(err.message))?;
        normalized_hypotheses.push(formula);
    }

    for premise in premises {
        for hypothesis in normalized_hypotheses.iter().rev() {
            let mut candidate_term_subst = term_subst.clone();
            let mut candidate_schema_subst = schema_subst.clone();
            let mut unify = UnifyState {
                env,
                ctx,
                term_metas,
                schema_params,
                term_subst: &mut candidate_term_subst,
                schema_subst: &mut candidate_schema_subst,
            };
            if unify_formula(premise, hypothesis, &mut unify).is_ok() {
                *term_subst = candidate_term_subst;
                *schema_subst = candidate_schema_subst;
                break;
            }
        }
    }

    Ok(())
}

fn infer_schema_subst_for_formula(
    env: &Env,
    ctx: &Context,
    params: &[Param],
    pattern: &Formula,
    target: &Formula,
    initial_schema_subst: SchemaSubst,
    theorem_name: Option<&str>,
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
    ensure_schema_subst_complete(params, &schema_subst, theorem_name)?;
    Ok(schema_subst)
}

fn ensure_schema_subst_complete(
    params: &[Param],
    subst: &SchemaSubst,
    theorem_name: Option<&str>,
) -> Result<(), TacticError> {
    for param in params {
        let complete = match &param.kind {
            ParamKind::Type => subst.type_args.contains_key(&param.name),
            ParamKind::Prop => subst.formula_args.contains_key(&param.name),
            ParamKind::Predicate(_) => subst.predicate_args.contains_key(&param.name),
            ParamKind::Term(_) => subst.term_args.contains_key(&param.name),
        };
        if !complete {
            let kind = schema_param_description(param);
            let theorem = theorem_name
                .map(|name| format!(" for theorem `{name}`"))
                .unwrap_or_default();
            return Err(TacticError::new(format!(
                "cannot infer schema argument `{}`{theorem} ({kind}); provide it explicitly with `{{{} := ...}}`",
                param.name, param.name
            )));
        }
    }
    Ok(())
}

fn schema_param_description(param: &Param) -> String {
    match &param.kind {
        ParamKind::Type => "type parameter".to_string(),
        ParamKind::Prop => "proposition parameter".to_string(),
        ParamKind::Predicate(args) => {
            let mut parts = args.iter().map(ToString::to_string).collect::<Vec<_>>();
            parts.push("Prop".to_string());
            format!("predicate parameter of type `{}`", parts.join(" -> "))
        }
        ParamKind::Term(ty) => format!("term parameter of type `{ty}`"),
    }
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
        Term::PredLambda { params, body } => {
            let mut scoped = subst.clone();
            for param in params {
                scoped.remove(&param.name);
            }
            Term::PredLambda {
                params: params.clone(),
                body: Box::new(subst_formula_terms(body, &scoped)),
            }
        }
        Term::Zero => Term::Zero,
        Term::Succ(term) => Term::Succ(Box::new(subst_term_terms(term, subst))),
        Term::Add(left, right) => Term::Add(
            Box::new(subst_term_terms(left, subst)),
            Box::new(subst_term_terms(right, subst)),
        ),
        Term::Mul(left, right) => Term::Mul(
            Box::new(subst_term_terms(left, subst)),
            Box::new(subst_term_terms(right, subst)),
        ),
        Term::Sub(left, right) => Term::Sub(
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
        Term::Powerset(term) => Term::Powerset(Box::new(subst_term_terms(term, subst))),
        Term::SetBuilder {
            var,
            var_type,
            body,
        } => {
            let mut scoped = subst.clone();
            scoped.remove(var);
            Term::SetBuilder {
                var: var.clone(),
                var_type: var_type.clone(),
                body: Box::new(subst_formula_terms(body, &scoped)),
            }
        }
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
        Term::PredLambda {
            params: p_params,
            body: p_body,
        } => {
            let Term::PredLambda {
                params: t_params,
                body: t_body,
            } = target
            else {
                return Err(());
            };
            if p_params.len() != t_params.len()
                || p_params
                    .iter()
                    .zip(t_params)
                    .any(|(left, right)| left.ty != right.ty)
            {
                return Err(());
            }
            let mut renamed = *t_body.clone();
            for (p_param, t_param) in p_params.iter().zip(t_params) {
                renamed =
                    subst_formula_term(&renamed, &t_param.name, &Term::Var(p_param.name.clone()));
            }
            unify_formula(p_body, &renamed, unify)
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
        Term::Mul(p_left, p_right) => {
            let Term::Mul(t_left, t_right) = target else {
                return Err(());
            };
            unify_term(p_left, t_left, unify)?;
            unify_term(p_right, t_right, unify)
        }
        Term::Sub(p_left, p_right) => {
            let Term::Sub(t_left, t_right) = target else {
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
        Term::Powerset(pattern) => {
            let Term::Powerset(target) = target else {
                return Err(());
            };
            unify_term(pattern, target, unify)
        }
        Term::SetBuilder {
            var: p_var,
            var_type: p_ty,
            body: p_body,
        } => {
            let Term::SetBuilder {
                var: t_var,
                var_type: t_ty,
                body: t_body,
            } = target
            else {
                return Err(());
            };
            let renamed = subst_formula_term(t_body, t_var, &Term::Var(p_var.clone()));
            unify_type(p_ty, t_ty, unify.schema_params, unify.schema_subst)?;
            unify_formula(p_body, &renamed, unify)
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
        match existing {
            PredicateArg::Named(existing) if existing == target_name => {}
            _ => return Err(()),
        }
    } else {
        schema_subst.predicate_args.insert(
            name.to_string(),
            PredicateArg::Named(target_name.to_string()),
        );
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
    use std::path::Path;

    fn check_ok(source: &str) -> CheckResult {
        let result = check_file(source);
        assert!(
            result.diagnostics.is_empty(),
            "unexpected diagnostics: {:#?}",
            result.diagnostics
        );
        result
    }

    fn check_path_ok(relative_path: &str) -> CheckResult {
        let path = repo_path(relative_path);
        let result = check_file_at_path(&path);
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

    fn check_path_err_contains(relative_path: &str, needle: &str) -> CheckResult {
        let path = repo_path(relative_path);
        let result = check_file_at_path(&path);
        assert!(
            !result.diagnostics.is_empty(),
            "expected diagnostics, but `{relative_path}` checked successfully"
        );
        let rendered = format!("{:#?}", result.diagnostics);
        assert!(
            rendered.contains(needle),
            "diagnostics for `{relative_path}` did not contain `{needle}`:\n{rendered}"
        );
        result
    }

    #[test]
    fn theorem_diagnostic_reports_failing_tactic_line() {
        let result = check_file(
            r#"
mode constructive

theorem bad (P : Prop) : P := by
  assumption
"#,
        );
        assert_eq!(
            result.diagnostics[0].location.as_ref().map(|loc| loc.line),
            Some(5)
        );
    }

    #[test]
    fn parse_error_reports_tactic_line() {
        let result = check_file(
            r#"
mode constructive

theorem bad (P : Prop) : P -> P := by
  intro h
  exatc h
"#,
        );
        assert_eq!(
            result.diagnostics[0].location.as_ref().map(|loc| loc.line),
            Some(6)
        );
    }

    #[test]
    fn parse_error_reports_token_span() {
        let result = check_file(
            r#"
mode constructive

theorem bad : exists n : Nat, n = n := by
  exists @
"#,
        );
        assert_eq!(
            result.diagnostics[0].location.as_ref().map(|loc| loc.line),
            Some(5)
        );
        assert_eq!(result.diagnostics[0].span, Some(Span { start: 9, end: 10 }));
    }

    #[test]
    fn failed_tactic_reports_current_goal_as_target_note() {
        let result = check_file(
            r#"
mode constructive

theorem bad (P Q : Prop) : P -> P /\ Q := by
  intro hp
  split
  exact hp
  exact hp
"#,
        );
        assert!(!result.diagnostics.is_empty());
        assert_eq!(
            result.diagnostics[0].location.as_ref().map(|loc| loc.line),
            Some(8)
        );
        assert!(
            result.diagnostics[0]
                .notes
                .iter()
                .any(|note| note == "target: Q"),
            "diagnostic notes were {:#?}",
            result.diagnostics[0].notes
        );
    }

    #[test]
    fn failed_nested_tactic_reports_inner_tactic_line() {
        let result = check_file(
            r#"
mode constructive

theorem bad (P Q R : Prop) : P \/ Q -> R := by
  intro h
  cases h with
  | left hp =>
      exact hp
  | right hq =>
      exact hq
"#,
        );
        assert!(!result.diagnostics.is_empty());
        assert_eq!(
            result.diagnostics[0].location.as_ref().map(|loc| loc.line),
            Some(8)
        );
        assert!(
            result.diagnostics[0]
                .notes
                .iter()
                .any(|note| note == "target: R"),
            "diagnostic notes were {:#?}",
            result.diagnostics[0].notes
        );
    }

    #[test]
    fn show_goal_reports_current_goal() {
        check_err_contains(
            r#"
mode constructive

theorem bad (P : Prop) : P := by
  show_goal
"#,
            "current goal is `P`",
        );
    }

    #[test]
    fn intro_rejects_shadowing() {
        check_err_contains(
            r#"
mode constructive

theorem bad (P Q : Prop) : P -> Q -> P := by
  intro h
  intro h
  exact h
"#,
            "`intro` would shadow existing hypothesis `h`",
        );
    }

    #[test]
    fn true_goal_can_be_solved_directly() {
        check_ok(
            r#"
mode constructive

theorem exact_true : True := by
  exact True

theorem trivial_true : True := by
  trivial
"#,
        );
    }

    fn repo_path(relative_path: &str) -> std::path::PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(relative_path)
    }

    fn import_line(relative_path: &str) -> String {
        format!("import \"{}\"", repo_path(relative_path).display())
    }

    #[test]
    fn std_prop_checks() {
        check_ok(include_str!("../../../std/prop.ctea"));
    }

    #[test]
    fn std_fol_checks() {
        check_ok(include_str!("../../../std/fol.ctea"));
    }

    #[test]
    fn std_eq_checks() {
        check_ok(include_str!("../../../std/eq.ctea"));
    }

    #[test]
    fn std_set_checks() {
        check_ok(include_str!("../../../std/set.ctea"));
    }

    #[test]
    fn std_nat_checks() {
        check_ok(include_str!("../../../std/nat.ctea"));
    }

    #[test]
    fn std_prelude_checks() {
        check_path_ok("std/prelude.ctea");
    }

    #[test]
    fn example_prop_checks() {
        check_ok(include_str!("../../../examples/prop.ctea"));
    }

    #[test]
    fn example_fol_checks() {
        check_ok(include_str!("../../../examples/fol.ctea"));
    }

    #[test]
    fn example_set_nat_checks() {
        check_ok(include_str!("../../../examples/set_nat.ctea"));
    }

    #[test]
    fn example_library_patterns_checks() {
        check_ok(include_str!("../../../examples/library_patterns.ctea"));
    }

    #[test]
    fn example_imports_checks() {
        check_path_ok("examples/imports.ctea");
    }

    #[test]
    fn cs250_positive_examples_check() {
        for path in [
            "docs/cs250/code/01_propositional.ctea",
            "docs/cs250/code/02_proof_systems.ctea",
            "docs/cs250/code/03_first_order.ctea",
            "docs/cs250/code/04_induction_nat.ctea",
            "docs/cs250/code/05_sets.ctea",
            "docs/cs250/code/06_relations.ctea",
        ] {
            check_path_ok(path);
        }
    }

    #[test]
    fn cs250_fallacies_example_fails_as_documented() {
        let result = check_path_err_contains(
            "docs/cs250/code/02_fallacies_negative.ctea",
            "proof has type `Q`, but expected `P`",
        );
        let rendered = format!("{:#?}", result.diagnostics);
        assert!(
            rendered.contains("converse_error") && rendered.contains("inverse_error"),
            "diagnostics did not mention both intended fallacies:\n{rendered}"
        );
    }

    #[test]
    fn duplicate_import_is_loaded_once() {
        let import = import_line("std/prop.ctea");
        let result = check_ok(&format!(
            r#"
{import}
{import}

theorem use_imported_id (P : Prop) : P -> P := by
  exact id
"#
        ));
        assert_eq!(
            result
                .theorems
                .iter()
                .filter(|theorem| theorem.name == "id")
                .count(),
            1
        );
    }

    #[test]
    fn imports_mark_imported_and_root_theorems() {
        let result = check_path_ok("examples/imports.ctea");
        let imported = result
            .theorems
            .iter()
            .find(|theorem| theorem.name == "imp_trans")
            .expect("imported theorem");
        assert!(imported.is_imported);

        let root = result
            .theorems
            .iter()
            .find(|theorem| theorem.name == "imported_imp_trans")
            .expect("root theorem");
        assert!(!root.is_imported);
    }

    #[test]
    fn missing_import_is_reported() {
        check_err_contains("import definitely_missing.ctea", "could not read import");
    }

    #[test]
    fn import_cycle_is_reported() {
        let dir = std::env::temp_dir().join(format!("cetacea-import-cycle-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create temp import-cycle directory");
        std::fs::write(dir.join("a.ctea"), "import b.ctea\n").expect("write a.ctea");
        std::fs::write(dir.join("b.ctea"), "import a.ctea\n").expect("write b.ctea");

        let result = check_file_at_path(dir.join("a.ctea"));
        let rendered = format!("{:#?}", result.diagnostics);
        assert!(
            rendered.contains("import cycle involving"),
            "diagnostics did not contain import cycle:\n{rendered}"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn import_mode_does_not_leak() {
        let import = import_line("std/prop.ctea");
        check_err_contains(
            &format!(
                r#"
{import}

theorem bad (P : Prop) : P \/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h
"#
            ),
            "requires classical mode",
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
    fn or_cases_block_allows_following_tactic() {
        check_ok(
            r#"
mode constructive

theorem cases_then_next_goal (P Q : Prop) : (P \/ Q) -> (Q \/ P) /\ (P \/ Q) := by
  intro h
  split
  cases h with
  | left hp =>
      right
      exact hp
  | right hq =>
      left
      exact hq
  exact h
"#,
        );
    }

    #[test]
    fn exists_cases_block_allows_following_tactic() {
        check_ok(
            r#"
mode constructive

theorem exists_cases_then_next_goal
  (A : Type)
  (P : A -> Prop)
  : (exists x : A, P(x)) -> (exists x : A, P(x)) /\ (exists x : A, P(x)) := by
  intro h
  split
  cases h with
  | intro x hx =>
      exists x
      exact hx
  exact h
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
    fn multi_binder_forall_parses_as_nested_foralls() {
        check_ok(
            r#"
mode constructive

sort Person
pred R(Person, Person)

theorem multi_forall
  : (forall x y : Person, R(x, y)) -> forall x y : Person, R(x, y) := by
  intro h
  intro x
  intro y
  exact h x y

theorem multi_exists
  : (exists x y : Person, R(x, y)) -> exists x y : Person, R(x, y) := by
  intro h
  exact h
"#,
        );
    }

    #[test]
    fn exact_can_apply_implication_proofs_inline() {
        check_ok(
            r#"
mode constructive

theorem imp_exact (P Q : Prop) : (P -> Q) -> P -> Q := by
  intro h
  intro hp
  exact h hp

theorem imp_projection (P Q R : Prop) : (P -> Q /\ R) -> P -> Q := by
  intro h
  intro hp
  exact (h hp).left
"#,
        );
    }

    #[test]
    fn alpha_equivalent_forall_binders_are_definitionally_equal() {
        check_ok(
            r#"
mode constructive

theorem alpha_forall
  (P : Nat -> Prop)
  : (forall x : Nat, P(x)) -> forall y : Nat, P(y) := by
  intro h
  exact h
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
    fn rewrite_accepts_compound_symmetry_expression() {
        let import = import_line("std/eq.ctea");
        check_ok(&format!(
            r#"
{import}
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

theorem rewrite_with_symm
  : alice = mother(alice) -> Happy(mother(alice)) -> Happy(alice) := by
  intro h
  intro hm
  rewrite eq_symm h
  exact hm
"#
        ));
    }

    #[test]
    fn rewrite_forward_rewrites_left_to_right() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

theorem rewrite_forward
  : alice = mother(alice) -> Happy(mother(alice)) -> Happy(alice) := by
  intro h
  intro hm
  rewrite -> h
  exact hm
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
    fn formula_definition_accepts_prop_and_predicate_parameters() {
        check_ok(
            r#"
mode constructive

sort Person
pred Likes(Person, Person)

def ConjSelf (P : Prop) : Prop := P /\ P
def Reflexive (T : Type) (R : T -> T -> Prop) : Prop := forall x : T, R(x, x)

theorem conj_self_left (P : Prop) : ConjSelf(P) -> P := by
  intro h
  exact h.left

theorem reflexive_likes
  : (forall x : Person, Likes(x, x)) -> Reflexive(Likes) := by
  intro h
  exact h
"#,
        );
    }

    #[test]
    fn formula_definition_accepts_predicate_lambda_argument() {
        check_ok(
            r#"
mode constructive

sort Person

def Reflexive (T : Type) (R : T -> T -> Prop) : Prop := forall x : T, R(x, x)

theorem reflexive_eq : Reflexive(fun x y : Person => x = y) := by
  simp
  intro x
  refl
"#,
        );
    }

    #[test]
    fn predicate_lambda_argument_must_match_expected_type() {
        check_err_contains(
            r#"
mode constructive

sort Person

def NatPred (P : Nat -> Prop) : Prop := forall n : Nat, P(n)

theorem bad : NatPred(fun x : Person => x = x) := by
"#,
            "predicate lambda parameter `x` has type `Person`, but expected `Nat`",
        );
    }

    #[test]
    fn theorem_explicit_schema_accepts_predicate_lambda_argument() {
        check_ok(
            r#"
mode constructive

theorem pred_id
  (A : Type)
  (P : A -> Prop)
  (x : A)
  : P(x) -> P(x) := by
  intro h
  exact h

theorem use_pred_id (n : Nat) : n = n -> n = n := by
  intro h
  exact pred_id {A := Nat; P := fun x => x = x; x := n} h
"#,
        );
    }

    #[test]
    fn set_builder_terms_simplify_membership() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
pred Tall(Person)

def TallSet : Set Person := { x : Person | Tall(x) }

theorem tall_member_named : Tall(alice) -> alice in TallSet := by
  intro h
  simp
  exact h

theorem tall_member_inline : Tall(alice) -> alice in { x : Person | Tall(x) } := by
  intro h
  simp
  exact h
"#,
        );
    }

    #[test]
    fn parameterized_term_definitions_simplify_membership() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
const bob : Person
pred Likes(Person, Person)
pred Tall(Person)

def LikesSet (y : Person) : Set Person := { x : Person | Likes(x, y) }
def TruthSet (T : Type) (P : T -> Prop) : Set T := { x : T | P(x) }
def One (T : Type) (x : T) : Set T := singleton(x)

theorem likes_set_member : Likes(alice, bob) -> alice in LikesSet(bob) := by
  intro h
  simp
  exact h

theorem truth_set_member : Tall(alice) -> alice in TruthSet(Tall) := by
  intro h
  simp
  exact h

theorem truth_set_lambda_member : alice in TruthSet(fun x : Person => x = alice) := by
  simp
  refl

theorem one_member : alice in One(alice) := by
  simp
  refl
"#,
        );
    }

    #[test]
    fn parameterized_term_definition_arity_mismatch_is_rejected() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person
pred Tall(Person)

def LikesSet (y : Person) : Set Person := { x : Person | Tall(x) }

theorem bad : alice in LikesSet := by
"#,
            "definition `LikesSet` expects 1 argument(s), but got 0",
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
    fn simp_uses_listed_equality_theorem_as_rewrite_rule() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func mother : Person -> Person
pred Happy(Person)

axiom mother_alice : mother(alice) = alice

theorem happy_mother : Happy(alice) -> Happy(mother(alice)) := by
  intro h
  simp [mother_alice]
  exact h
"#,
        );
    }

    #[test]
    fn simp_rule_can_instantiate_schema_term_arguments() {
        check_ok(
            r#"
mode constructive

sort Person
const alice : Person
func normalize : Person -> Person
pred Happy(Person)

axiom normalize_id (x : Person) : normalize(x) = x

theorem happy_normalized : Happy(alice) -> Happy(normalize(alice)) := by
  intro h
  simp [normalize_id]
  exact h
"#,
        );
    }

    #[test]
    fn simp_rule_must_be_equality() {
        check_err_contains(
            r#"
mode constructive

axiom trusted : True

theorem bad : True := by
  simp [trusted]
"#,
            "simp rule `trusted` must prove a term equality",
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

theorem add_zero_right (n : Nat) : add(n, 0) = n := by
  simp
  refl

theorem add_succ_right (n m : Nat) : add(n, succ(m)) = succ(add(n, m)) := by
  simp
  refl

theorem add_one_zero : add(succ(0), 0) = succ(0) := by
  simp
  refl
"#,
        );
    }

    #[test]
    fn primitive_nat_recursion_definitions_compute_under_simp() {
        check_ok(
            r#"
mode constructive

defrec double (n : Nat) : Nat
| zero => 0
| succ k rec => succ(succ(rec))

theorem double_zero : double(0) = 0 := by
  simp
  refl

theorem double_two : double(succ(succ(0))) = succ(succ(succ(succ(0)))) := by
  simp
  refl

theorem double_succ (n : Nat) : double(succ(n)) = succ(succ(double(n))) := by
  simp
  refl
"#,
        );
    }

    #[test]
    fn primitive_nat_recursion_rejects_non_nat_parameter() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person

defrec bad (x : Person) : Nat
| zero => 0
| succ k rec => rec
"#,
            "recursive definition parameter must have type `Nat`",
        );
    }

    #[test]
    fn primitive_nat_recursion_checks_case_types() {
        check_err_contains(
            r#"
mode constructive

sort Person
const alice : Person

defrec bad (n : Nat) : Nat
| zero => alice
| succ k rec => rec
"#,
            "zero case has type `Person`, but expected `Nat`",
        );
    }

    #[test]
    fn primitive_nat_recursion_rejects_duplicate_successor_binders() {
        check_err_contains(
            r#"
mode constructive

defrec bad (n : Nat) : Nat
| zero => 0
| succ k k => k
"#,
            "recursive definition successor case binders must be distinct",
        );
    }

    #[test]
    fn simp_computes_inside_predicate_arguments() {
        check_ok(
            r#"
mode constructive

pred Even(Nat)

theorem even_zero_to_simplified_arg : Even(0) -> Even(add(0, 0)) := by
  intro h
  simp
  exact h
"#,
        );
    }

    #[test]
    fn simp_at_simplifies_named_hypothesis() {
        check_ok(
            r#"
mode constructive

theorem inter_hyp_right
  (T : Type)
  (x : T)
  (A B : Set T)
  : x in inter(A, B) -> x in B := by
  intro h
  simp at h
  exact h.right
"#,
        );
    }

    #[test]
    fn simp_at_rejects_no_progress() {
        check_err_contains(
            r#"
mode constructive

theorem bad (P : Prop) : P -> P := by
  intro h
  simp at h
  exact h
"#,
            "simp made no progress on hypothesis `h`",
        );
    }

    #[test]
    fn simp_at_star_simplifies_goal_and_hypotheses() {
        check_ok(
            r#"
mode constructive

theorem inter_hyp_and_goal
  (T : Type)
  (x : T)
  (A B : Set T)
  : x in inter(A, B) -> x in inter(B, B) := by
  intro h
  simp at *
  split
  exact h.right
  exact h.right
"#,
        );
    }

    #[test]
    fn simp_at_star_rejects_no_progress() {
        check_err_contains(
            r#"
mode constructive

theorem bad (P : Prop) : P -> P := by
  intro h
  simp at *
  exact h
"#,
            "simp made no progress on goal or hypotheses",
        );
    }

    #[test]
    fn nat_multiplication_computes_under_simp() {
        check_ok(
            r#"
mode constructive

theorem mul_zero_left (n : Nat) : mul(0, n) = 0 := by
  simp
  refl

theorem mul_succ_left (n m : Nat) : mul(succ(n), m) = add(m, mul(n, m)) := by
  simp
  refl

theorem mul_zero_right (n : Nat) : mul(n, 0) = 0 := by
  simp
  refl

theorem mul_succ_right (n m : Nat) : mul(n, succ(m)) = add(n, mul(n, m)) := by
  simp
  refl

theorem mul_two_one : mul(succ(succ(0)), succ(0)) = succ(succ(0)) := by
  simp
  refl
"#,
        );
    }

    #[test]
    fn nat_subtraction_computes_under_simp() {
        check_ok(
            r#"
mode constructive

theorem sub_zero_right (n : Nat) : sub(n, 0) = n := by
  simp
  refl

theorem sub_zero_left (n : Nat) : sub(0, n) = 0 := by
  simp
  refl

theorem sub_succ_succ (n m : Nat) : sub(succ(n), succ(m)) = sub(n, m) := by
  simp
  refl

theorem sub_two_one : sub(succ(succ(0)), succ(0)) = succ(0) := by
  simp
  refl
"#,
        );
    }

    #[test]
    fn nat_le_computes_under_simp() {
        check_ok(
            r#"
mode constructive

theorem zero_le (n : Nat) : le(0, n) := by
  simp
  trivial

theorem succ_not_le_zero (n : Nat) : le(succ(n), 0) -> False := by
  simp
  intro h
  exact h

theorem one_le_two : le(succ(0), succ(succ(0))) := by
  simp
  trivial

theorem two_not_le_one : le(succ(succ(0)), succ(0)) -> False := by
  simp
  intro h
  exact h
"#,
        );
    }

    #[test]
    fn nat_induction_proves_add_assoc() {
        check_ok(
            r#"
mode constructive

theorem add_assoc (n m k : Nat) : add(add(n, m), k) = add(n, add(m, k)) := by
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
    fn induction_block_allows_following_tactic() {
        check_ok(
            r#"
mode constructive

theorem induction_then_next_goal (n : Nat) : add(n, 0) = n /\ n = n := by
  split
  induction n with
  | zero =>
      simp
      refl
  | succ k ih =>
      simp
      refl
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
    fn powerset_membership_computes_under_simp() {
        check_ok(
            r#"
mode constructive

sort Person

theorem powerset_intro_demo
  (A B : Set Person)
  : B subset A -> B in powerset(A) := by
  intro h
  simp
  exact h

theorem powerset_elim_demo
  (A B : Set Person)
  : B in powerset(A) -> B subset A := by
  intro h
  simp at h
  exact h
"#,
        );
    }

    #[test]
    fn powerset_argument_must_be_a_set() {
        check_err_contains(
            r#"
mode constructive

theorem bad (n : Nat) : empty(Nat) in powerset(n) := by
"#,
            "powerset argument has type `Nat`, but expected a set",
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
    fn explicit_schema_args_work_when_names_overlap() {
        let import = import_line("std/set.ctea");
        check_ok(&format!(
            r#"
{import}
mode constructive

theorem subsets_carry
  (T : Type)
  (A B S : Set T)
  : A subset B -> S subset A -> S subset B := by
  intro hAB
  intro hSA
  apply subset_trans {{T := T; A := S; B := A; C := B}}
  exact hSA
  exact hAB
"#
        ));
    }

    #[test]
    fn apply_infers_intermediate_schema_argument_from_hypotheses() {
        let import = import_line("std/set.ctea");
        check_ok(&format!(
            r#"
{import}
mode constructive

theorem subsets_carry_without_explicit_middle
  (T : Type)
  (A B S : Set T)
  : A subset B -> S subset A -> S subset B := by
  intro hAB
  intro hSA
  apply subset_trans
  exact hSA
  exact hAB
"#
        ));
    }

    #[test]
    fn apply_infers_eq_trans_middle_from_hypotheses() {
        let import = import_line("std/eq.ctea");
        check_ok(&format!(
            r#"
{import}
mode constructive

theorem eq_trans_without_explicit_middle
  (x y z : Nat)
  : x = y -> y = z -> x = z := by
  intro hxy
  intro hyz
  apply eq_trans
  exact hxy
  exact hyz
"#
        ));
    }

    #[test]
    fn explicit_schema_args_can_combine_with_forall_args() {
        check_ok(
            r#"
mode constructive

sort Person

axiom all_subset_trans
  (T : Type)
  : forall A B C : Set T, A subset B -> B subset C -> A subset C

theorem use_all_subset_trans
  (X Y Z : Set Person)
  : X subset Y -> Y subset Z -> X subset Z := by
  intro hXY
  intro hYZ
  apply all_subset_trans {T := Person} X Y Z
  exact hXY
  exact hYZ
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
            "available schema arguments: `P`",
        );
    }

    #[test]
    fn invalid_explicit_schema_argument_value_names_the_argument() {
        check_err_contains(
            r#"
mode constructive

theorem refl_arg (A : Type) (x : A) : x = x := by
  refl

theorem bad (A : Type) (x : A) : x = x := by
  exact refl_arg {A := A; x := missing}
"#,
            "invalid value for schema argument `x` of theorem `refl_arg`: unknown term `missing`",
        );
    }

    #[test]
    fn missing_schema_argument_reports_theorem_and_parameter_kind() {
        check_err_contains(
            r#"
mode constructive

theorem unused_type (A B : Type) (x : A) : x = x := by
  refl

theorem bad (A : Type) (x : A) : x = x := by
  exact unused_type {A := A; x := x}
"#,
            "cannot infer schema argument `B` for theorem `unused_type` (type parameter); provide it explicitly with `{B := ...}`",
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
