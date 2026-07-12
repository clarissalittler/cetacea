# Cetacea Design and Code Guide

This guide explains the implementation structure, the design decisions behind
the current language, and how the Rust code fits together. It is written for
someone who wants to maintain Cetacea or extend it.

The main implementation lives in `crates/cetacea_core/src/lib.rs`. The CLI in
`crates/cetacea_cli/src/main.rs` is intentionally thin: it reads a path, asks
the core checker to check that path, and prints the resulting diagnostics or
accepted declarations.

## High-Level Design

Cetacea is a small tactic-based theorem prover with a checked proof-object
kernel.

The important design choice is this separation:

1. Parse source files into syntax trees and tactic scripts.
2. Elaborate tactic scripts into proof objects.
3. Independently check proof objects in a smaller kernel.

This keeps tactic execution out of the trusted core. Tactics can be incomplete
or convenience-oriented, but the proof object still has to pass the kernel.

The current implementation is intentionally compact. There is one core crate,
one CLI crate, and a checked standard library written in Cetacea itself.

## Repository Layout

```text
crates/cetacea_core/src/lib.rs
  ASTs, parser, environment, validator, tactic elaborator, proof checker,
  imports, diagnostics, and tests.

crates/cetacea_cli/src/main.rs
  Command-line entry point.

crates/cetacea_wasm/src/lib.rs
  WebAssembly boundary. Exposes JSON-returning C-ABI functions for checking,
  source outline, cursor goals, and tactic stepping.

web/
  Static browser UI that loads the wasm checker.

std/
  Checked theorem-library files.

std/prelude.ctea
  Imports the standard theorem-library files.

examples/
  Standalone examples and import examples.

docs/
  Long-form user and implementation guides.
```

## Public API

The main public entry points are:

```rust
pub fn check_file(source: &str) -> CheckResult
pub fn check_file_at_path(path: impl AsRef<Path>) -> CheckResult
pub fn check_source_at_path(source: &str, path: impl AsRef<Path>) -> CheckResult
pub fn check_file_with_imports(source: &str, imports: &[VirtualFile]) -> CheckResult
pub fn outline(source: &str) -> SourceOutline
pub fn goals_at(source: &str, position: Position) -> GoalStepResult
pub fn goals_at_path(path: impl AsRef<Path>, position: Position) -> GoalStepResult
pub fn goals_at_source_path(
    source: &str,
    path: impl AsRef<Path>,
    position: Position,
) -> GoalStepResult
pub fn goals_at_with_imports(
    source: &str,
    position: Position,
    imports: &[VirtualFile],
) -> GoalStepResult
pub fn run_tactic(source: &str, theorem_name: &str, tactic_index: usize) -> GoalStepResult
pub fn run_tactic_at_path(
    path: impl AsRef<Path>,
    theorem_name: &str,
    tactic_index: usize,
) -> GoalStepResult
pub fn run_tactic_in_source_at_path(
    source: &str,
    path: impl AsRef<Path>,
    theorem_name: &str,
    tactic_index: usize,
) -> GoalStepResult
pub fn run_tactic_with_imports(
    source: &str,
    theorem_name: &str,
    tactic_index: usize,
    imports: &[VirtualFile],
) -> GoalStepResult
pub fn explain_theorem(source: &str, theorem_name: &str) -> ExplanationResult
pub fn explain_theorem_at_path(path: impl AsRef<Path>, theorem_name: &str) -> ExplanationResult
pub fn explain_theorem_in_source_at_path(
    source: &str,
    path: impl AsRef<Path>,
    theorem_name: &str,
) -> ExplanationResult
pub fn explain_theorem_with_imports(
    source: &str,
    theorem_name: &str,
    imports: &[VirtualFile],
) -> ExplanationResult
pub fn check_proof(
    signature: &KernelSignature<'_>,
    ctx: &Context,
    proof: &KernelProof,
    expected: &Formula,
    allowed_mode: LogicMode,
) -> Result<LogicMode, KernelError>
```

`Env::kernel_signature()` creates the opaque, read-only signature view. The
legacy implementation still adapts that view to the existing environment
internally, but callers no longer make the full checker environment part of the
kernel API.

Use `check_file` for in-memory source strings. It can parse import declarations,
but relative imports are resolved relative to the current working directory
because there is no root path.

Use `check_file_at_path` for real files. This is what the CLI uses. It supports
imports relative to the importing file.

Use `check_source_at_path` and the source-at-path editor APIs for an
unsaved editor buffer that still has a real filesystem identity. This is what
the terminal TUI uses: the displayed source comes from memory, diagnostics are
tied to the opened file path, and imports still resolve relative to that file.

Use the `*_at_path` editor APIs for terminal or filesystem-backed editor
integrations. They parse the selected root file, keep source locations tied to
that path, and resolve imports relative to the root file while showing goals,
stepping tactics, or explaining a proof.

Use `check_file_with_imports` and the `*_with_imports` goal APIs for in-memory
or browser-hosted sources where imports come from a virtual file map rather than
the local filesystem.

Use `explain_theorem_with_imports` for editor-facing proof explanations. It
checks declarations before the selected theorem, runs the theorem tactic script
step by step, and returns the goal before each tactic, the goals afterward, and
short rule-based explanation sentences. The explanations are derived from the
checked tactic execution path; they are not independent proof search.

`check_proof` and `infer_proof` are the lower-level kernel-facing APIs. Most
callers should not need them directly unless they are constructing proof
objects programmatically.

`outline`, `goals_at`, and `run_tactic` are editor-facing APIs. They parse the
source, check declarations before the selected theorem, run tactics through the
existing tactic elaborator, and return rendered goal snapshots plus diagnostics.
`run_tactic` uses zero-based tactic indexes and returns the state after running
the selected tactic and all prior tactics in that theorem.

## Core ASTs

### Types

`Type` represents first-order types:

```rust
pub enum Type {
    Named(Name),
    Nat,
    Prod(Box<Type>, Box<Type>),
    Set(Box<Type>),
}
```

Design notes:

- `Named` is for user-declared sorts and type parameters.
- `Nat` is built in because natural-number induction and computation are built
  into the language.
- `Prod(T, U)` is built in for ordered pairs and Cartesian products.
- `Set(T)` is built in because set membership, subset, and set operations have
  special validation and simplification rules.

`Prop` and `Type` are not first-order `Type` values. They appear in parameter
declarations through `ParamKind`.

### Terms

`Term` represents first-order terms:

```rust
pub enum Term {
    Var(Name),
    App(Name, Vec<Term>),
    Zero,
    Succ(Box<Term>),
    Add(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    Pair(Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    EmptySet(Type),
    Universe(Type),
    Singleton(Box<Term>),
    Union(Box<Term>, Box<Term>),
    Inter(Box<Term>, Box<Term>),
    Diff(Box<Term>, Box<Term>),
    Complement(Box<Term>),
    CartProd(Box<Term>, Box<Term>),
    Powerset(Box<Term>),
    SetBuilder { var: Name, var_type: Type, body: Box<Formula> },
}
```

Design notes:

- User functions are represented by `App`.
- Built-ins have dedicated variants. That makes validation and simplification
  direct and avoids encoding arithmetic and set computation as opaque
  functions.
- `empty(T)` carries an explicit type because the element type cannot always be
  inferred from context.
- Nonempty finite set literals such as `{x, y}` parse as nested `union` terms
  over `singleton` terms, so they reuse the ordinary set validation and
  simplification paths.

### Formulas

`Formula` represents propositions:

```rust
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
    Forall { var: Name, var_type: Type, body: Box<Formula> },
    Exists { var: Name, var_type: Type, body: Box<Formula> },
}
```

Design notes:

- `not P` is represented as `P -> False`.
- `P <-> Q` is parsed into `(P -> Q) /\ (Q -> P)` rather than having its own
  kernel rule.
- Membership and subset have dedicated formula constructors because they have
  set-specific typing and simplification behavior.

## Parameters and Schema Variables

Theorem, axiom, and definition parameters are represented by:

```rust
pub enum ParamKind {
    Prop,
    Predicate(Vec<Type>),
    Type,
    Term(Type),
}

pub struct Param {
    pub name: Name,
    pub kind: ParamKind,
}
```

This is how Cetacea supports theorem schemas:

```text
theorem forall_mono
  (A : Type)
  (P Q : A -> Prop)
  : (forall x : A, P(x) -> Q(x)) -> (forall x : A, P(x)) -> forall x : A, Q(x) := by
  ...
```

When the user writes `exact forall_mono`, the elaborator tries to infer values
for `A`, `P`, and `Q` from the current goal. When inference is not strong
enough, the user can write explicit arguments:

```text
exact forall_mono {A := Person; P := Student; Q := Enrolled}
```

Explicit and inferred schema assignments are stored in `SchemaSubst`:

```rust
pub struct SchemaSubst {
    pub type_args: HashMap<Name, Type>,
    pub term_args: HashMap<Name, Term>,
    pub formula_args: HashMap<Name, Formula>,
    pub predicate_args: HashMap<Name, PredicateArg>,
}
```

Predicate schema arguments can be predicate names or inline predicate lambdas.
Lambdas are validated against the expected predicate parameter type before
their bodies are substituted at predicate applications. Lambda application uses
simultaneous, capture-avoiding substitution so lambda binder names may overlap
with surrounding theorem variables.

## Proof Objects

Tactics build a `DraftProof`. It has the natural-deduction constructors plus a
`Sorry` hole used by editor and homework-skeleton workflows:

```rust
pub enum DraftProof {
    Hyp(Name),
    TrueIntro,
    FalseElim { proof_false: Box<DraftProof>, target: Formula },
    AndIntro(Box<DraftProof>, Box<DraftProof>),
    AndElimLeft(Box<DraftProof>),
    AndElimRight(Box<DraftProof>),
    OrIntroLeft { ... },
    OrIntroRight { ... },
    OrElim { ... },
    ImpIntro { ... },
    ImpElim { ... },
    ForallIntro { ... },
    ForallElim { ... },
    ExistsIntro { ... },
    ExistsElim { ... },
    EqRefl(Term),
    EqSubst { ... },
    NatInduction { ... },
    TheoremRef { ... },
    Classical(ClassicalRule, Formula),
    Convert { ... },
    Sorry { target: Formula },
}

pub struct KernelProof(DraftProof); // private field

pub enum TheoremEvidence {
    Kernel(KernelProof),
    Incomplete(DraftProof),
    TrustedAxiom,
}
```

Design notes:

- Proof objects are natural-deduction-style.
- Tactics do not directly prove theorems. They build draft proof objects.
- The only conversion to `KernelProof` recursively rejects `Sorry`; its inner
  field is private, and `check_proof` accepts only this hole-free type.
- Results distinguish accepted proofs, incomplete drafts, and trusted axioms.
- The environment stores the matching `TheoremEvidence` variant rather than an
  optional, potentially hole-bearing proof.
- `Convert` exists for transparent formula definitions and definitional
  equality.
- Classical rules are explicit proof nodes, so the checker can track whether a
  proof used classical reasoning.

## Environment and Context

`Env` stores top-level declarations:

```rust
pub struct Env {
    sorts: HashMap<Name, Type>,
    consts: HashMap<Name, Type>,
    funcs: HashMap<Name, FuncDecl>,
    preds: HashMap<Name, Vec<Type>>,
    defs: HashMap<Name, FormulaDef>,
    theorems: HashMap<Name, Theorem>,
}
```

`Context` stores local proof state:

- proof hypotheses
- local term variables
- theorem schema type variables
- theorem schema proposition variables
- theorem schema predicate variables

The environment is global for a checking session. Unaliased imports keep the
legacy behavior of adding declarations to the same environment as the root
file. Aliased imports check imported declarations under the alias namespace, so
`import std/nat.ctea as nat` exposes names such as `nat.add_comm` without also
exposing that import's short names. Dot-qualified top-level names are accepted,
and namespace blocks prefix declarations and resolve sibling top-level
references through the current namespace.

The context is local to a theorem proof or definition body. It is built from
the declaration parameters and extended by tactics such as `intro`, `cases`,
and `induction`.

## Checking Pipeline

The root checker pipeline is:

```text
check_file / check_file_at_path
  -> FileChecker
  -> parse_file
  -> check_commands
      imports
      modes
      declarations
      theorem validation
      tactic elaboration with prove
      kernel check with check_proof
  -> CheckResult
```

For a theorem:

1. Reject top-level name collisions.
2. Build a theorem context from parameters.
3. Validate the statement in that context.
4. Run the tactic script with `prove`.
5. Check the generated proof object with `check_proof`.
6. Reject classical proof use if the current mode is constructive.
7. Add the theorem to the environment.
8. Add an accepted declaration to `CheckResult`.

This means later declarations can use earlier declarations in the same file.

## Imports

Imports are handled by `FileChecker`.

State:

```rust
loaded_files: HashSet<PathBuf>
import_stack: Vec<PathBuf>
```

Design decisions:

- Imports are checked immediately when encountered.
- Imports are loaded into the same global environment.
- Duplicate imports are skipped by canonical path.
- Cycles are detected with `import_stack`.
- Import path resolution tries the importing file's directory first, then the
  current working directory.
- The mode of an imported file does not leak. Each call to `check_commands`
  starts with `LogicMode::Constructive`.

`CheckedTheorem` includes:

```rust
pub statement: String
pub is_imported: bool
```

The CLI uses `is_imported` to print only declarations from the root file. The
browser uses `statement` plus the imported flag to populate the searchable
theorem-library panel. The imported declarations are still available to later
proofs.

## Diagnostics

Diagnostics are returned in `CheckResult`:

```rust
pub struct Diagnostic {
    pub span: Option<Span>,
    pub location: Option<SourceLocation>,
    pub message: String,
    pub notes: Vec<String>,
    pub suggestions: Vec<DiagnosticSuggestion>,
}
```

Current diagnostic design:

- `SourceLocation` reports an optional path and a command, parse-error, or
  tactic-execution line.
- Parser errors carry line-local `Span` values when the parser can identify the
  offending token.
- The parser stores line numbers on top-level commands via `LocatedCommand` and
  on raw tactic lines while parsing theorem bodies.
- Tactic execution errors report the failing tactic line and attach the current
  open goal as the diagnostic target note.
- Common tactic errors also carry structured recovery suggestions so the browser
  and CLI can show next actions without parsing diagnostic strings.
- The CLI prints `path:line: message` when location information exists.

This is a pragmatic halfway point. It helps users find failing declarations and
parse tokens without requiring a fully span-aware checked AST.

## Parser Design

The parser is deliberately lightweight and line-oriented.

Top-level commands:

- `import`
- `mode`
- `sort`
- `const`
- `func`
- `pred`
- `def`
- `axiom`
- `theorem`

`parse_file` walks source lines and recognizes commands from their leading
keyword after comments are stripped. Multi-line theorem, axiom, and definition
headers are accumulated into a single string before being parsed.

Formula and term expressions are parsed by a simple token stream:

- `Tokens::parse_type`
- `Tokens::parse_term`
- `Tokens::parse_formula`

The formula parser handles precedence:

1. implication, right associative
2. biconditional, parsed as conjunction of implications
3. disjunction
4. conjunction
5. unary and atomic formulas

Proof expressions are parsed separately. They support:

- theorem or hypothesis names
- explicit arguments in `{...}`, including wrapped tactic-line continuations
- forall application with term arguments
- implication application with proof arguments
- `.left` and `.right` projections

For theorem references with inline arguments, elaboration can infer schema
arguments from supplied proof arguments before building the final `TheoremRef`.
This supports expressions such as `rewrite <- eq_symm h`.

## Tactic Parsing

Tactics are line-oriented.

Simple tactic lines include:

```text
intro h
exact h
trivial
assumption
apply h
exists x
refl
rewrite <- h
unfold Name
simp
simp at h
simp at *
exfalso
contradiction
by_contra h
show_goal
```

Structured tactic blocks include:

```text
cases h with
| left hp =>
    ...
| right hq =>
    ...
```

```text
cases h with
| intro x hx =>
    ...
```

```text
induction n with
| zero =>
    ...
| succ k ih =>
    ...
```

The parser uses indentation to find the end of each case arm body. This is a
conscious compromise: it keeps the grammar simple while allowing more tactics
after a `cases` or `induction` block.

## Tactic Elaboration

`prove` runs a tactic script against a goal list.

The elaborator uses:

- `Goal`, with an id, context, and target
- `PartialProof`, a proof tree with holes
- `StepResult`, a replacement partial proof plus new subgoals

Each tactic consumes the current goal and returns either a completed proof
fragment or new goals.

Example: `split`

- If the target is `P /\ Q`, it replaces the current hole with
  `AndIntro(left_hole, right_hole)`.
- It creates one goal for `P`.
- It creates one goal for `Q`.

Example: `intro`

- If the target is `P -> Q`, it adds a proof hypothesis `h : P` to the context
  and creates a goal for `Q`.
- If the target is `forall x : A, P(x)`, it adds a term variable `x : A` and
  creates a goal for `P(x)`.

Example: `revert`

- If the latest proof hypothesis is `h : P` and the target is `Q`, it removes
  `h` from the new goal context and creates the target `P -> Q`.
- The surrounding proof fragment applies the resulting implication proof to
  the original witness for `h`, so the kernel still checks ordinary implication
  elimination.

Example: `cases`

- For `P \/ Q`, it creates an `OrElim` proof with a branch context containing
  the left or right hypothesis.
- For `exists x : A, P(x)`, it creates an `ExistsElim` proof with a witness
  term variable and hypothesis.

Example: `rewrite`

- It checks that the supplied proof expression has equality type.
- It searches the current target for the equality's right-hand side.
- It generates a subgoal where one occurrence has been replaced by the
  equality's left-hand side.
- The kernel later checks this as `EqSubst`.

## Kernel Checking

The public kernel boundary is:

```rust
pub fn check_proof(
    signature: &KernelSignature<'_>,
    ...,
    proof: &KernelProof,
    ...,
)
```

Node inference is private and only runs after conversion to `KernelProof` has
recursively excluded draft holes.

`infer_proof` computes the formula proved by a proof object. `check_proof`
validates that the inferred formula is definitionally equal to the expected
formula.

The kernel validates:

- local hypothesis lookup
- introduction and elimination rules
- equality reflexivity and substitution
- theorem references with schema substitution
- universal and existential quantifier rules
- natural-number induction
- classical proof nodes
- transparent conversion

The kernel also returns the strongest `LogicMode` used by a proof:

```rust
Constructive
Classical
```

Theorem checking then rejects classical proof use if the current source mode is
constructive.

## Validation

Validation functions reject ill-formed declarations before tactic execution or
kernel checking.

Important validators:

- `validate_type`
- `validate_term`
- `validate_formula`

Validation checks:

- known type names
- known function names
- known predicate names
- function arity
- predicate arity
- term argument types
- predicate argument types
- set element compatibility
- subset compatibility
- definition body well-formedness
- theorem and axiom parameter well-formedness

This is why errors such as unknown predicates or type mismatches are caught
before proof search.

## Definitional Equality and Normalization

Cetacea has transparent formula and term definitions and a small amount of
built-in computation.

Important functions:

- `normalize_formula_defs`
- `normalize_formula_for_kernel`
- `normalize_term`
- `normalize_rec_def`
- `normalize_term_compute`
- formula/term substitution helpers
- formula equality helpers

Transparent definitions let users write:

```text
def HappyMother (x : Person) : Prop := Happy(mother(x))
```

and then prove goals involving `HappyMother(alice)` by unfolding or simplifying
to `Happy(mother(alice))`.

Kernel conversion also enforces datatype no-confusion. Applications of
different constructors are disjoint, and equality of two applications of the
same constructor is equivalent to equality of their corresponding arguments.
This stronger kernel normalization is separate from tactic-facing display
normalization: ordinary goals such as `cons(a, as) = cons(b, bs)` remain visibly
equalities, while projections and proof checking may use constructor
injectivity.

Term definitions support named and parameterized set builders:

```text
def TallSet : Set Person := { x : Person | Tall(x) }
def LikesSet (y : Person) : Set Person := { x : Person | Likes(x, y) }
def TruthSet (T : Type) (P : T -> Prop) : Set T := { x : T | P(x) }
```

Recursive definitions are deliberately narrower. `defrec` defines structural
primitive recursion over `Nat` or a declared data type, with optional fixed
parameters after the recursive first argument:

```text
defrec double (n : Nat) : Nat
| zero => 0
| succ k rec => succ(succ(rec))
```

The checker validates the zero case in an empty term context and validates the
successor case with `k : Nat` and `rec : result_type`. The recursive definition
is added to the environment only after both cases validate, so definitions are
structural, non-mutual, and cannot make direct self-calls except through the
provided `rec` value. During normalization, `normalize_rec_def` reduces
applications at `0` and `succ(k)` and leaves calls on neutral arguments stuck.

Built-in term computation currently covers Nat addition, multiplication, and
truncated subtraction:

```text
add(0, n)         ==> n
add(n, 0)         ==> n
add(succ(n), m)  ==> succ(add(n, m))
add(n, succ(m))  ==> succ(add(n, m))
mul(0, n)         ==> 0
mul(n, 0)         ==> 0
mul(succ(n), m)  ==> add(m, mul(n, m))
mul(n, succ(m))  ==> add(n, mul(n, m))
sub(n, 0)         ==> n
sub(0, n)         ==> 0
sub(succ(n), succ(m))  ==> sub(n, m)
```

This computation is applied recursively to terms, including terms nested under
function and predicate arguments.

The built-in Nat comparison `le(n, m)` is represented as a predicate
application with a reserved predicate signature `Nat, Nat`. Formula
simplification computes:

```text
le(0, n)                 ==> True
le(succ(n), 0)           ==> False
le(succ(n), succ(m))     ==> le(n, m)
```

Set simplification is mostly formula-level. Membership in set constructors is
expanded:

```text
x in empty(T)      ==> False
x in univ(T)       ==> True
x in singleton(y)  ==> x = y
x in union(A, B)   ==> x in A \/ x in B
x in inter(A, B)   ==> x in A /\ x in B
x in diff(A, B)    ==> x in A /\ not x in B
x in compl(A)      ==> not x in A
x in prod(A, B)    ==> fst(x) in A /\ snd(x) in B
x in powerset(A)   ==> x subset A
x in { y : T | P(y) }  ==> P(x)
```

Finite literals are lowered before validation, so `x in {a, b}` follows the
same `union` and `singleton` rules.

Subset is expanded to a universal implication:

```text
A subset B  ==>  forall x : T, x in A -> x in B
```

## `simp`

The `simp` tactic is intentionally small. It normalizes the current goal using
transparent formula definitions, set computation, subset expansion, and Nat
computation inside formula terms. `simp [lemma]` additionally uses listed term
equality theorems or local equality hypotheses as rewrite rules in the goal or
in hypothesis-targeted forms such as `simp [lemma] at h` and
`simp [local_eq] at *`. `simp at h` applies built-in normalization to a named
hypothesis in the local proof state, and `simp at *` normalizes the goal plus
all named hypotheses. All forms accept no-op calls but emit a warning note so
users notice when `simp` did not change anything.

Current design tradeoff:

- `simp` is predictable and easy to inspect.
- The theorem-driven part is explicit: users list equality rules in
  `simp [rule]`.
- There is no attribute-based global simp set or iff/proposition rewriting yet.
- Hypothesis simplification is explicit: either one named hypothesis or all
  hypotheses with `simp at *`, optionally with listed equality rules.

This keeps the implementation simple while still supporting useful examples.

## Equality and Rewrite

Equality proof objects use:

- `EqRefl`
- `EqSubst`

The tactic-facing `rewrite` is directional in an important way. If the equality
proof has type:

```text
left = right
```

then `rewrite <- h` expects the current goal to contain `right`. The tactic
creates a subgoal with that occurrence changed to `left`. Bare `rewrite h`
parses to the same right-to-left direction and remains supported for backward
compatibility, but docs and examples prefer the explicit arrow.

This supports examples like:

```text
theorem rewrite_happy
  : alice = mother(alice) -> Happy(alice) -> Happy(mother(alice)) := by
  intro h
  intro ha
  rewrite <- h
  exact ha
```

The target contains `mother(alice)`, the right side of `h`, so the subgoal
becomes `Happy(alice)`.

Use `rewrite -> h` for the reverse tactic direction. Compound proof expressions
such as `rewrite <- eq_symm h` are also accepted when schema arguments can be
inferred from the supplied proof arguments.

For a non-`all` rewrite with several matching occurrences, the checker keeps
the existing selection rule and records a warning note naming the occurrence it
chose. This makes accidental wrong-direction or wrong-occurrence rewrites
visible at the tactic line without rejecting an otherwise valid proof.

Use `rewrite all <- h` or `rewrite all -> h` to rewrite every matching
occurrence in the target. This form rejects expanding rewrites where the
replacement would introduce new occurrences of the term being rewritten.

## Natural-Number Induction

`NatInduction` is a proof object and `induction` is the tactic that builds it.

Current induction is specialized:

- It works over `Nat`.
- It expects a target that depends on the induction variable.
- It rejects local hypotheses that depend on the induction variable, because
  the current implementation does not generalize them.

The tactic form is:

```text
induction n with
| zero =>
    ...
| succ k ih =>
    ...
```

This is enough for the current Nat library:

- `add_zero_right`
- `add_succ_right`
- `add_assoc`
- `add_comm`

## Classical Reasoning

Classical proof use is explicit in proof objects:

```rust
DraftProof::Classical(ClassicalRule, Formula)
```

The current classical rules are:

- excluded middle
- proof by contradiction
- double-negation elimination

Tactics such as `by_cases` and `by_contra` create classical proof nodes.

Design benefit:

- The kernel can return whether a proof used classical reasoning.
- Constructive mode can reject classical proofs after elaboration.
- The CLI can report whether an accepted theorem is constructive or classical.

## Standard Library Design

The standard library is deliberately written in Cetacea rather than hard-coded
in Rust, except where a principle is intended to be trusted.

Files:

- `std/prop.ctea`
- `std/fol.ctea`
- `std/eq.ctea`
- `std/nat.ctea`
- `std/set.ctea`
- `std/list.ctea`
- `std/fun.ctea`
- `std/modular.ctea`
- `std/prelude.ctea`
- `std/qualified_prelude.ctea`

Notable trusted axiom:

```text
axiom set_ext
  (T : Type)
  (A B : Set T)
  : (forall x : T, x in A <-> x in B) -> A = B
```

Everything else in the current standard library is proved through the ordinary
checker.

The prelude is just an import file. It does not define new theorems itself.

## Tests

Most tests live at the bottom of `crates/cetacea_core/src/lib.rs`.

Test categories:

- standard library checks
- example checks
- positive propositional and FOL examples
- negative validation tests
- equality and rewrite tests
- set and Nat computation tests
- parser block regressions
- import behavior tests
- diagnostic location tests

Important philosophy: std and examples are checked by tests. This makes the
library and examples part of the regression suite.

## CLI Design

The CLI:

1. Reads a single path argument.
2. Calls `cetacea_core::check_file_at_path`.
3. If there are no diagnostics, prints accepted root-file declarations.
4. If there are diagnostics, prints each error and note.

The CLI filters out imported declarations using `CheckedTheorem::is_imported`.
This avoids overwhelming output when a user checks a small file that imports
the prelude.

With `--tui`, `--interactive`, or `-i`, the CLI starts a full-screen terminal
TUI. It uses raw terminal mode, an alternate screen, and ANSI drawing without
external terminal dependencies. The left pane is an editable source buffer; the
right pane can show cursor-sensitive goals, theorem outline, theorem search,
proof explanations, diagnostics, or help. The TUI re-checks the in-memory
buffer after cursor movement and edits using the source-at-path APIs, so import
resolution and diagnostics stay consistent with normal file checking.

With `--line`, the CLI starts the older line-oriented terminal shell. It reuses
the path-backed editor APIs for proof-state display, stepping, theorem search,
tactic hints, and proof explanations.

Native check mode first uses the legacy checker as a capability probe. If its
`CheckResult` reports that an exact logical package import requires HOL, the
CLI reruns the root and its transitive imports through the fail-closed sidecar
and discards the probe result. TUI buffer refreshes and line reloads use the
same signal to select package-aware full checks and goal analysis; replay
mismatches become editor diagnostics. This keeps package-free callers on the
existing path while avoiding diagnostic-text coupling: the core exposes an
explicit `requires_hol_shadow` result flag. `--hol-shadow` still forces dual
checking when no logical import is present.

Logical package dependencies are surface-aware. Importing
`std/hol/finite@1 as F` transactionally installs and exposes its List dependency
as `F.List`, `F.cons`, and the remaining List catalog, then adds `F.HasCard` and
the checked `F.has_card_intro` theorem. Source aliases share a namespace for
ergonomics, but registry records and receipt names continue to identify List
and finite declarations separately. Any dependency or owned-name collision
rolls the whole import back.

## Wasm And Web UI

The wasm crate is intentionally thin, mirroring the CLI. It exports:

- `cetacea_check`
- `cetacea_outline`
- `cetacea_goals_at`
- `cetacea_run_tactic`
- `cetacea_explain_theorem`

The exports accept UTF-8 strings through explicit `cetacea_alloc` /
`cetacea_free` memory helpers and return a length-prefixed JSON string. This
keeps the wasm crate dependency-free while still making the browser boundary
straightforward.

The wasm wrapper embeds the current standard library as virtual imports, so
browser sources can use paths such as `import std/prelude.ctea`,
`import std/qualified_prelude.ctea`, or the CS250-style
`import ../../../std/prelude.ctea` without filesystem access.

The Wasm dependency also enables the HOL compatibility sidecar. Full checks
are fail-closed dual checks: JSON reports `ok` only when legacy checking and a
complete mismatch-free HOL replay both succeed, and includes
`hol_certified`, exact logical package IDs, receipt IDs, least fragments, and
proof features. The virtual-import goal, step, and explanation exports use the
same package-aware state and certify a proof when stepping reaches its end.
Release builds use size-oriented LTO so this complete path remains below the
raw-Wasm review threshold.

The static UI in `web/` loads `cetacea_wasm.wasm`, renders diagnostics and
accepted declarations, and uses the goal-stepping APIs to show the current proof
state. Goal snapshots include rule-based tactic hints, and check results include
theorem statements for the searchable theorem-library panel. The proof
explanation panel calls `cetacea_explain_theorem` for the selected theorem and
renders the checked tactic trace as student-facing prose.

## Why the Language Is Small

Cetacea is not trying to be Lean, Coq, or Agda. The implementation favors:

- a small trusted checker
- explicit proof scripts
- readable proof objects
- enough automation to be usable
- enough syntax to demonstrate first-order reasoning

That explains several current choices:

- dot-qualified names, namespace blocks, and deliberately small import aliases
- no tactic language expressions
- no theorem-driven simplifier yet
- no dependent type theory
- no elaboration of arbitrary predicate expressions
- line-oriented parser

The upside is that nearly every feature is inspectable in one file.

## How To Add a New Built-In Term

Suppose you wanted to add a new Nat primitive, such as maximum.

Likely steps:

1. Add a `Term` variant for the primitive.
2. Update `Display for Term`.
3. Update term validation in `validate_term`.
4. Update substitution and free-variable helpers for terms.
5. Update term normalization if it computes.
6. Update term size and rewrite traversal helpers.
7. Update the parser in `Tokens::parse_term`.
8. Add tests for parsing, validation, computation, and proof use.
9. Add standard-library theorems in `std/nat.ctea`.

Because built-ins are represented explicitly, every term traversal needs to
know about a new term variant.

## How To Add a New Formula Form

A new formula form is larger than a new term form.

Likely steps:

1. Add a `Formula` variant.
2. Update `Display for Formula`.
3. Update precedence if it has syntax.
4. Update parser support.
5. Update `validate_formula`.
6. Update substitution and free-variable helpers.
7. Update normalization and definitional equality.
8. Update formula size and rewrite traversal helpers.
9. Add proof-object rules if it has logical meaning.
10. Add tactic support if users need a tactic for it.
11. Add tests.

For many connectives, it may be better to encode them in existing forms. For
example, `<->` is currently encoded as conjunction of implications instead of a
new formula variant.

## How To Add a New Tactic

A new tactic generally touches:

1. The `Tactic` enum.
2. `parse_tactic_line` or `parse_tactic_lines`.
3. `apply_tactic` or the relevant tactic execution code.
4. `PartialProof` only if the tactic needs a new proof-building shape.
5. Tests for success and failure.

When possible, a tactic should elaborate to existing proof objects. Add a new
proof object only when the kernel needs a genuinely new rule.

Good tactic design in Cetacea means:

- it should fail with a clear message when the target shape is wrong
- it should validate any supplied proof expression early
- it should leave the kernel responsible for final soundness
- it should produce predictable subgoals

## How To Improve Theorem Instantiation

The current system supports both inferred and explicit schema substitution.
Inference uses the expected goal and, for `apply`, matching local hypotheses
plus simple implication/conjunction consequences of those hypotheses. It is
still intentionally limited. Improving it further likely means working in the
schema-matching and theorem-reference code rather than the parser.

Useful future improvements:

- infer more term parameters from equality and predicate positions
- produce better messages when only one schema argument is missing
- explain which theorem parameter could not be inferred
- add backtracking when several local hypotheses could instantiate the same
  missing theorem parameter

This would make library proofs shorter without changing the kernel.

## How To Improve Diagnostics

The current diagnostics know command line numbers, parse errors in tactic
blocks know the offending tactic line, and execution-time tactic failures report
the failing tactic line. Parser errors carry token spans where possible.
Checked declarations and execution-time tactic failures do not yet carry exact
AST or tactic spans within the line.

Useful next steps:

1. Preserve spans in AST nodes.
2. Render spans in the CLI with caret ranges.
3. Include a compact proof state when tactic execution fails.

The existing `Span` field in `Diagnostic` is a placeholder for this direction.

## Known Architectural Limitations

Important limitations to account for when extending the system:

- Unaliased imports are legacy global imports; aliased imports expose imported
  declarations under the alias namespace.
- Dot-qualified top-level names and namespace blocks are accepted. Namespace
  blocks prefix declarations and resolve sibling top-level references through
  the current namespace, but Cetacea still does not have a full module system
  with private exports or `open` scopes.
- Remaining namespace migration work is tracked in
  [`docs/NAMESPACE_DESIGN.md`](NAMESPACE_DESIGN.md); qualified names affect
  the parser, environment lookup, imports, theorem search, and proof
  projections.
- The parser is line-oriented and only parse errors carry token spans.
- Formula and term definitions are transparent and simple.
- Recursive definitions are limited to unary primitive recursion over `Nat`.
- Predicate lambdas are intentionally first-order and are only accepted where a
  predicate argument is expected.
- `simp` has explicit equality rewrite rules, but no global simp attribute set.
- Nat induction is specialized and not fully generalized.
- The standard library contains an explicit trusted set-extensionality axiom.

These are acceptable for the current project size, but they should be revisited
if the language grows.

## Good Maintenance Practices

When changing Cetacea:

- Add a minimal positive test.
- Add a failure test if the feature has validation or mode restrictions.
- Check all standard-library files.
- Check all examples.
- Keep the kernel smaller than the tactic layer.
- Prefer adding theorem-library lemmas over hard-coding logic in Rust.
- Only add Rust built-ins when computation or typechecking genuinely needs
  built-in knowledge.

The usual verification command is:

```sh
cargo test
cargo clippy --all-targets -- -D warnings
cargo build
for f in std/*.ctea examples/*.ctea; do target/debug/cetacea_cli "$f" >/tmp/cetacea-cli-check.out; done
```

## Reading Order For New Contributors

Recommended order:

1. Read `docs/USAGE.md`.
2. Run `cargo test`.
3. Check `examples/imports.ctea`.
4. Read `std/prop.ctea` and `std/fol.ctea`.
5. Read the AST definitions at the top of `crates/cetacea_core/src/lib.rs`.
6. Read `check_file_at_path` and `FileChecker`.
7. Read the parser near `parse_file`.
8. Read tactic elaboration around `prove`.
9. Read the kernel functions `infer_proof` and `check_proof`.
10. Read tests at the bottom of the file.

That path moves from user-facing behavior into internal machinery without
starting in the densest part of the code.
