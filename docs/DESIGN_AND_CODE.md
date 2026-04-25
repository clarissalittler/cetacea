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
pub fn check_proof(
    env: &Env,
    ctx: &Context,
    proof: &Proof,
    expected: &Formula,
    allowed_mode: LogicMode,
) -> Result<LogicMode, KernelError>
pub fn infer_proof(
    env: &Env,
    ctx: &Context,
    proof: &Proof,
    allowed_mode: LogicMode,
) -> Result<CheckedProof, KernelError>
```

Use `check_file` for in-memory source strings. It can parse import declarations,
but relative imports are resolved relative to the current working directory
because there is no root path.

Use `check_file_at_path` for real files. This is what the CLI uses. It supports
imports relative to the importing file.

`check_proof` and `infer_proof` are the lower-level kernel-facing APIs. Most
callers should not need them directly unless they are constructing proof
objects programmatically.

## Core ASTs

### Types

`Type` represents first-order types:

```rust
pub enum Type {
    Named(Name),
    Nat,
    Set(Box<Type>),
}
```

Design notes:

- `Named` is for user-declared sorts and type parameters.
- `Nat` is built in because natural-number induction and computation are built
  into the language.
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
    EmptySet(Type),
    Singleton(Box<Term>),
    Union(Box<Term>, Box<Term>),
    Inter(Box<Term>, Box<Term>),
    Diff(Box<Term>, Box<Term>),
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
    pub predicate_args: HashMap<Name, Name>,
}
```

Predicate schema arguments currently map to predicate names, not arbitrary
lambda expressions.

## Proof Objects

`Proof` is the kernel-level proof language:

```rust
pub enum Proof {
    Hyp(Name),
    TrueIntro,
    FalseElim { proof_false: Box<Proof>, target: Formula },
    AndIntro(Box<Proof>, Box<Proof>),
    AndElimLeft(Box<Proof>),
    AndElimRight(Box<Proof>),
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
}
```

Design notes:

- Proof objects are natural-deduction-style.
- Tactics do not directly prove theorems. They build these proof objects.
- The kernel checks the proof object afterward.
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

The environment is global for a checking session. Imports add declarations to
the same environment as the root file. There are no namespaces yet.

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
pub is_imported: bool
```

The CLI uses this to print only declarations from the root file. The imported
declarations are still available to later proofs.

## Diagnostics

Diagnostics are returned in `CheckResult`:

```rust
pub struct Diagnostic {
    pub span: Option<Span>,
    pub location: Option<SourceLocation>,
    pub message: String,
    pub notes: Vec<String>,
}
```

Current diagnostic design:

- `SourceLocation` reports an optional path and a command or parse-error line.
- `Span` exists but is not meaningfully populated yet.
- The parser stores line numbers on top-level commands via `LocatedCommand` and
  on raw tactic lines while parsing theorem bodies.
- Tactic execution errors attach the current open goal as the diagnostic target
  note.
- The CLI prints `path:line: message` when location information exists.

This is a pragmatic halfway point. It helps users find failing declarations
without requiring a fully span-aware parser.

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
- explicit arguments in `{...}`
- forall application with term arguments
- implication application with proof arguments
- `.left` and `.right` projections

For theorem references with inline arguments, elaboration can infer schema
arguments from supplied proof arguments before building the final `TheoremRef`.
This supports expressions such as `rewrite eq_symm h`.

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
rewrite h
unfold Name
simp
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

The kernel is implemented by:

```rust
pub fn infer_proof(...)
pub fn check_proof(...)
```

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
- `normalize_term`
- `normalize_term_compute`
- formula/term substitution helpers
- formula equality helpers

Transparent definitions let users write:

```text
def HappyMother (x : Person) : Prop := Happy(mother(x))
```

and then prove goals involving `HappyMother(alice)` by unfolding or simplifying
to `Happy(mother(alice))`.

Term definitions support named set builders:

```text
def TallSet : Set Person := { x : Person | Tall(x) }
```

Built-in term computation currently focuses on Nat addition and multiplication:

```text
add(0, n)         ==> n
add(succ(n), m)  ==> succ(add(n, m))
mul(0, n)         ==> 0
mul(succ(n), m)  ==> add(m, mul(n, m))
```

This computation is applied recursively to terms, including terms nested under
function and predicate arguments.

Set simplification is mostly formula-level. Membership in set constructors is
expanded:

```text
x in empty(T)      ==> False
x in singleton(y)  ==> x = y
x in union(A, B)   ==> x in A \/ x in B
x in inter(A, B)   ==> x in A /\ x in B
x in diff(A, B)    ==> x in A /\ not x in B
x in { y : T | P(y) }  ==> P(x)
```

Subset is expanded to a universal implication:

```text
A subset B  ==>  forall x : T, x in A -> x in B
```

## `simp`

The `simp` tactic is intentionally small. It normalizes the current goal using
transparent formula definitions, set computation, subset expansion, and Nat
computation inside formula terms. It rejects no-op calls so users notice when
`simp` did not change anything.

Current design tradeoff:

- `simp` is predictable and easy to inspect.
- It is not yet a theorem-driven simplifier.
- It does not simplify hypotheses.

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

then the current goal must contain `right`. The tactic creates a subgoal with
that occurrence changed to `left`.

This supports examples like:

```text
theorem rewrite_happy
  : alice = mother(alice) -> Happy(alice) -> Happy(mother(alice)) := by
  intro h
  intro ha
  rewrite h
  exact ha
```

The target contains `mother(alice)`, the right side of `h`, so the subgoal
becomes `Happy(alice)`.

Use `rewrite -> h` for the reverse tactic direction. Compound proof expressions
such as `rewrite eq_symm h` are also accepted when schema arguments can be
inferred from the supplied proof arguments.

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
Proof::Classical(ClassicalRule, Formula)
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
- `std/prelude.ctea`

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

## Why the Language Is Small

Cetacea is not trying to be Lean, Coq, or Agda. The implementation favors:

- a small trusted checker
- explicit proof scripts
- readable proof objects
- enough automation to be usable
- enough syntax to demonstrate first-order reasoning

That explains several current choices:

- no namespaces yet
- no tactic language expressions
- no theorem-driven simplifier yet
- no dependent type theory
- no elaboration of arbitrary predicate expressions
- line-oriented parser

The upside is that nearly every feature is inspectable in one file.

## How To Add a New Built-In Term

Suppose you wanted to add a new Nat primitive, such as subtraction.

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
Inference is intentionally limited. Improving it likely means working in the
schema-matching and theorem-reference code rather than the parser.

Useful future improvements:

- infer more term parameters from equality and predicate positions
- produce better messages when only one schema argument is missing
- explain which theorem parameter could not be inferred
- use expected goal shape more aggressively in `apply`
- avoid requiring explicit arguments in common Nat rewrite lemmas

This would make library proofs shorter without changing the kernel.

## How To Improve Diagnostics

The current diagnostics know command line numbers, and parse errors in tactic
blocks know the offending tactic line. They do not yet know exact token spans
or execution-time tactic spans.

Useful next steps:

1. Give parse tokens byte spans.
2. Preserve spans in AST nodes.
3. Store tactic line numbers inside `Tactic`.
4. Report the failing execution-time tactic line, not just the theorem line.
5. Include a compact proof state when tactic execution fails.

The existing `Span` field in `Diagnostic` is a placeholder for this direction.

## Known Architectural Limitations

Important limitations to account for when extending the system:

- Imports are global and unqualified.
- There are no namespaces.
- The parser is not a full grammar with spans.
- Formula and term definitions are transparent and simple.
- Term definitions do not support parameters.
- Predicate schema arguments are names, not arbitrary predicates.
- `simp` is not theorem-driven.
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
