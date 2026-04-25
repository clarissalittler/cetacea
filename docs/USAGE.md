# Cetacea User Guide

This guide explains how to write and check Cetacea files. It is written for
someone who wants to use the language, read the standard library, and write new
proofs without first studying the Rust implementation.

Cetacea is a small tactic-based theorem prover. A Cetacea file contains
declarations, theorem statements, and tactic scripts. The checker elaborates
the tactic script into a proof object and then checks that proof object against
the theorem statement.

## Running Cetacea

Build and test the project with Cargo:

```sh
cargo test
cargo build
```

Check a file with the CLI:

```sh
cargo run -p cetacea_cli -- examples/imports.ctea
```

After building, the compiled binary can be run directly:

```sh
target/debug/cetacea_cli examples/imports.ctea
```

The CLI prints accepted declarations from the root file. Imported declarations
are checked and loaded, but they are not printed as part of the importing file's
summary.

For example:

```text
accepted theorem imported_imp_trans (constructive)
accepted theorem imported_forall_mono (constructive)
accepted theorem imported_exists_mono (constructive)
accepted theorem imported_add_comm (constructive)
accepted theorem imported_subset_trans (constructive)
```

If a file has only imports, the CLI prints:

```text
accepted file
```

Diagnostics include the file and command line when the checker was given a file
path:

```text
error: /tmp/cetacea-bad.ctea:3: theorem `bad` failed: no matching assumption found
  note: target: P
```

## File Shape

A typical file starts with imports, chooses a logic mode, declares any domain
symbols it needs, and then states theorems.

```text
import ../std/prelude.ctea

mode constructive

sort Person

pred Student(Person)
pred Enrolled(Person)

theorem promote_all
  : (forall x : Person, Student(x) -> Enrolled(x))
    -> (forall x : Person, Student(x))
    -> forall x : Person, Enrolled(x) := by
  exact forall_mono {A := Person; P := Student; Q := Enrolled}
```

Blank lines are ignored. Comments start with `--` and run to the end of the
line.

## Imports

Import another Cetacea file with:

```text
import ../std/prelude.ctea
```

Import paths are resolved relative to the importing file first, then relative
to the current working directory. A file imported more than once is loaded once,
so it is safe for several files to import a shared library.

The standard prelude imports the current library files:

```text
import prop.ctea
import fol.ctea
import eq.ctea
import nat.ctea
import set.ctea
```

Use the prelude when you want the common propositional, first-order, equality,
Nat, and set lemmas:

```text
import ../std/prelude.ctea
```

Import modes do not leak into the importing file. If an imported file switches
to `mode classical`, your file still starts in constructive mode unless it says
otherwise.

## Logic Modes

Cetacea has two modes:

```text
mode constructive
mode classical
```

Constructive mode is the default. In constructive mode, proofs that use
classical rules are rejected. Classical mode permits:

- `by_cases`
- `by_contra`
- imported classical theorems such as `em` or `dne`

The checker also records the strongest mode actually used by a proof. A theorem
declared in classical mode can still be reported as constructive if the proof
uses only constructive rules.

Example:

```text
mode classical

theorem still_constructive (P : Prop) : P -> P := by
  intro h
  exact h
```

This proof is accepted as constructive because it does not use classical
reasoning.

## Types and Terms

Cetacea has a small first-order type language.

Built-in types:

- `Nat`
- `Set T`

User-defined first-order sorts:

```text
sort Person
sort Course
```

Type parameters in theorems:

```text
theorem id_for_any_type
  (A : Type)
  (P : A -> Prop)
  : (forall x : A, P(x)) -> forall x : A, P(x) := by
  intro h
  exact h
```

Term constants:

```text
const alice : Person
```

Functions:

```text
func mother : Person -> Person
func add_course : Person -> Course -> Person
```

Predicate declarations:

```text
pred Student(Person)
pred Takes(Person, Course)
```

Predicate parameters in theorem declarations use arrow notation:

```text
theorem forall_mono
  (A : Type)
  (P Q : A -> Prop)
  : (forall x : A, P(x) -> Q(x)) -> (forall x : A, P(x)) -> forall x : A, Q(x) := by
  ...
```

Built-in Nat terms:

```text
0
succ(n)
add(n, m)
```

Built-in set terms:

```text
empty(T)
singleton(x)
union(A, B)
inter(A, B)
diff(A, B)
```

The checker validates arities and types for functions, predicates, membership,
subset, and set operations.

## Formulas

Cetacea supports:

```text
True
False
P
Student(alice)
x = y
x in A
A subset B
not P
P /\ Q
P \/ Q
P -> Q
P <-> Q
forall x : T, P(x)
exists x : T, P(x)
```

`not P` is represented as `P -> False`.

`P <-> Q` is parsed as:

```text
(P -> Q) /\ (Q -> P)
```

This is useful in set extensionality proofs:

```text
axiom set_ext
  (T : Type)
  (A B : Set T)
  : (forall x : T, x in A <-> x in B) -> A = B
```

## Definitions

Formula definitions are transparent. They can be unfolded explicitly with
`unfold`, and `simp` can unfold them when that helps.

```text
def HappyMother (x : Person) : Prop := Happy(mother(x))

theorem happy_mother_def_intro : Happy(mother(alice)) -> HappyMother(alice) := by
  intro h
  unfold HappyMother
  exact h
```

Formula definitions currently support type and term parameters. They do not yet
support proposition or predicate parameters.

## Theorems

The general shape is:

```text
theorem name
  (parameter : Kind)
  : statement := by
  tactic
  tactic
```

Small theorem:

```text
theorem and_comm (P Q : Prop) : P /\ Q -> Q /\ P := by
  intro h
  split
  exact h.right
  exact h.left
```

The theorem parameters become schema variables. A theorem can quantify over:

- propositions: `(P : Prop)`
- types: `(A : Type)`
- predicates: `(P : A -> Prop)`
- terms: `(x : A)`

## Axioms

Axioms add trusted declarations to the environment. They have theorem-like
statements, but no proof.

```text
axiom set_ext
  (T : Type)
  (A B : Set T)
  : (forall x : T, x in A <-> x in B) -> A = B
```

Use axioms sparingly. They are trusted by the checker.

## Proof State Mental Model

A tactic script operates on a list of goals. Each goal has:

- a context of hypotheses and local variables
- a target formula to prove

Tactics either solve the current goal or replace it with subgoals. For example,
`split` on a conjunction target creates one goal for the left side and one goal
for the right side.

```text
theorem and_intro (P Q : Prop) : P -> Q -> P /\ Q := by
  intro hp
  intro hq
  split
  exact hp
  exact hq
```

After `split`, `exact hp` solves the first goal and `exact hq` solves the
second.

## Core Tactics

### `intro`

Use `intro name` for implication and universal quantification.

For implication:

```text
theorem id (P : Prop) : P -> P := by
  intro h
  exact h
```

For universal quantification:

```text
theorem forall_self
  (A : Type)
  (P : A -> Prop)
  : (forall x : A, P(x)) -> forall x : A, P(x) := by
  intro h
  intro x
  exact h x
```

### `exact`

Use `exact proof_expr` when a hypothesis or theorem has exactly the target
formula, or can be instantiated to it.

```text
theorem use_id (Q : Prop) : Q -> Q := by
  exact id
```

`exact` can use projections and forall application:

```text
exact h.left
exact h.right
exact h x
```

### `assumption`

`assumption` searches the local context for a hypothesis matching the target.

```text
theorem id_assumption (P : Prop) : P -> P := by
  intro h
  assumption
```

### `apply`

`apply proof_expr` uses an implication or universally quantified theorem to
reduce the current goal to its premises.

```text
theorem imp_trans (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R := by
  intro hpq
  intro hqr
  intro hp
  apply hqr
  apply hpq
  exact hp
```

`apply` can also instantiate universally quantified hypotheses:

```text
theorem forall_apply
  (A : Type)
  (P Q : A -> Prop)
  (a : A)
  : (forall x : A, P(x) -> Q(x)) -> P(a) -> Q(a) := by
  intro h
  intro hp
  apply h
  exact hp
```

### `split`

Use `split` to prove conjunctions and biconditionals. Since `<->` parses as a
conjunction of two implications, `split` is the usual way to prove `<->`.

```text
theorem and_intro (P Q : Prop) : P -> Q -> P /\ Q := by
  intro hp
  intro hq
  split
  exact hp
  exact hq
```

### `left` and `right`

Use `left` or `right` to prove a disjunction.

```text
theorem or_left (P Q : Prop) : P -> P \/ Q := by
  intro hp
  left
  exact hp
```

```text
theorem or_right (P Q : Prop) : Q -> P \/ Q := by
  intro hq
  right
  exact hq
```

### `cases`

Use `cases` to eliminate disjunctions and existentials.

For disjunction:

```text
theorem or_comm (P Q : Prop) : P \/ Q -> Q \/ P := by
  intro h
  cases h with
  | left hp =>
      right
      exact hp
  | right hq =>
      left
      exact hq
```

For existential:

```text
theorem exists_and_left
  (A : Type)
  (P Q : A -> Prop)
  : (exists x : A, P(x) /\ Q(x)) -> exists x : A, P(x) := by
  intro h
  cases h with
  | intro x hx =>
      exists x
      exact hx.left
```

Case body indentation matters. The body of a case arm is the indented block
under `| left ... =>`, `| right ... =>`, or `| intro ... =>`.

### `exists`

Use `exists term` to prove an existential.

```text
theorem student_exists : Student(alice) -> exists x : Person, Student(x) := by
  intro h
  exists alice
  exact h
```

### `refl`

Use `refl` to prove equality whose two sides are definitionally equal after
computation.

```text
theorem add_zero_left (n : Nat) : add(0, n) = n := by
  simp
  refl
```

### `rewrite`

Use `rewrite h` when `h` proves an equality and the target contains the right
side of that equality. The tactic creates a subgoal where one occurrence has
been rewritten back to the left side.

```text
theorem rewrite_happy
  : alice = mother(alice) -> Happy(alice) -> Happy(mother(alice)) := by
  intro h
  intro ha
  rewrite h
  exact ha
```

Here the target is `Happy(mother(alice))`, and `h` is
`alice = mother(alice)`. `rewrite h` changes the subgoal to `Happy(alice)`.

For theorem schemas, explicit instantiation is sometimes needed:

```text
rewrite add_zero_right {n := m}
```

### `unfold`

Use `unfold Name` to unfold a transparent formula definition in the goal.

```text
theorem happy_mother_def_intro : Happy(mother(alice)) -> HappyMother(alice) := by
  intro h
  unfold HappyMother
  exact h
```

### `simp`

`simp` performs built-in computation and transparent definition unfolding when
it makes progress.

It currently knows:

- formula definitions
- set membership in `empty`, `singleton`, `union`, `inter`, and `diff`
- subset expansion
- the left-recursive equations for `add`

Examples:

```text
theorem singleton_member : alice in singleton(alice) := by
  simp
  refl
```

```text
theorem subset_refl
  (T : Type)
  (A : Set T)
  : A subset A := by
  simp
  intro x
  intro hx
  exact hx
```

### `induction`

Use `induction n with` for natural-number induction.

```text
theorem add_zero_right (n : Nat) : add(n, 0) = n := by
  induction n with
  | zero =>
      simp
      refl
  | succ k ih =>
      simp
      rewrite ih
      refl
```

The zero and successor arm bodies are indented. In the successor arm, `k` is
the predecessor variable and `ih` is the induction hypothesis.

The checker rejects induction if a local hypothesis depends on the induction
variable, because the current induction rule does not generalize such
hypotheses.

### `exfalso` and `contradiction`

Use `exfalso` to change any goal into a goal of `False`.

Use `contradiction` when the context contains either:

- a proof of `False`
- both a proposition and its negation

```text
theorem false_elim (P : Prop) : False -> P := by
  intro h
  contradiction
```

### `by_cases`

Classical case split:

```text
mode classical

theorem em (P : Prop) : P \/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h
```

`by_cases h : P` creates two goals. In the first, `h : P`. In the second,
`h : not P`.

### `by_contra`

Classical proof by contradiction:

```text
mode classical

theorem dne (P : Prop) : not not P -> P := by
  intro hnn
  by_contra hn
  apply hnn
  exact hn
```

`by_contra hn` changes the target `P` into a goal of `False` and adds
`hn : not P`.

## Proof Expressions

Many tactics take a proof expression.

Hypothesis or theorem:

```text
exact h
exact imp_trans
```

Projection from conjunction:

```text
exact h.left
exact h.right
exact h.left.right
```

Forall application:

```text
exact h x
apply h x
```

Explicit theorem instantiation:

```text
exact forall_mono {A := Person; P := Student; Q := Enrolled}
rewrite add_zero_right {n := m}
```

Explicit arguments are written in braces and separated by semicolons. The
values are parsed according to the parameter kind:

- type parameters, such as `A := Person`
- proposition parameters, such as `P := P /\ Q`
- predicate parameters, such as `P := Student`
- term parameters, such as `x := alice`

Cetacea can infer many schema arguments from the goal, especially for bare
theorem references in `exact` and `apply`. When inference fails, use explicit
arguments.

## Standard Library

The standard library is in `std/`.

### `std/prop.ctea`

Includes basic propositional lemmas:

- `id`
- `false_elim`
- `imp_trans`
- `imp_swap`
- `modus_tollens`
- `and_left`
- `and_right`
- `and_intro`
- `and_comm`
- `and_assoc_left`
- `and_assoc_right`
- `or_comm`
- `or_assoc_left`
- `or_assoc_right`
- `or_elim`
- `not_not_em`
- classical `em`
- classical `dne`

### `std/fol.ctea`

Includes first-order quantifier lemmas:

- `forall_and_left`
- `forall_and_right`
- `forall_and_intro`
- `forall_mono`
- `exists_and_left`
- `exists_and_right`
- `exists_or_left`
- `exists_or_right`
- `exists_mono`
- `not_exists_to_forall_not`
- `forall_not_to_not_exists`
- `forall_apply`

### `std/eq.ctea`

Includes equality lemmas:

- `eq_symm`
- `eq_trans`
- `congr_pred`
- `congr_pred2_left`
- `congr_pred2_right`
- `eq_subst_left`
- `eq_subst_right`

### `std/nat.ctea`

Includes basic Nat addition lemmas:

- `add_zero_left`
- `add_succ_left`
- `add_zero_right`
- `add_zero_right_rev`
- `add_succ_right`
- `add_succ_right_rev`
- `add_assoc`
- `add_comm`

### `std/set.ctea`

Includes set extensionality as an axiom plus set lemmas:

- `set_ext`
- `subset_refl`
- `subset_trans`
- `subset_antisymm`
- `empty_subset`
- `inter_subset_left`
- `inter_subset_right`
- `subset_union_left`
- `subset_union_right`
- `union_subset`
- `diff_subset_left`
- `diff_disjoint_right`
- `union_comm`
- `union_assoc_left`
- `union_empty_left`
- `union_empty_right`
- `inter_comm`
- `inter_assoc_left`
- `inter_empty_left`
- `inter_empty_right`

## Working Example

This example imports the prelude, declares a domain, and reuses standard lemmas.

```text
import ../std/prelude.ctea

mode constructive

sort Person

pred Student(Person)
pred Enrolled(Person)

theorem imported_forall_mono
  : (forall x : Person, Student(x) -> Enrolled(x))
    -> (forall x : Person, Student(x))
    -> forall x : Person, Enrolled(x) := by
  exact forall_mono {A := Person; P := Student; Q := Enrolled}
```

Check it with:

```sh
cargo run -p cetacea_cli -- examples/imports.ctea
```

## Common Patterns

### Prove a conjunction

```text
split
exact proof_of_left
exact proof_of_right
```

### Use a conjunction

```text
exact h.left
exact h.right
```

### Prove a disjunction

```text
left
exact proof_of_left
```

or:

```text
right
exact proof_of_right
```

### Use a disjunction

```text
cases h with
| left hp =>
    ...
| right hq =>
    ...
```

### Prove a universal statement

```text
intro x
...
```

### Use a universal statement

```text
exact h x
apply h
```

### Prove an existential statement

```text
exists witness
exact proof_for_witness
```

### Use an existential statement

```text
cases h with
| intro x hx =>
    ...
```

### Prove set equality

Use `set_ext`, introduce an arbitrary element, simplify membership, and prove
both directions.

```text
theorem union_comm
  (T : Type)
  (A B : Set T)
  : union(A, B) = union(B, A) := by
  apply set_ext
  intro x
  simp
  split
  intro hx
  cases hx with
  | left hxA =>
      right
      exact hxA
  | right hxB =>
      left
      exact hxB
  intro hx
  cases hx with
  | left hxB =>
      right
      exact hxB
  | right hxA =>
      left
      exact hxA
```

### Prove Nat facts by induction

Use `simp` in each branch to expose computation equations.

```text
theorem add_succ_right (n m : Nat) : add(n, succ(m)) = succ(add(n, m)) := by
  induction n with
  | zero =>
      simp
      refl
  | succ k ih =>
      simp
      rewrite ih
      refl
```

## Current Limitations

Cetacea is intentionally small. Important current limitations:

- There are no namespaces or qualified imports.
- Imported declarations enter one global environment.
- The parser is line-oriented and intentionally simple.
- Precise source spans are not implemented yet. Diagnostics report command
  lines, not exact tactic or token spans.
- `simp` uses built-in computation rules and formula definitions. It does not
  yet use arbitrary imported rewrite lemmas.
- Theorem instantiation is useful but incomplete. Some proofs still need
  explicit schema arguments.
- Formula definitions cannot currently take proposition or predicate
  parameters.
- Nat induction is specialized to `Nat` and rejects induction when local
  hypotheses depend on the induction variable.

## Debugging Failed Proofs

When a proof fails:

1. Read the target note in the diagnostic.
2. Check whether the failing theorem is in constructive or classical mode.
3. If a theorem reference cannot be instantiated, add explicit arguments.
4. If a `rewrite` fails, remember that the target must contain the equality's
   right-hand side.
5. If a `cases` or `induction` block behaves oddly, check indentation.
6. Try replacing `exact theorem_name` with explicit steps using `intro`,
   `apply`, `split`, and `cases`.

## Style Conventions

The current examples and standard library follow these conventions:

- Put imports first.
- Put `mode constructive` explicitly in ordinary files.
- Use short hypothesis names such as `h`, `hp`, `hx`, `ih`.
- Use longer names for theorem-level assumptions, such as `hAB` or `hpq`.
- Indent case and induction branch bodies by four spaces under the arm.
- Prefer importing `std/prelude.ctea` in examples that use the library.
- Use explicit theorem instantiation when it makes a proof more predictable.

