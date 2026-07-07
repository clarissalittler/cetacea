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

Start the full-screen terminal TUI with:

```sh
cargo run -p cetacea_cli -- --tui examples/prop.ctea
```

`--interactive` and `-i` are aliases for `--tui`.

Inside the TUI, the left pane is an editable source buffer and the right pane
shows information about the cursor position. Move with the arrow keys and type
to edit. The goal pane updates as the cursor moves through a proof script.
Use `m` to open the command menu, `F2` for the theorem outline, `F3` for
theorem search, `F4` for proof explanations, `F5` for diagnostics, `Ctrl-S` to
save, `Ctrl-R` to reload from disk, and `Ctrl-Q` to quit.

The older line-oriented terminal shell remains available with:

```sh
cargo run -p cetacea_cli -- --line examples/prop.ctea
```

Inside line mode, use `help` to see commands. The main commands are `theorems`,
`select <name|number>`, `reset`, `step`, `goals <line> [column]`, `hints`,
`search <text>`, and `explain [theorem]`.

After building, the compiled binary can be run directly:

```sh
target/debug/cetacea_cli examples/imports.ctea
```

Run the browser UI from the repository root:

```sh
rustup target add wasm32-unknown-unknown
cargo build -p cetacea_wasm --target wasm32-unknown-unknown --release
python3 -m http.server 8000
```

Then open:

```text
http://localhost:8000/web/
```

The browser build embeds the standard library for virtual imports, so tutorial
sources can still use imports such as `import std/prelude.ctea` or
`import ../../../std/prelude.ctea`.

The browser UI also shows the current proof goals, rule-based tactic hints for
each open goal, diagnostic repair suggestions, a searchable theorem-library
panel populated by the checked source and imported standard library, and a
line-by-line proof explanation for the selected theorem. Tactic hints are
speculatively executed before they are shown, so suggestions that would fail
are dropped. The editor autosaves to localStorage, re-checks as you type,
marks error lines inline, and has a load-example menu.

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

Accepted lines are printed for every passing theorem even when other theorems
in the file fail, so one broken proof does not hide the status of the rest of
the file.

A proof that depends on axioms, directly or through other theorems it uses,
lists those axioms:

```text
accepted theorem length_append (constructive; axioms: append_cons, append_nil)
```

A proof that uses the `sorry` tactic, or a theorem whose proof does, is
accepted but flagged as incomplete:

```text
accepted theorem homework_gap (constructive; incomplete: uses sorry)
```

If a file has only imports, the CLI prints:

```text
accepted file
```

Diagnostics include the file and command or tactic line when the checker was
given a file path:

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
import list.ctea
import fun.ctea
```

Use the prelude when you want the common propositional, first-order, equality,
Nat, set, list, and function-graph lemmas:

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

Predicate arguments can be declared predicate names or inline lambdas. A typed
lambda can infer a definition's type parameter:

```text
def Reflexive (T : Type) (R : T -> T -> Prop) : Prop := forall x : T, R(x, x)

theorem equality_reflexive : Reflexive(fun x y : Person => x = y) := by
  simp
  intro x
  refl
```

Lambda parameters must be distinct. They are substituted simultaneously, so
using names such as `x` and `y` in both the lambda and the surrounding theorem
is safe.

Built-in Nat terms:

```text
0
1
2
succ(n)
add(n, m)
mul(n, m)
sub(n, m)
```

Decimal Nat literals parse as repeated successors, so `2` is the same term as
`succ(succ(0))`.

`add` and `mul` simplify using both the left-recursive built-in equations and
the textbook right-recursive equations. In particular, `add(0, n)`,
`add(n, 0)`, `add(succ(n), m)`, `add(n, succ(m))`, `mul(0, n)`, and
`mul(n, 0)` all compute directly.
`sub` is truncated subtraction: `sub(n, 0)`, `sub(0, n)`, and
`sub(succ(n), succ(m))` simplify directly.

User-defined inductive data types use `data`:

```text
data Tree
| leaf
| node(Tree, Nat, Tree)
```

Each `|` line declares one constructor. A constructor without arguments, such
as `leaf`, becomes a constant of the data type. A constructor with arguments,
such as `node`, becomes a function. Argument types may mention the data type
itself; those recursive arguments are what structural induction and `defrec`
recurse on. Data types are monomorphic: there are no type parameters, so
`std/list.ctea`'s `List` is specifically a list of `Nat`.

User-defined recursive functions use `defrec`, over `Nat`:

```text
defrec double (n : Nat) : Nat
| zero => 0
| succ k rec => succ(succ(rec))
```

The zero arm gives the value at `0`. In the successor arm, `k` is the
predecessor and `rec` is the already-computed recursive result for `k`.
The simplifier reduces concrete calls such as `double(succ(succ(0)))` and
symbolic successor calls such as `double(succ(n))`.

`defrec` also works over declared data types, with one arm per constructor in
declaration order. In each arm, bind one name per constructor argument, then
one name per recursive argument for its already-computed recursive result, in
order:

```text
defrec size (t : Tree) : Nat
| leaf => 0
| node l v r recl recr => succ(add(recl, recr))
```

Here `l`, `v`, and `r` are the constructor arguments of `node`, and `recl` and
`recr` are `size(l)` and `size(r)`. Both `simp` and `refl` compute `defrec`
definitions.

`defrec` recurses on its first argument only, but additional fixed parameters
may follow it, which is enough for the usual binary operations:

```text
defrec append (l : List) (r : List) : List
| nil => r
| cons h t rec => cons(h, rec)
```

The extra parameters (`r` here) stay fixed through the recursion and are in
scope in every arm; `rec` abbreviates `append(t, r)`. Recursion on a later
argument or mutual recursion is not supported.

Built-in set terms:

```text
empty(T)
univ(T)
singleton(x)
{x, y, z}
union(A, B)
inter(A, B)
diff(A, B)
compl(A)
prod(A, B)
powerset(A)
{ x : T | P(x) }
```

Finite set literals such as `{x, y, z}` are shorthand for nested unions
of singletons. Empty finite-set literals are not supported because their
element type is ambiguous; use `empty(T)` instead.

`powerset(A)` has type `Set (Set T)` when `A : Set T`; membership
`B in powerset(A)` simplifies to `B subset A`.
`univ(T)` has type `Set T`, and `compl(A)` is the complement of `A`
inside its element type's universe. `complement(A)` is accepted as an
alias for `compl(A)`.
Cartesian products use ordered pairs: `pair(x, y)` has type `Prod T U`
when `x : T` and `y : U`; `fst(p)` and `snd(p)` project a pair; and
`prod(A, B)` has type `Set (Prod T U)` when `A : Set T` and `B : Set U`.

The checker validates arities and types for functions, predicates, membership,
subset, and set operations.

## Formulas

Cetacea supports:

```text
True
False
P
Student(alice)
le(n, m)
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
forall x y : T, R(x, y)
exists x y : T, R(x, y)
```

`not P` is represented as `P -> False`.

The usual Unicode symbols are accepted as aliases for the ASCII spellings:

| Unicode | ASCII |
|---|---|
| `∧` | `/\` |
| `∨` | `\/` |
| `¬` | `not` |
| `→` | `->` |
| `↔` | `<->` |
| `∀` | `forall` |
| `∃` | `exists` |
| `∈` | `in` |
| `⊆` | `subset` |

So `P ∧ Q → Q ∧ P` parses the same as `P /\ Q -> Q /\ P`. Other non-ASCII
characters are rejected with an error that points at the offending character.

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

Formula definitions support type, term, proposition, and predicate parameters:

```text
def ConjSelf (P : Prop) : Prop := P /\ P
def Reflexive (T : Type) (R : T -> T -> Prop) : Prop := forall x : T, R(x, x)
```

Term definitions are also transparent and can take type, term, proposition, and
predicate parameters. This is useful for naming set-builder expressions.

```text
def TallSet : Set Person := { x : Person | Tall(x) }
def LikesSet (y : Person) : Set Person := { x : Person | Likes(x, y) }
def TruthSet (T : Type) (P : T -> Prop) : Set T := { x : T | P(x) }

theorem tall_member : Tall(alice) -> alice in TallSet := by
  intro h
  simp
  exact h

theorem likes_member : Likes(alice, bob) -> alice in LikesSet(bob) := by
  intro h
  simp
  exact h
```

Primitive recursive Nat definitions are transparent to `simp`:

```text
defrec double (n : Nat) : Nat
| zero => 0
| succ k rec => succ(succ(rec))

theorem double_succ (n : Nat) : double(succ(n)) = succ(succ(double(n))) := by
  simp
  refl
```

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

It can also apply an implication proof inline, and `exact True` introduces
`True`:

```text
exact h hp
exact (h hp).left
exact True
```

### `trivial`

Use `trivial` to prove a `True` goal.

```text
theorem true_intro : True := by
  trivial
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

For transitive lemmas, `apply` can often infer the intermediate object from
local hypotheses:

```text
theorem subsets_carry
  (T : Type)
  (A B C : Set T)
  : A subset B -> C subset A -> C subset B := by
  intro hAB
  intro hCA
  apply subset_trans
  exact hCA
  exact hAB
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

Use `cases` to eliminate disjunctions, existentials, and conjunctions.

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

The `| intro a b =>` form also destructures a conjunction hypothesis, naming
the two halves:

```text
theorem and_comm_cases (P Q : Prop) : P /\ Q -> Q /\ P := by
  intro h
  cases h with
  | intro hp hq =>
      split
      exact hq
      exact hp
```

The binders in a `cases` arm must be fresh and distinct: reusing an existing
name, or the same name twice, is rejected.

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

The witness term is validated against the existential's bound type, so a
witness of the wrong type is reported at the tactic line, as in
``witness `0` has type `Nat`, but expected `Person` ``.

### `refl`

Use `refl` to prove equality whose two sides are definitionally equal after
computation. `refl` normalizes both sides itself, so pure computation goals
close in one step:

```text
theorem add_zero_left (n : Nat) : add(0, n) = n := by
  refl

theorem two_times_three : mul(2, 3) = 6 := by
  refl
```

This also covers `defrec` definitions, including `defrec` over data types.
Writing `simp` before `refl` still works and can be useful when you want to
see the simplified goal, but it is no longer required for computation.

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
Use `rewrite -> h` for the opposite direction, where the target contains the
left side and the new subgoal contains the right side.

Use `rewrite all h` to rewrite every matching occurrence in the target. To
keep this form finite and predictable, Cetacea rejects `rewrite all` when the
replacement would introduce new occurrences of the term being rewritten.

For theorems with parameters, explicit instantiation is sometimes needed:

```text
rewrite add_zero_right {n := m}
```

Compound proof expressions are allowed, so equality lemmas can be applied
inline:

```text
rewrite eq_symm h
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
- transparent term definitions
- primitive recursive Nat definitions declared with `defrec`
- set membership in `empty`, `univ`, `singleton`, `union`, `inter`,
  `diff`, `compl`, `prod`, `powerset`, and set builders
- subset expansion
- the built-in equations for `add`, `mul`, `sub`, and `le`, including inside
  predicate and function arguments

You can also provide equality theorems explicitly as rewrite rules:

```text
axiom mother_alice : mother(alice) = alice

theorem happy_mother : Happy(alice) -> Happy(mother(alice)) := by
  intro h
  simp [mother_alice]
  exact h
```

Use `simp at h` to simplify a named hypothesis in the local context, or
`simp at *` to simplify the current goal and all local hypotheses. Listed
equality rules can also target hypotheses: `simp [mother_alice] at h` and
`simp [mother_alice] at *`. The names in `simp [...]` may be top-level
equality theorems or local equality hypotheses introduced in the proof.

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

```text
pred Even(Nat)

theorem even_zero_to_simplified_arg : Even(0) -> Even(add(0, 0)) := by
  intro h
  simp
  exact h
```

```text
theorem inter_hyp_right
  (T : Type)
  (x : T)
  (A B : Set T)
  : x in inter(A, B) -> x in B := by
  intro h
  simp at h
  exact h.right
```

```text
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
```

### `induction`

Use `induction n with` for natural-number induction:

```text
theorem add_comm (n m : Nat) : add(n, m) = add(m, n) := by
  induction n with
  | zero =>
      simp
      refl
  | succ k ih =>
      simp
      rewrite ih
      refl
```

The arm bodies are indented. In the successor arm, `k` is the predecessor
variable and `ih` is the induction hypothesis.

`induction` also does structural induction over declared data types. Arms must
follow the constructor declaration order. Each arm binds one name per
constructor argument, then one induction hypothesis per recursive argument, in
order, after the constructor-argument binders:

```text
data Tree
| leaf
| node(Tree, Nat, Tree)

theorem mirror_size (t : Tree) : size(mirror(t)) = size(t) := by
  induction t with
  | leaf =>
      rewrite -> mirror_leaf
      refl
  | node l v r ihl ihr =>
      rewrite -> mirror_node {l := l; v := v; r := r}
      simp
      rewrite -> ihl
      rewrite -> ihr
      rewrite -> add_comm {n := size(l); m := size(r)}
      refl
```

Here `node` has two recursive arguments, so its arm binds two induction
hypotheses: `ihl` for `l` and `ihr` for `r`.

Induction binders must be fresh. Shadowing an existing variable or hypothesis
is rejected with `induction binder would shadow an existing variable`, and
this applies to the Nat `| succ k ih` binders as well.

The checker rejects induction if a local hypothesis depends on the induction
variable, because the current induction rule does not generalize such
hypotheses.

For strong (course-of-values) induction on `Nat`, use the library theorem
`strong_induction` from `std/nat.ctea`:

```text
strong_induction (P : Nat -> Prop) (n : Nat)
  : P(0)
    -> (forall k : Nat, (forall m : Nat, le(m, k) -> P(m)) -> P(succ(k)))
    -> P(n)
```

It is applied with an explicit predicate lambda, since `P` cannot be inferred
from the goal:

```text
theorem zero_le_all (n : Nat) : le(0, n) := by
  apply strong_induction {P := fun m : Nat => le(0, m); n := n}
  simp
  trivial
  intro k
  intro hk
  simp
  trivial
```

After the `apply`, the first goal is `P(0)` and the second is the step goal,
in which the strong hypothesis `hk` provides `P(m)` for every `m` with
`le(m, k)`. The library also provides `strong_induction_bounded`,
`le_zero_inv`, and `le_succ_inv`.

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

### `show_goal`

Use `show_goal` or `print_state` as a debugging tactic. It intentionally stops
the proof and reports the current open goal.

```text
theorem stuck (P : Prop) : P := by
  show_goal
```

### `sorry`

Use `sorry` (or its alias `admit`) to close any goal without proving it. The
theorem is accepted so the rest of the file can be checked, but it is reported
as incomplete:

```text
theorem homework_gap (P Q : Prop) : P /\ Q -> Q /\ P := by
  sorry
```

```text
accepted theorem homework_gap (constructive; incomplete: uses sorry)
```

Incompleteness propagates: a theorem whose proof uses a sorry'd theorem is
also reported as `incomplete: uses sorry`. This makes `sorry` safe to use for
homework skeletons — an instructor can distribute a file of stated theorems
with `sorry` bodies, and a submission is only fully proved when no accepted
line carries the incomplete flag.

### `have`

`have` states an intermediate fact, proves it (or takes a proof directly), and
makes it available as a named hypothesis for the rest of the proof:

```text
theorem chain (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R := by
  intro hpq
  intro hqr
  intro hp
  have hq : Q
  apply hpq
  exact hp
  apply hqr
  exact hq
```

`have hq : Q` opens `Q` as the next goal; once it is closed, the original goal
resumes with `hq : Q` in the context. When the proof is a single expression,
supply it directly and no extra goal is opened:

```text
have hq := h.right
have hp : P := h.left
```

The annotated form checks the expression against the stated formula and
reports a mismatch as `have proof has type ..., but the stated formula
is ...`. The name must be fresh; shadowing an existing hypothesis or variable
is rejected.

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

Implication application:

```text
exact h hp
exact (h hp).left
```

Projections and parenthesized sub-expressions also work inside arguments, and
projections bind tighter than application, so `f h.left` means `f (h.left)`:

```text
exact f h.left
exact f (h.left) (h.right)
rewrite -> hinj x y (h.left)
```

Explicit theorem instantiation:

```text
exact forall_mono {A := Person; P := Student; Q := Enrolled}
rewrite add_zero_right {n := m}
```

Explicit arguments are written in braces and separated by semicolons. They can
stay on one line or be wrapped across several tactic lines. The values are
parsed according to the parameter kind:

- type parameters, such as `A := Person`
- proposition parameters, such as `P := P /\ Q`
- predicate parameters, such as `P := Student` or `P := fun x => x = x`
- term parameters, such as `x := alice`

Cetacea can infer many theorem parameters from the goal, especially for bare
theorem references in `exact` and `apply`. For `apply`, it also uses local
hypotheses and simple implication/conjunction consequences of those hypotheses
to fill missing parameters. When inference fails, use explicit arguments.

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

Includes basic Nat addition, multiplication, subtraction, and order lemmas:

- `pred_zero`
- `pred_succ`
- `nat_congr_pred`
- `succ_inj`
- `add_zero_left`
- `add_succ_left`
- `add_zero_right`
- `add_zero_right_rev`
- `add_succ_right`
- `add_succ_right_rev`
- `add_assoc`
- `add_comm`
- `mul_zero_left`
- `mul_succ_left`
- `mul_zero_right`
- `mul_succ_right`
- `sub_zero_right`
- `sub_zero_left`
- `sub_succ_succ`
- `sub_self`
- `zero_le`
- `succ_not_le_zero`
- `le_succ_succ`
- `le_succ_succ_rev`
- `le_refl`
- `le_trans`
- `le_zero_inv`
- `le_succ_inv`
- `strong_induction_bounded`
- `strong_induction`

### `std/set.ctea`

Includes set extensionality as an axiom plus set lemmas:

- `set_ext`
- `subset_refl`
- `subset_trans`
- `powerset_intro`
- `powerset_elim`
- `powerset_mono`
- `subset_antisymm`
- `empty_subset`
- `subset_univ`
- `inter_subset_left`
- `inter_subset_right`
- `subset_union_left`
- `subset_union_right`
- `union_subset`
- `diff_subset_left`
- `diff_disjoint_right`
- `prod_member_intro`
- `prod_member_left`
- `prod_member_right`
- `prod_mono`
- `prod_empty_left`
- `prod_empty_right`
- `compl_intro`
- `compl_elim`
- `inter_univ_right`
- `inter_univ_left`
- `inter_compl_empty`
- `union_comm`
- `union_assoc_left`
- `union_empty_left`
- `union_empty_right`
- `inter_comm`
- `inter_assoc_left`
- `inter_empty_left`
- `inter_empty_right`

### `std/list.ctea`

Lists of natural numbers. Cetacea data types are monomorphic, so this is the
concrete list type used by the course examples:

- `data List` with constructors `nil` and `cons(Nat, List)`
- `length`, a `defrec` over `List`
- `length_nil`
- `length_cons`
- `append`, a binary `defrec` recursing on its first argument
- `append_nil` and `append_cons`, the recursion equations as theorems
- `length_append`
- `append_nil_length`
- `append_assoc`

Because `append` is a `defrec`, `simp` and `refl` compute it directly and no
axioms are involved.

### `std/fun.ctea`

Functions `f : A -> B` modeled by their graphs, following the
functions-as-relations treatment: a graph is a predicate
`G : A -> B -> Prop`, and `G(x, y)` means `f(x) = y`. For a declared
`func f : A -> B`, the graph is the lambda `fun x y : A => f(x) = y` (the
checker gives `y` its type `B` from context).

Definitions, each with parameters `(A : Type) (B : Type) (G : A -> B -> Prop)`:

- `Total`
- `SingleValued`
- `Injective`
- `Surjective`
- `Bijective`

Theorems:

- `id_injective`
- `id_surjective`
- `id_bijective`, stated with `Bijective(...)`, which unfolds to
  `Injective(...) /\ Surjective(...)`
- `compose_injective`
- `compose_surjective`

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
  simp
  refl
```

## Current Limitations

Cetacea is intentionally small. Important current limitations:

- There are no namespaces or qualified imports.
- Imported declarations enter one global environment.
- The parser is line-oriented and intentionally simple.
- Parse diagnostics carry line-local token spans where possible, but checked
  declaration and tactic execution errors still report line numbers rather than
  exact AST spans. Runtime tactic failures report the failing tactic line.
- `simp [lemma]` and `simp [h]` can use listed equality theorems or local
  equality hypotheses as rewrite rules, including in hypotheses with
  `simp [lemma] at h` or `simp [lemma] at *`, but there is not yet an
  attribute-based global simp set or iff/proposition rewriting.
- Theorem instantiation is useful but incomplete. Some underdetermined proofs
  still need explicit theorem parameters.
- Nat has addition, multiplication, truncated subtraction, and `le`, but no
  division, modular arithmetic, or decidable equality tactic.
- Data types are monomorphic: there are no type parameters, so there is no
  polymorphic `List A`.
- `defrec` recurses on its first argument, with optional fixed extra
  parameters; recursion on later arguments and mutual recursion are not
  supported.
- `induction` rejects induction when local hypotheses depend on the induction
  variable.
- `intro`, `cases` arm binders, and `induction` arm binders reject names that
  would shadow an existing local variable or hypothesis.

## Debugging Failed Proofs

When a proof fails and the statement, or the open goal together with its
hypotheses, is purely propositional and classically falsifiable, the error
includes a countermodel note:

```text
note: the statement is not a tautology: it is false when P = false, Q = true.
No proof can close it; check the statement itself.
```

or, when the statement is fine but an earlier step painted the proof into a
corner:

```text
note: the open goal does not follow from the current hypotheses: it is false
when P = true, Q = false. Reconsider the earlier proof steps.
```

The first note means no tactic script can ever succeed — the statement itself
is wrong. The second means the statement may be provable, but not from here;
back up and take a different step. The browser UI surfaces the same check as a
"Warning: this goal is not provable" hint in the Goals panel.

For everything else, when a proof fails:

1. Read the target note in the diagnostic.
2. Check whether the failing theorem is in constructive or classical mode.
3. If a theorem reference cannot be instantiated, add explicit arguments.
4. If a `rewrite` fails, remember that the target must contain the equality's
   right-hand side.
5. Insert `show_goal` temporarily to see the current open goal.
6. If a `cases` or `induction` block behaves oddly, check indentation.
7. Try replacing `exact theorem_name` with explicit steps using `intro`,
   `apply`, `split`, and `cases`.
8. Close a stubborn subgoal with `sorry` to keep checking the rest of the
   file, then come back to it. The theorem stays flagged as
   `incomplete: uses sorry` until the `sorry` is removed.

## Style Conventions

The current examples and standard library follow these conventions:

- Put imports first.
- Put `mode constructive` explicitly in ordinary files.
- Use short hypothesis names such as `h`, `hp`, `hx`, `ih`.
- Use longer names for theorem-level assumptions, such as `hAB` or `hpq`.
- Indent case and induction branch bodies by four spaces under the arm.
- Prefer importing `std/prelude.ctea` in examples that use the library.
- Use explicit theorem instantiation when it makes a proof more predictable.
