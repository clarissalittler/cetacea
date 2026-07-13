# Cetacea Hands-On Tutorial and Pain-Point Lab

This is the practical route into Cetacea as it exists on the `hol` branch. It
is meant for two jobs at once:

1. learn enough of the prover to write and debug real proofs; and
2. notice where the language, tactics, libraries, profiles, or tools make that
   work harder than the mathematics warrants.

The companion file is
[`tutorial/PLAYGROUND.ctea`](tutorial/PLAYGROUND.ctea). It is a checked tour
through propositions, first-order logic, equality, sets, arithmetic,
datatypes, recursion, generic lists, counting, the HOL boundary, and explicit
classical mode.

For exhaustive syntax details, keep the [user guide](USAGE.md) nearby. For a
course-shaped progression with exercises, use the
[book](book/README.md). This tutorial favors short experiments and observable
checker behavior.

## 1. Get to a known-good starting point

From the repository root:

```sh
cargo build -p cetacea_cli
cargo test --workspace
./scripts/check_all.sh
```

The first command leaves a reusable checker at `target/debug/cetacea_cli`.
Using that binary directly makes the edit/check loop faster:

```sh
target/debug/cetacea_cli docs/tutorial/PLAYGROUND.ctea
```

The playground should report nineteen accepted root theorems. Eighteen are
constructive; `playground_excluded_middle` is explicitly classical. Because
the file transitively imports logical HOL packages, ordinary checking is
already fail-closed: the teaching checker and HOL replay must agree.

If you want a disposable copy while preserving the relative imports, keep it
in the same directory:

```sh
cp docs/tutorial/PLAYGROUND.ctea docs/tutorial/MY_PLAYGROUND.ctea
target/debug/cetacea_cli docs/tutorial/MY_PLAYGROUND.ctea
```

`MY_PLAYGROUND.ctea` will be an untracked file. Remove it when finished if you
want a clean worktree.

## 2. Know what is doing the checking

A `.ctea` theorem goes through two conceptually separate stages:

```text
source statement + tactic script
              |
              v
teaching elaborator builds a proof object
              |
              v
kernel checks the proof against the statement
              |
              v
receipt records fragment, trust, features, and dependencies
```

On files using exact logical packages such as `std/hol/list@1`, the current
compatibility path also replays declarations in the HOL checker. Acceptance
requires the two paths to match. The second path is not a heuristic linter; a
mismatch makes the check fail.

The output status has a precise meaning:

- `accepted theorem`: checked, with no unresolved proof hole;
- `incomplete theorem`: accepted only as a draft because `sorry` occurs in its
  dependency closure;
- `trusted axiom`: assumed rather than proved;
- `constructive` or `classical`: the strongest logic actually used by the
  proof.

A theorem can have a first-order-looking statement but a higher-order
dependency. The receipt tracks both, so importing a HOL proof cannot launder
it into a restricted assignment.

## 3. Read one tiny proof as a goal transformation

Start with the first playground theorem:

```text
theorem playground_and_swap (P Q : Prop) : P /\ Q -> Q /\ P := by
  intro h
  split
  exact h.right
  exact h.left
```

Read the script as four state changes:

```text
|- P /\ Q -> Q /\ P

h : P /\ Q
|- Q /\ P

h : P /\ Q
|- Q                    and                    h : P /\ Q
                                              |- P
```

`h.right` proves the first goal and `h.left` proves the second. Tactics are
not magic commands applied to the entire theorem; each consumes the current
goal and produces zero or more new goals.

Pain-point experiment: replace `exact h.right` with `exact h.left`. The error
prints the type of the proof you supplied and the target it expected. Decide
whether that comparison is enough to repair the mistake without reading the
solution.

## 4. The core tactic vocabulary

You can do a great deal with this small table:

| Goal or situation | First tactic to try | Effect |
|---|---|---|
| `P -> Q` or `forall x, P(x)` | `intro name` | moves the premise or binder into context |
| `P /\ Q` | `split` | creates one goal for each conjunct |
| `P \/ Q` | `left` / `right` | chooses which disjunct to prove |
| `exists x, P(x)` | `exists term` | supplies the witness |
| local conjunction, disjunction, or existential | `cases h with ...` | exposes its components or branches |
| target matches a hypothesis | `assumption` or `exact h` | closes the goal |
| target is `True` | `trivial` | supplies the canonical proof |
| theorem conclusion matches the target | `apply theorem` | creates goals for its premises |
| equality with computing sides | `refl` | normalizes and checks reflexivity |
| replace equals by equals | `rewrite -> proof` / `rewrite <- proof` | rewrites one selected occurrence |
| expose a transparent formula definition | `unfold Name` | replaces the definition at the goal |
| computation or listed rewrite rules | `simp` / `simp [rule]` | simplifies the goal or a hypothesis |
| `False` is easier than the current target | `exfalso` | changes the target to `False` |
| context already contains a contradiction | `contradiction` | searches standard contradiction forms |
| Nat or datatype variable | `induction x with` | creates constructor cases and induction hypotheses |
| useful intermediate claim | `have h : P := by` | proves and adds a local lemma |
| a proof hypothesis blocks induction | `revert h` | moves that hypothesis back into the target |
| classical case split | `by_cases h : P` | creates `P` and `not P` goals |
| classical contradiction proof | `by_contra h` | assumes the negation of the target |
| inspect the current state | `show_goal` | emits a goal snapshot note |
| intentionally leave a draft hole | `sorry` | marks the theorem incomplete |

Two details are easy to miss:

- `by_cases` feeds two goals to the following tactic sequence; it does not use
  `| left =>` / `| right =>` arms.
- `cases` and `induction` do use explicit arms when their syntax says `with`.

The complete tactic reference, with accepted forms and examples, starts at
[Core Tactics](USAGE.md#core-tactics).

## 5. Declarations: build a small mathematical world

The playground declares a first-order domain and symbols:

```text
sort Person
const alice : Person
func mentor : Person -> Person
pred Student(Person)
pred Reads(Person)
```

The declaration forms currently worth trying are:

| Declaration | Purpose |
|---|---|
| `sort Person` | new first-order base type |
| `const alice : Person` | named value |
| `func mentor : Person -> Person` | first-order function symbol |
| `pred Reads(Person)` | predicate symbol |
| `def Name ... : Prop := ...` | transparent formula abbreviation |
| `def Name ... : T := ...` | transparent term abbreviation |
| `data Tree ...` | monomorphic inductive datatype |
| `defrec f ...` | structurally recursive definition |
| `axiom name ... : P` | explicitly trusted proposition |
| `theorem name ... : P := by` | checked theorem |
| `namespace name` / `end name` | qualify a group of declarations |
| `import path as alias` | check and qualify another source module |

Type checking happens before proof search. Change `exists alice` in
`playground_exists_reader` to `exists 0`: the checker should reject the Nat
witness for a `Person` existential at the tactic line.

## 6. First-order logic and proof expressions

Universal hypotheses behave like functions from terms to proofs:

```text
all_read : forall x : Person, Student(x) -> Reads(x)
alice_student : Student(alice)

exact all_read alice alice_student
```

The first argument instantiates the universal; the second applies the
resulting implication. The same application syntax works for theorem
references.

When inference cannot determine schema parameters, make them explicit:

```text
exact theorem_name {A := Person; P := Reads; x := alice}
```

Common proof-expression forms include:

```text
h.left
h.right
theorem_name argument
(theorem_name {A := A} argument).left
```

Projections bind tightly. If a deeply nested expression is rejected, split it
into `apply` and `exact` steps before assuming the underlying theorem is
wrong. Chapter 16 records one current parser seam here.

Good files to explore next:

- [`examples/fol.ctea`](../examples/fol.ctea) for direct quantifier use;
- [`examples/fol_advanced.ctea`](../examples/fol_advanced.ctea) for relation
  properties, quantifier distribution, paradoxes, and exists-unique patterns.

## 7. Equality, definitions, and simplification

Cetacea uses typed equality. `refl` closes goals whose sides are definitionally
equal after checked computation:

```text
theorem two_plus_one : add(2, 1) = 3 := by
  refl
```

`rewrite` consumes an equality proof. In

```text
rewrite <- xy
```

the backward arrow replaces the equality's right side with its left side.
When multiple occurrences match, the checker warns which occurrence it chose;
`rewrite all -> proof` rewrites every matching occurrence.

Transparent definitions can be exposed directly:

```text
def MentoredStudent (x : Person) : Prop := Student(mentor(x))

unfold MentoredStudent
```

`simp` handles transparent definitions, Nat computation, recursive
definitions, and the built-in set operations. It can also use named equality
rules or hypotheses:

```text
simp [add_zero_right]
simp [h] at target_hypothesis
simp [h] at *
```

Current distinction: `simp ... at h` exists, but a general
`rewrite ... at h` tactic does not.

Pain-point experiment: delete `simp` from `playground_set_builder`. Try
`unfold Readers` instead. Compare which version better communicates why the
membership claim is true.

## 8. Typed sets

For `S T : Set A`, the source language includes:

```text
x in S
S subset T
empty(A)
singleton(x)
{x, y, z}
union(S, T)
inter(S, T)
diff(S, T)
compl(S)
univ(A)
powerset(S)
pair(x, y)
fst(p)
snd(p)
prod(S, T)
{ x : A | P(x) }
```

Finite set literals elaborate to unions of singletons. `pair(x,y)` has product
type `Prod A B`; `prod(S,T)` is the Cartesian-product set, and `fst`/`snd`
project pairs. The playground's `playground_product_member` uses the checked
`prod_member_intro` theorem rather than relying on notation alone.

Set membership and subset claims simplify to ordinary logic. For example,
membership in a union becomes a disjunction; subset becomes a universal
implication.

Set equality is different. The standard library's `set_ext` is an explicit
trusted axiom, so a theorem using it reports that trust dependency. Run a set
example normally and under an axiom-denying policy to see the distinction:

```sh
target/debug/cetacea_cli std/set.ctea
target/debug/cetacea_cli --deny-axioms std/set.ctea
```

The second command rejects root axioms. A root theorem's receipt separately
tracks whether it actually uses an imported axiom.

## 9. Naturals, recursion, and induction

The built-in Nat surface provides:

```text
0, 1, 2, ...
succ(n)
add(n, m)
mul(n, m)
sub(n, m)
le(n, m)
```

The checked [`std/nat.ctea`](../std/nat.ctea) library supplies arithmetic
lemmas and strong induction. Use direct theorems when they already express the
fact; use induction when proving a new recursive invariant.

Nat induction syntax is:

```text
induction n with
| zero =>
    ...
| succ k ih =>
    ...
```

For a theorem such as `forall m, P(n,m)`, keep `m` under the `forall` until
after induction if the induction hypothesis must work for different values of
`m`. `revert` currently generalizes proof hypotheses, not term variables, so
the theorem statement often has to anticipate this invariant.

Pain-point experiment: inspect the proof of
`nodup_inclusion_length_le` in
[`std/hol/counting.ctea`](../std/hol/counting.ctea). Move its container list
from the inner `forall` to an ordinary theorem parameter and see how the
induction hypothesis changes.

### Relations, functions as graphs, and modular arithmetic

The prelude also imports relation properties, graph-style function properties,
and the current modular library. A binary predicate can be classified with
`Reflexive`, `Symmetric`, `Transitive`, `Antisymmetric`, or `Euclidean`.
Functions are studied through their graphs:

```text
Total(fun (x : A) (y : B) => f(x) = y)
SingleValued(fun (x : A) (y : B) => f(x) = y)
Injective(...)
Surjective(...)
Bijective(...)
```

`playground_mentor_graph_total` proves totality by choosing `mentor(x)` as the
output. This remains a first-order use: the lambda supplies syntax for a
relation schema rather than becoming a partially applied object-level value.
Compare Chapters [7](book/07-relations.md) and [8](book/08-functions.md).

For naturals, `Divides(a,b)` is the usual existential witness relation.
`ModEq(m,x,y)` uses a subtraction-free formulation because Nat subtraction is
truncated; it does not provide a `%` computation operator. The playground
reuses `divides_3_12`. Chapter [10](book/10-recursion-data.md) develops these
proofs and also makes visible where the current arithmetic library stops.

## 10. User datatypes and `defrec`

The playground declares:

```text
data Light
| red_light
| green_light

defrec flip_light (light : Light) : Light
| red_light => green_light
| green_light => red_light
```

`defrec` must cover each constructor with the expected binders, and recursive
calls must be structurally smaller. `refl` computes closed constructor cases.

Structural induction mirrors the datatype:

```text
induction light with
| red_light =>
    refl
| green_light =>
    refl
```

Recursive constructor fields add induction hypotheses after the constructor
arguments. Distinct constructors are disjoint, and equality of two values
built with the same constructor exposes equal corresponding fields.

User-declared datatypes are currently monomorphic. The generic `List A` used
later is a checked imported package datatype, not yet syntax available to
arbitrary user `data` declarations.

Pain-point experiment: rename the second induction arm to `red_light`, omit an
arm, or give a `defrec` arm the wrong number of binders. Check whether the
diagnostic explains both the declaration order and expected shape.

## 11. Imports, aliases, namespaces, and three kinds of library

There are currently three library styles:

1. ordinary checked source, such as `std/nat.ctea`;
2. exact logical packages, such as `std/hol/list@1`; and
3. checked source modules built over logical packages, such as
   `std/hol/counting.ctea`.

Examples:

```text
import ../../std/prelude.ctea
import ../../std/hol/counting.ctea as C
import std/hol/cardinality@1 as H
```

An alias qualifies declarations from the imported source and its transitive
imports. That is why the playground sees `C.List`, `C.length_append`, and
`C.zero_le` through one source-module alias.

The exact packages currently exposed are:

- `std/hol/list@1`: polymorphic `List A`, constructors, `Member`, `Nodup`,
  `append`, `length`, computation theorems, and checked induction;
- `std/hol/finite@1`: whole-type `HasCard` evidence and its List dependency;
- `std/hol/cardinality@1`: generic `map`, its computation and length theorems,
  membership support, and cardinality transport.

The counting source module adds set-relative `HasSize`, member removal,
inclusion bounds, and append membership. It remains source-visible while the
decidable-overlap interface and source-to-`@1` publication mechanism are still
being designed.

Namespaces qualify declarations written in one file:

```text
namespace demo
theorem identity (P : Prop) : P -> P := by
  intro h
  exact h
end demo
```

The theorem is then `demo.identity`.

## 12. See the fragment boundary for yourself

The playground was chosen to include every current teaching fragment. Ask for
machine-readable receipts:

```sh
target/debug/cetacea_cli --json docs/tutorial/PLAYGROUND.ctea
```

With `jq` installed, this extracts the root names and fragment classifications:

```sh
target/debug/cetacea_cli --json docs/tutorial/PLAYGROUND.ctea |
  jq '.hol_shadow.theorems[] |
      select(.is_imported == false) |
      {name, statement_fragment, required_fragment, features}'
```

Representative results are:

| Theorem | Statement | Required | Why |
|---|---|---|---|
| `playground_and_swap` | `prop` | `prop` | propositional natural deduction |
| `playground_every_student_reads` | `fol` | `fol` | first-order terms and quantifiers |
| `playground_mentor_graph_total` | `fol` | `fol` | a saturated relation-schema lambda |
| `playground_add_assoc` | `fol+induction` | `fol+induction` | Nat recursion/induction dependency |
| `playground_member_append` | `fol+induction` | `fol+induction` | generic inductive List and recursive membership |
| `playground_map_refl` | `hol` | `hol` | `map` consumes `bump` as a function value |
| `playground_excluded_middle` | `prop` | `prop` | statement is Prop; receipt separately records `classical` |

Now enforce the boundaries:

```sh
# Fails only because classical proof use is not authorized.
target/debug/cetacea_cli --hol-profile hol \
  docs/tutorial/PLAYGROUND.ctea

# Passes: HOL and classical use are independently authorized.
target/debug/cetacea_cli --hol-profile hol --allow-classical \
  docs/tutorial/PLAYGROUND.ctea

# Fails at playground_map_refl: classical permission does not grant HOL.
target/debug/cetacea_cli --hol-profile fol+induction --allow-classical \
  docs/tutorial/PLAYGROUND.ctea
```

This independence is deliberate:

```text
logical fragment:  prop < fol < fol+induction < hol
trust/status:      checked | axiom | incomplete
logic feature:     constructive | classical
```

One choice does not silently authorize another.

## 13. `HasCard` versus `HasSize`

This distinction is easy to test and important for discrete mathematics:

```text
F.HasCard(xs, n)
```

says `xs` enumerates every value of its element type. In contrast,

```text
C.HasSize(S, xs, n)
```

says `xs` enumerates exactly one set `S : Set A`.

Use Chapters [13](book/13-finite-types.md) through
[16](book/16-finite-unions.md) as a progression:

- Chapter 13 constructs and projects whole-type cardinality evidence;
- Chapter 14 transports it through a bijection and crosses the HOL `map`
  boundary;
- Chapter 15 proves pigeonhole and records the transitive HOL dependency;
- Chapter 16 returns to `fol+induction` and counts particular set unions with
  `HasSize`.

Pain-point experiment: try to state the Chapter 16 union theorem using only
`HasCard`. The missing set argument should become evident before you attempt a
proof.

## 14. Constructive and classical modes

Files begin in constructive mode unless changed. Classical tactics require:

```text
mode classical
```

The mode affects subsequent theorem checking; it is not a claim that every
subsequent proof uses classical logic. Receipts record actual use.

Move `mode constructive` above `playground_excluded_middle`. The theorem then
fails at `by_cases`. Restore classical mode and it passes with a visible
`classical` feature.

For constructive statements, prefer data-bearing conclusions when possible:

- a constructive `P \/ Q` proof tells you which branch;
- a constructive `exists x, P(x)` proof supplies a witness;
- `not forall x, P(x)` does not automatically supply `exists x, not P(x)`;
- a generic negative pigeonhole theorem does not automatically compute a
  colliding pair.

These are design choices with API consequences, not merely tactic syntax.

## 15. Axioms, holes, and strict checking

Add this temporary theorem to your playground copy:

```text
theorem draft (P : Prop) : P := by
  sorry
```

Normal checking retains it as an incomplete theorem. Strict checking rejects
the root dependency:

```sh
target/debug/cetacea_cli --strict docs/tutorial/MY_PLAYGROUND.ctea
```

The granular flags are:

```text
--deny-sorry
--deny-axioms
--deny-classical
```

An `axiom` declaration is explicit trusted input. Trust and incompleteness
propagate transitively: a theorem that uses an axiom or incomplete theorem
cannot hide that dependency by presenting a harmless-looking conclusion.

For course-grade control, assignment manifests additionally pin imports,
allowed imported axioms, profiles, and exact required theorem signatures. A
working example is
[`ch16-solutions.ctea-assignment`](book/hol-code/ch16-solutions.ctea-assignment):

```sh
target/debug/cetacea_cli \
  --assignment docs/book/hol-code/ch16-solutions.ctea-assignment \
  docs/book/hol-code/ch16-solutions.ctea
```

## 16. Debugging with the CLI, TUI, and line shell

### Plain checker

The fastest loop is:

```sh
target/debug/cetacea_cli path/to/file.ctea
```

Diagnostics include the failing theorem and tactic line, the current target,
and often a repair suggestion. Deliberately failing book files are useful
diagnostic samples:

```sh
target/debug/cetacea_cli docs/book/hol-code/ch16-mistakes.ctea
```

### Full-screen TUI

Start it with:

```sh
target/debug/cetacea_cli --tui docs/tutorial/PLAYGROUND.ctea
```

Useful keys:

| Key | Action |
|---|---|
| arrow keys | move/edit source and update cursor-sensitive goals |
| `m` | command menu |
| `F2` | theorem outline |
| `F3` | theorem search |
| `F4` | proof explanation |
| `F5` | diagnostics |
| `Ctrl-S` | save |
| `Ctrl-R` | reload |
| `Ctrl-Z` / `Ctrl-Y` | undo / redo |
| `Ctrl-Q` | quit |

Questions to ask while testing it:

- Does moving the cursor select the proof state you expected?
- Are tactic hints useful, or merely valid?
- Can you locate an imported theorem by the words you naturally search for?
- Does the explanation say enough about implicit instantiation and rewrites?
- After an edit, is it obvious whether the issue is parsing, typing, tactic
  execution, or policy?

### Line-oriented shell

Start it with:

```sh
target/debug/cetacea_cli --line docs/tutorial/PLAYGROUND.ctea
```

Then try:

```text
theorems
select playground_and_swap
goals
hints
step
step
explain playground_and_swap
search append
quit
```

The shell is useful when you want deterministic stepping without editing a
full-screen buffer.

## 17. Browser workflow

Build and serve from the repository root:

```sh
rustup target add wasm32-unknown-unknown
cargo build -p cetacea_wasm --target wasm32-unknown-unknown --release
python3 -m http.server 8000
```

Open:

```text
http://localhost:8000/web/
```

The browser provides checking, cursor goals, hints, diagnostics, theorem
search, and proof explanations. It always uses fail-closed HOL replay for
package-aware analysis. The standard source library, including the checked
counting module, is embedded as virtual files.

Browser assignment-manifest enforcement is not implemented yet, so use the
native CLI for exact grading-policy experiments.

## 18. Countermodels and failed statements

For eligible propositional and bounded first-order/Nat goals, Cetacea can
attach a countermodel or falsifying assignment. This is most useful when the
statement itself is false rather than the proof merely unfinished.

Try changing

```text
P /\ Q -> Q /\ P
```

to

```text
P \/ Q -> P
```

and leave a failing tactic. Compare the countermodel note with the diagnostic
from merely swapping `h.left` and `h.right` in a true theorem. A good tool
should help distinguish “wrong move” from “false destination.”

Countermodel search is gated by certified fragment information. HOL goals do
not get misleading first-order models.

## 19. A focused pain-point lab

Work through these in a playground copy. Record what you expected before each
experiment.

### A. Parser shape

Add a transparent definition with its body on several lines. Formula
definitions are currently more line-oriented than theorem statements. Is the
parse error located where you would look?

### B. Inference versus explicit arguments

In `playground_member_append`, remove explicit parameters from
`C.member_append` one at a time. Note which are inferred from the goal and
which produce an underdetermined error. Did the diagnostic suggest the missing
parameter kind?

### C. Nested proof expressions

Replace an `apply projection` / `exact hypothesis` pair in Chapter 16 with one
inline expression such as:

```text
exact (C.has_size_members {A := A; S := S; xs := xs; n := n} size x).left hx
```

The current parser may reject forms that are mathematically well typed. Is the
workaround discoverable?

### D. Induction invariants

Move a changing container variable outside the `forall` in
`nodup_inclusion_length_le`. Because `revert` cannot generalize term variables,
you may have to redesign the statement before the induction hypothesis is
strong enough. Does the goal display make that cause clear?

### E. Rewriting hypotheses

Try a natural `rewrite -> lemma at h`. General rewrite-at is absent; compare
the available `simp [lemma] at h` workaround. Note whether the distinction is
clear from help and autocomplete.

### F. Constructive data requirements

Try to construct a duplicate-free enumeration for an arbitrary overlapping
union from two `HasSize` witnesses. Identify the exact point where you need
decidable equality or decidable membership.

### G. Fragment honesty

Run the playground under `fol+induction`, then remove only
`playground_map_refl`. The rest should fit once classical use is separately
authorized. This tests whether the profile boundary matches your intuitive
course boundary.

### H. Trust propagation

Create an axiom, prove a helper from it, then prove a harmless-looking theorem
from the helper. Inspect text and JSON output to see whether the root receipt
names the transitive axiom.

### I. Diagnostics versus explanations

For the same broken proof, compare plain CLI output, TUI diagnostics, tactic
hints, and theorem explanation. Record which surface first gives you the
missing mathematical idea.

### J. Library discoverability

Without reading source, search for the theorem that says membership in append
is a disjunction. Try the TUI and line-shell search. Record the search terms
you expected to work.

## 20. Current limitations worth keeping in view

These are active design constraints, not promises that a tactic is hiding
somewhere:

- the parser is deliberately line-oriented; multiline definitions and some
  nested proof expressions are rough;
- user `data` declarations are monomorphic, although checked imported
  `List A` is polymorphic;
- recursion is structural and limited; there is no mutual recursion or broad
  termination checker;
- `revert` handles proof hypotheses, not arbitrary term-variable
  generalization;
- `rewrite ... at h` is missing, although targeted `simp ... at h` exists;
- theorem-parameter inference often needs explicit braces in complex generic
  proofs;
- generic constructive deduplication lacks a decidable equality/membership
  interface;
- checked source modules do not yet compile directly into versioned `@1`
  package registry records;
- model search covers selected certified fragments, not arbitrary HOL;
- browser checking is rich, but assignment-manifest enforcement remains a
  native CLI feature;
- proof diagnostics are generally line-based rather than full source-range
  structured edits.

If you hit something not on this list, reduce it to the smallest theorem that
still feels awkward. A ten-line reproducer is much more useful than a report
that a two-hundred-line proof was unpleasant.

## 21. A useful observation template

For each pain point, write down:

```text
Goal:
What I expected to type:
What Cetacea accepted or reported:
Logical issue, missing library fact, elaboration issue, or UI issue:
Workaround:
Did the workaround teach the mathematics or only the prover:
Smallest reproducer:
Suggested behavior:
```

The crucial classification is “logical issue versus interface issue.” For
example:

- positive collision witnesses require additional logic or computation;
- repeating explicit parameters is elaboration friction;
- copying member-removal induction was a library-design failure, now repaired;
- `map` being HOL is an honest fragment boundary, not a parser accident.

## 22. Where to continue

Choose the path matching what you want to evaluate:

- language and tactics: [User Guide](USAGE.md);
- gradual undergraduate sequence: [Proofs, Checked](book/README.md);
- current usability findings: [Book Friction Ledger](book/FRICTION.md);
- architecture: [Design and Code](DESIGN_AND_CODE.md);
- HOL migration rationale and remaining gates:
  [HOL Re-architecture Plan](HOL_REARCHITECTURE_PLAN.md);
- discrete-mathematics coverage:
  [Gap Audit](DISCRETE_MATH_GAP_AUDIT.md).

The most revealing next theorem-sized experiments are a decidable finite-union
constructor, a handshake lemma over finite graphs, and a finite tree
edge/vertex count. Each stresses a different boundary: computation,
double-counting, and induction over structured combinatorial evidence.
