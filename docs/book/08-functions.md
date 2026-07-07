# Chapter 8 — Functions: Relations with Rules

> **Files for this chapter:**
> [`code/ch08-examples.ctea`](code/ch08-examples.ctea) ·
> [`code/ch08-mistakes.ctea`](code/ch08-mistakes.ctea) (intended to fail) ·
> [`code/ch08-exercises.ctea`](code/ch08-exercises.ctea) ·
> [`code/ch08-solutions.ctea`](code/ch08-solutions.ctea)

## 8.1 Two promises

Every person has an age. Not "most people," not "usually one age,
occasionally two" — the relation between a person and their age keeps
two ironclad promises:

1. **At least one:** everyone has *some* age.
2. **At most one:** nobody has *two* ages.

Compare a relation that keeps neither promise: *x has read book y*.
Some people have read nothing; most have read many things. Perfectly
respectable relation — but you'd never say "the book of x" the way you
say "the age of x." **That's what a function is: a relation that keeps
both promises.** The slogan from your discrete math course — *every
input is related to exactly one output* — is "at least one" and "at
most one" stapled together, and this chapter makes the slogan into
checkable mathematics.

The move that makes it formal: we represent a function by its
**graph**, a two-place predicate `G(x, y)` read as "input x yields
output y." (Think of the graph of a real function from algebra — the
set of pairs `(x, f(x))` — and keep only the idea "which pairs are
related.") Chapter 7 studied properties of relations; a function is
just a relation with two particular properties. The whole chapter runs
on machinery you already own.

## 8.2 The four properties, from the library

`std/fun.ctea` — loaded by the prelude you're already importing —
states the two promises, plus two more properties that will dominate
the second half of the chapter. All four take a graph
`G : A -> B -> Prop` relating inputs in `A` to outputs in `B`:

```text
def Total (A : Type) (B : Type) (G : A -> B -> Prop) : Prop := forall x : A, exists y : B, G(x, y)

def SingleValued (A : Type) (B : Type) (G : A -> B -> Prop) : Prop := forall x : A, forall y1 y2 : B, G(x, y1) -> G(x, y2) -> y1 = y2
```

`Total` is promise one: every input has at least one output.
`SingleValued` is promise two, phrased the way equality lets us:
if `x` yields `y1` and `x` yields `y2`, then `y1 = y2` — you can
*claim* two outputs, but they were the same output all along. A graph
with both properties deserves the word "function."

Let's keep the age promise formally. Declare `age` as a function
symbol:

```text
func age : Person -> Nat
```

Its graph has two *different* types, person in and number out, so the
lambda gives each binder its own annotation:

```text
theorem age_graph_total : Total(fun (p : Person) (n : Nat) => age(p) = n) := by
  unfold Total
  intro p
  exists age(p)
  refl
```

After `unfold Total` the goal is
`forall x : Person, exists y : Nat, age(x) = y`. For an arbitrary
person `p`, the witness is the term `age(p)` itself, and `refl` closes
`age(p) = age(p)`.

## 8.3 Declared functions and their graphs

Cetacea's `func` declarations — `mother` has been one since Chapter 5
— are function *symbols*: `mother(x)` is a term you can compute with
and rewrite under. To ask Chapter 7-style questions about `mother`, we
need it as a *relation*, and the recipe is one lambda:

```text
fun x y : Person => mother(x) = y
```

*x yields y exactly when mother(x) equals y* — the graph of `mother`.
And here is the pleasant theorem: a declared func's graph keeps both
promises *provably*, with three-line proofs:

```text
theorem mother_graph_total : Total(fun x y : Person => mother(x) = y) := by
  unfold Total
  intro x
  exists mother(x)
  refl
```

Who is the output for input `x`? Why, `mother(x)` — the term names its
own witness, and `refl` seals `mother(x) = mother(x)`. Chapter 4's
`exists` plus Chapter 5's `refl`, and "at least one" is kept.

```text
theorem mother_graph_single_valued
  : SingleValued(fun x y : Person => mother(x) = y) := by
  unfold SingleValued
  intro x
  intro y1
  intro y2
  intro h1
  intro h2
  rewrite h1
  exact h2
```

"At most one": we hold `h1 : mother(x) = y1` and `h2 : mother(x) = y2`
and owe `y1 = y2`. Bare `rewrite h1` — hunt the goal for `h1`'s right
side, `y1`, and fold it back to `mother(x)` — leaves
`mother(x) = y2`, which is `h2`. Both claimed outputs collapse into
the term they came from.

When all binders have one type, the shorthand `fun x y : Person => ...`
keeps examples compact. For mixed graphs, use the parenthesized form
from `age`: `fun (p : Person) (n : Nat) => ...`.

## 8.4 Injective and surjective: the two aristocrats

Now the two properties that mathematicians actually gossip about.
Again from `std/fun.ctea`:

```text
def Injective (A : Type) (B : Type) (G : A -> B -> Prop) : Prop := forall x1 x2 : A, forall y : B, G(x1, y) -> G(x2, y) -> x1 = x2

def Surjective (A : Type) (B : Type) (G : A -> B -> Prop) : Prop := forall y : B, exists x : A, G(x, y)
```

**Injective** — *no collisions*: if two inputs land on the same
output, they were the same input. Squint at the definition next to
`SingleValued` and you'll see they are mirror images — the same
formula with the input and output columns swapped. (An injective
function is one whose *reversed* graph is single-valued. This
symmetry is beautiful and also a trap; it's Mistake 2.)
**Surjective** — *no gaps*: every output in `B` actually gets hit.

The successor function `succ` is the book's favorite specimen,
because it has one property and provably lacks the other. Injective
first — if `succ(x1)` and `succ(x2)` are the same number, then
`x1 = x2` — with the library fact `succ_inj` doing the peeling:

```text
theorem succ_graph_injective : Injective(fun x y : Nat => succ(x) = y) := by
  unfold Injective
  intro x1
  intro x2
  intro y
  intro h1
  intro h2
  apply succ_inj
  rewrite -> h1
  exact eq_symm h2
```

Trace the endgame, because it's a Chapter 5 étude. After the intros we
hold `h1 : succ(x1) = y` and `h2 : succ(x2) = y`, owing `x1 = x2`.
`apply succ_inj` works backwards — to prove the predecessors equal,
prove `succ(x1) = succ(x2)`. Then `rewrite -> h1` replaces `succ(x1)`
with `y`, leaving `y = succ(x2)` — which is `h2` *flipped*, so
`eq_symm h2` pays exactly.

Now the showpiece: `succ` is **not** surjective, because nothing maps
to `0` — there is no natural number whose successor is zero. First,
that lemma, and its proof is the cleverest six lines in the chapter:

```text
theorem succ_never_zero (k : Nat) : not (succ(k) = 0) := by
  intro h
  apply congr_pred {A := Nat; P := fun n : Nat => le(succ(k), n); x := succ(k); y := 0}
  exact h
  exact le_refl {n := succ(k)}
```

Chapter 5 promised `congr_pred` — Leibniz's law as a *thing* — would
star in a clever proof; here it is. We assume `h : succ(k) = 0` and
owe `False`. The scheme: find a property that `succ(k)` *has* and `0`
*lacks*, then ride it across the equality. The property is
`P := fun n => le(succ(k), n)` — "being at least succ(k)."
`congr_pred` says `P` must transfer from `succ(k)` to its equal, `0` —
but `P(succ(k))` is `le(succ(k), succ(k))`, true by `le_refl`, while
`P(0)` is `le(succ(k), 0)`, which the checker *computes* straight down
to `False` (Chapter 7's `le`-arithmetic again). So the `apply` matches
our `False` goal, and the two remaining debts are the equality (`h`)
and the true instance (`le_refl` — with explicit braces, since nothing
in a `False` goal hints at which number we mean). A truth, an
equation, a contradiction: *ex falso*, delivered by substitution.

With the lemma in hand, the refutation follows Chapter 7's
counterexample etiquette — assume surjectivity, demand a preimage for
`0`, and feed it to the lemma:

```text
theorem succ_not_surjective : not Surjective(fun x y : Nat => succ(x) = y) := by
  intro h
  simp at h
  cases h 0 with
  | intro w hw =>
      apply succ_never_zero {k := w}
      exact hw
```

`h 0` — the surjectivity claim, asked about `0` — is an existential;
`cases` opens it to a witness `w` with `hw : succ(w) = 0`, and
`succ_never_zero` ends the conversation.

Step back and admire what this pair of theorems says: `succ` maps the
naturals into the naturals *without collisions* and yet *misses a
spot*. A finite set can't do that — shuffle ten things injectively
into ten slots and every slot is hit. A set that can embed into itself
with room left over is, in Dedekind's famous definition, precisely an
**infinite** set. Your two little proofs are a certificate that `Nat`
is infinite.

## 8.5 Bijections

A graph that is both injective and surjective — no collisions, no
gaps, a perfect pairing — is called **bijective**. The identity
function is everyone's first example, and the library proves both
halves (`id_injective`, `id_surjective`) and bundles them under the
definition `Bijective`:

```text
theorem identity_bijective_demo : Bijective(fun x y : Person => x = y) := by
  exact id_bijective {A := Person}
```

`Bijective(G)` unfolds to `Injective(G) /\ Surjective(G)`, so a proof
of a bijection is still a proof of the two promises. The definition
just lets the theorem statement say the mathematical word directly.

## 8.6 Composition: properties that survive plugging together

The deepest fact in the functions-as-relations story is that the good
properties *compose*. If `F : A -> B -> Prop` and `G : B -> C -> Prop`
are graphs, their composite relates `x` to `z` when some midpoint
carries the baton:

```text
exists y : B, F(x, y) /\ G(y, z)
```

`std/fun.ctea` proves the two classics: `compose_injective` (two
injective legs make an injective composite) and `compose_surjective`
(likewise for surjective). Here's the injective one deployed, in the
Chapter 4 own-the-shape style — arbitrary graphs on `Person`, and the
library theorem invoked with its two premises handed over as
arguments:

```text
theorem compose_preserves_injective
  (F : Person -> Person -> Prop)
  (G : Person -> Person -> Prop)
  : Injective(F)
    -> Injective(G)
    -> forall x1 x2 : Person, forall z : Person,
         (exists y : Person, F(x1, y) /\ G(y, z))
         -> (exists y : Person, F(x2, y) /\ G(y, z))
         -> x1 = x2 := by
  intro hf
  intro hg
  exact compose_injective {A := Person; B := Person; C := Person; F := F; G := G} hf hg
```

One line of substance: instantiate, then apply to `hf` and `hg` —
proof expressions take arguments just like Chapter 4's `h alice`, and
here the arguments are whole *proofs*. Do also read the proof of
`compose_injective` itself in `std/fun.ctea` — it's a `cases` inside a
`cases` with a `have` at the bottom, every tool from Chapters 4 and 5
in a dozen lines, and it's pleasant to watch a library earn its keep.

The same theorem can be used with concrete graph lambdas. Since
`succ_graph_injective` proves the successor graph injective,
`succ_succ_graph_injective` instantiates `compose_injective` with
`F := fun x y : Nat => succ(x) = y` and
`G := fun y z : Nat => succ(y) = z`, then hands the same premise proof
to both legs. The result says the two-step successor graph is
injective without reproving the composition argument.

## 8.7 Common mistakes

Run [`code/ch08-mistakes.ctea`](code/ch08-mistakes.ctea) — intended to
fail.

**Mistake 1: a witness from the wrong column.** Proving totality of
`AgeIs`, the proof reaches the goal "there exists an age for `x`" and
offers... `x`:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch08-mistakes.ctea:22: theorem `witness_from_wrong_column` failed: exists witness `x` has type `Person`, but the goal needs a `Nat`
  note: target: exists y : Nat, AgeIs(x, y)
```

Chapter 4's wrong-world witness, all grown up: with relations between
*two* types, "which column am I in?" becomes a live question, and the
type-checker answers it before the logic even wakes up. When a graph
runs `A` to `B`, totality wants a `B`-witness and surjectivity an
`A`-witness — if you can keep that straight, you've understood both
definitions.

**Mistake 2: single-valued is not injective.** The mirror symmetry
from Section 8.4, mistaken for sameness — the file tries to *derive*
`Injective(G)` from `SingleValued(G)`, feeding the single-valuedness
hypothesis the injectivity data:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch08-mistakes.ctea:37: theorem `single_valued_is_not_injective` failed: cannot use proof `h` with an argument: proof has type `G(x1, y)`, but expected `G(x1, x2)`
  note: target: x1 = x2
```

Decode it: `h` (single-valuedness) was specialized to `x1` and then to
`x2` — but its second argument is supposed to be an *output*, so the
checker now expects evidence `G(x1, x2)`, "input x1 yields output x2."
We offered `G(x1, y)` instead, and the mismatch names the exact spot
where the two definitions' columns cross. The statement itself is
false, not just badly proved — a constant graph is single-valued but
maximally collision-prone. This one still earns no countermodel note:
the relevant facts are wrapped in graph-property definitions, which
are outside the small first-order fragment the checker searches. The
counterexample lives in your head, and the error message is the one to
remember: *when arguments seem to be in the wrong slots, re-read which
column each quantifier ranges over.*

**Mistake 3: "inverting" succ with truncated subtraction.** Surely
`succ` is surjective — every `y` is hit by `y - 1`? The proof offers
`sub(y, 1)` as the preimage and asks `refl` to check:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch08-mistakes.ctea:45: theorem `succ_surjective_wish` failed: refl cannot prove `succ(sub(y, succ(0))) = y` because the sides are not identical
  note: target: succ(sub(y, succ(0))) = y
  note: the open arithmetic goal does not follow from the current hypotheses: it is false when y = 0. Reconsider the earlier proof steps.
  help: Use equality simplification first
    `refl` closes goals whose two sides are already identical. Try `simp` or `rewrite` before `refl` if the sides should compute to the same term.
    try:
      simp
      refl
```

`refl` won't budge, and it's right not to: for a *variable* `y` the
two sides aren't equal-by-computation, and they aren't even *true* —
at `y = 0`, truncated subtraction gives `sub(0, 1) = 0`, so the left
side is `succ(0) = 1`, not `0`. The wish fails at exactly the number
Section 8.4 proved unreachable. (This is also your periodic reminder
that Nat's subtraction is truncated — a fact `std/modular.ctea`'s
authors worked around too, as its comments cheerfully admit.)

## 8.8 Exercises

Open [`code/ch08-exercises.ctea`](code/ch08-exercises.ctea) and clear
the `sorry` flags.

- **Exercise 8.1** the squaring graph `fun x y : Nat => mul(x, x) = y`
  is total — the witness names itself, like `mother_graph_total`.
- **Exercise 8.2** ...and single-valued — one `rewrite`, one `exact`.
- **Exercise 8.3** adding two is injective. Hint: `simp at h1` (and
  `h2`) computes `add(x, 2)` into successors; then `apply succ_inj`
  *twice* and finish the Section 8.4 endgame.
- **Exercise 8.4** the identity graph is surjective: every `y` is hit
  — by whom?
- **Exercise 8.5** the constant graph `fun x y : Person => y = alice`
  is total...
- **Exercise 8.6** ...and single-valued: both claimed outputs equal
  `alice`, so they equal each other — `eq_symm`/`eq_trans` country, or
  a well-aimed `rewrite ->`. (It is spectacularly *not* injective, but
  proving that would need two provably distinct Persons, which our
  little sort doesn't supply — sit with why.)
- **Exercise 8.7** composition preserves surjectivity: mirror Section
  8.6 with `compose_surjective`.

Solutions: [`code/ch08-solutions.ctea`](code/ch08-solutions.ctea).

---

*Next up (see the [outline](OUTLINE.md)): induction — the proof
principle the natural numbers are born with. Chapter 7 owed you
transitivity of `le`, and Chapter 9 pays the debt: prove the base,
prove each rung from the one below, conclude for all. The proofs stop
being shape-shuffling and start being* work — *the good kind.*
