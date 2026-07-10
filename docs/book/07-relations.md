# Chapter 7 — Relations: Structure Between Things

> **Files for this chapter:**
> [`code/ch07-examples.ctea`](code/ch07-examples.ctea) ·
> [`code/ch07-mistakes.ctea`](code/ch07-mistakes.ctea) (intended to fail) ·
> [`code/ch07-exercises.ctea`](code/ch07-exercises.ctea) ·
> [`code/ch07-solutions.ctea`](code/ch07-solutions.ctea)

## 7.1 Three questions to ask any relation

Consider a handful of everyday connections between things:

- *x equals y.*
- *x is less than or equal to y.*
- *x knows y.*
- *x and y land on the same hour of the clock.*

Each is a **relation**: a claim about a *pair*. Formally that's nothing
new — Chapter 4's `Knows(Person, Person)` was already a relation, just
a two-place predicate. What *is* new is the move this chapter
practices: instead of studying one relation at a time, we study
**properties of relations** — questions you can put to any relation
whatsoever, and whose answers organize the whole zoo. The classic
three:

1. **Reflexive** — is everything related to itself?
2. **Symmetric** — does `R(x, y)` always come with `R(y, x)`?
3. **Transitive** — do `R(x, y)` and `R(y, z)` always yield `R(x, z)`?

Equality goes three-for-three (Chapter 5 was secretly a proof of
this). "Less than or equal" fails symmetry — `3 <= 5`, but not the
reverse. "Knows" is a sociological minefield: arguably reflexive,
famously not symmetric (celebrities), and transitivity would make your
friend-of-a-friend your friend. And the clock relation — same hour mod
12 — passes all three tests, which earns it the title of *equivalence
relation* and the final section of this chapter.

The formal payoff is a new kind of reuse. Chapter 4 taught you to
state a theorem once over an arbitrary type; this chapter states a
*property* once over an arbitrary **relation**, and instantiates it at
will. It's the difference between proving "equality on `Person` is
reflexive" and owning the very concept of reflexivity.

## 7.2 Stating a property once: `def` over a relation

Cetacea's `def` — which named sets in Chapter 6 — can take a whole
relation as a parameter. Here are the three questions, asked formally,
from the top of the examples file:

```text
def Reflexive (T : Type) (R : T -> T -> Prop) : Prop := forall x : T, R(x, x)

def Symmetric (T : Type) (R : T -> T -> Prop) : Prop := forall x y : T, R(x, y) -> R(y, x)

def Transitive (T : Type) (R : T -> T -> Prop) : Prop := forall x y z : T, R(x, y) -> R(y, z) -> R(x, z)

def Equivalence (T : Type) (R : T -> T -> Prop) : Prop := Reflexive(R) /\ Symmetric(R) /\ Transitive(R)
```

Read the parameter list of `Reflexive`: give me a type `T` and a
relation `R` on `T` (a thing that takes two `T`s and yields a
proposition), and I hand back the proposition *every x relates to
itself*. These definitions are the chapter; everything else is
plugging relations into them.

What can you plug in? A declared predicate like `Knows` fits directly:
`Symmetric(Knows)` is a well-formed proposition (a false one, if the
celebrity intuition holds — but well-formed). For relations that don't
have a `pred` name of their own, you write a **lambda** — an anonymous
relation, built on the spot:

```text
fun x y : Person => Knows(x, y) /\ Knows(y, x)
```

Read: *the relation holding between x and y when each knows the
other.* You saw a lambda flash by in Chapter 4's `forall_mono` braces;
here they become everyday tools. Equality-as-a-relation is the lambda
`fun x y : T => x = y`, the clock relation will be
`fun x y : Nat => ModEq(12, x, y)`, and so on.

One mechanical note before the proofs. A `def` is a *name* for a
formula, and the checker keeps the name folded until you say
otherwise. The tactic `unfold Reflexive` replaces the name by its
definition in the goal, exposing the `forall` underneath so that
`intro` can bite. Forgetting the `unfold` is this chapter's Mistake 1
— the error is friendly, but you'll meet it, so Section 7.7 shows it
now.

## 7.3 Equality's report card

Let's grade equality on all three questions — over an *arbitrary*
type, because nothing about `Person` or `Nat` is needed:

```text
theorem eq_reflexive (T : Type) : Reflexive(fun x y : T => x = y) := by
  unfold Reflexive
  intro x
  refl
```

After `unfold Reflexive`, the goal is
`forall x : T, x = x` — the lambda has been applied, the definition
opened. (Notice the division of labor: `unfold` opens the *property*,
and the lambda's application happens silently as part of it.) Then
Chapter 4's `intro`, Chapter 5's `refl`, done.

```text
theorem eq_symmetric (T : Type) : Symmetric(fun x y : T => x = y) := by
  unfold Symmetric
  intro x
  intro y
  intro h
  exact eq_symm h

theorem eq_transitive (T : Type) : Transitive(fun x y : T => x = y) := by
  unfold Transitive
  intro x
  intro y
  intro z
  intro h1
  intro h2
  exact eq_trans h1 h2
```

Symmetry and transitivity fall to the Chapter 5 lemmas — of course
they do; `eq_symm` and `eq_trans` *are* those properties, we've merely
re-packaged them in the new vocabulary. Three passes, full marks: an
**equivalence relation**, says Section 7.6.

## 7.4 A relation that flunks: `le`

Meet `le(n, m)` — "n is less than or equal to m" — a built-in relation
on `Nat`. Like `add` in Chapter 5, `le` *computes* on concrete
numbers: `simp` and `refl` reduce `le(0, 1)` to `True` and `le(1, 0)`
to `False` without any help. (Its general theory lives in
`std/nat.ctea`; today we need only `le_refl` and one fact with a
wonderful name, `succ_not_le_zero`.)

Reflexivity: everything is less-than-or-equal-to itself, and the
library already knows:

```text
theorem le_reflexive : Reflexive(fun x y : Nat => le(x, y)) := by
  unfold Reflexive
  intro x
  exact le_refl
```

Symmetry is where it gets interesting — because `le` *isn't*
symmetric, and unlike the sad shrug of a failed attempt, we can prove
the failure outright. Here is the first theorem in the book of the
form *this relation does NOT have that property*:

```text
theorem le_not_symmetric : not Symmetric(fun x y : Nat => le(x, y)) := by
  intro h
  simp at h
  have h01 : le(1, 0)
  apply h 0 1
  trivial
  apply succ_not_le_zero {n := 0}
  exact h01
```

This proof is worth walking through slowly — it's a *refutation by
counterexample*, the formal version of "but 3 ≤ 5 and not 5 ≤ 3."
The goal `not Symmetric(...)` is an implication (Chapter 2 forever),
so `intro h` assumes symmetry and owes `False`. `simp at h` unfolds
the definition inside the hypothesis, leaving `h` as the naked
universal claim *whenever x ≤ y, also y ≤ x*.

Now the trap springs, and Chapter 5's `have` gets its finest hour.
`have h01 : le(1, 0)` names the absurd thing we're about to extract,
and makes it the current goal:

```text
h : forall x y : Nat, le(x, y) -> le(y, x)  |-  le(1, 0)
```
To prove it, `apply h 0 1` — symmetry, specialized to the pair
`(0, 1)`, promises `le(0, 1) -> le(1, 0)` — and the premise `le(0, 1)`
*computes to* `True`, so the goal after the `apply` is literally
`True`, and `trivial` collects. Back in the main goal we hold
`h01 : le(1, 0)`, i.e. `1 ≤ 0`, and `succ_not_le_zero` — *no successor
is ≤ 0* — turns it into the `False` we owed.

Two things to notice. First, the counterexample is *inside* the proof:
the pair `(0, 1)` appears nowhere in the statement, only in our
`apply h 0 1`. Choosing it was the creative act; everything else was
bookkeeping. Second — transitivity: `le` *does* have it, and the
standard library provides it as `le_trans` in `std/nat.ctea`. But if
you open that file you'll find its proof is a nested induction —
Chapter 9's whole subject. For now we may *use* `le_trans` freely
while owing the technique that proves it; the debt comes due two
chapters from now.

## 7.5 Manufacturing properties

When a relation lacks a property, you can often build a better
relation out of it. `Knows` isn't symmetric — but *mutual* knowing is,
automatically, no sociology required:

```text
theorem mutual_knowing_symmetric
  : Symmetric(fun x y : Person => Knows(x, y) /\ Knows(y, x)) := by
  unfold Symmetric
  intro x
  intro y
  intro h
  split
  exact h.right
  exact h.left
```

The proof is Chapter 1's and-swap wearing relation clothes: to flip
"x knows y and y knows x" into "y knows x and x knows y," swap the
halves. This trick — symmetrize by conjunction — is a first taste of
*closure* constructions, a theme that runs all through mathematics:
what's the least you must add to a relation to give it the property
you want?

## 7.6 The payoff: clock arithmetic is an equivalence relation

A relation with all three properties is an **equivalence relation**.
That is why the examples file defines `Equivalence(R)` as the bundle
`Reflexive(R) /\ Symmetric(R) /\ Transitive(R)`. It is hard to
overstate how load-bearing that concept is. An equivalence relation is
a machine for *deliberately forgetting*: it
sorts a type into buckets ("equivalence classes") of things you've
chosen not to distinguish. Same birthday. Same remainder. Same shape.
Reflexivity, symmetry, and transitivity are exactly the axioms that
make "same bucket" coherent.

Now the star witness: **congruence mod m**, the clock relation. Two
numbers are congruent mod 12 when they land on the same hour: 14
o'clock *is* 2 o'clock. The standard library (`std/modular.ctea`,
loaded by the prelude) defines it without subtraction — Nat can't
subtract freely — by a lovely trick: *x and y are congruent mod m when
each can be padded by a multiple of m to reach the same number*:

```text
def ModEq (m : Nat) (x : Nat) (y : Nat) : Prop := exists a b : Nat, add(x, mul(m, a)) = add(y, mul(m, b))
```

And — this is the payoff — the library doesn't just define it, it
*proves* the three properties, as honest theorems with no axioms:
`modeq_refl`, `modeq_sym`, and `modeq_trans`. (Open `std/modular.ctea`
and look at `modeq_trans`. It's a dozen `rewrite`s deep, Chapter 5
equational reasoning at full gallop, and every line is checkable. That
proof is why this section can exist.) Our job is just to hold the
certificates up against the Chapter 7 definitions:

```text
theorem modeq_reflexive (m : Nat) : Reflexive(fun x y : Nat => ModEq(m, x, y)) := by
  unfold Reflexive
  intro x
  exact modeq_refl

theorem modeq_symmetric (m : Nat) : Symmetric(fun x y : Nat => ModEq(m, x, y)) := by
  unfold Symmetric
  intro x
  intro y
  intro h
  exact modeq_sym m x y h

theorem modeq_transitive (m : Nat) : Transitive(fun x y : Nat => ModEq(m, x, y)) := by
  unfold Transitive
  intro x
  intro y
  intro z
  intro h1
  intro h2
  apply modeq_trans
  exact h1
  exact h2
```

The middle proof passes `modeq_sym` its three term parameters
positionally, then the proof `h`; this is the same left-to-right habit
as applying a hypothesis to an argument. And the bundle, all three certificates
stapled together, quantified over *every* modulus at once:

```text
theorem modeq_equivalence (m : Nat)
  : Equivalence(fun x y : Nat => ModEq(m, x, y)) := by
  unfold Equivalence
  split
  exact modeq_reflexive {m := m}
  split
  exact modeq_symmetric {m := m}
  exact modeq_transitive {m := m}
```

Sit with what that accepted line means. "Congruence mod m is an
equivalence relation" is a genuine theorem of number theory — the fact
that makes modular arithmetic *arithmetic*, the reason cryptography
and hash tables and calendars can treat "same remainder" as "same."
Your file now contains a machine-checked proof of it, for all moduli
simultaneously, resting on a chain of `rewrite`s you could audit line
by line if you doubted a single link.

And because `ModEq` is just an `exists`, concrete congruences are
Chapter 4 witness-hunting where `refl` does the arithmetic:

```text
theorem clock_27_is_3 : ModEq(12, 27, 3) := by
  unfold ModEq
  exists 0
  exists 2
  refl
```

27 o'clock is 3 o'clock: pad 27 by zero twelves and 3 by two twelves,
and both roads reach 27. The `refl` at the end checks
`add(27, mul(12, 0)) = add(3, mul(12, 2))` by pure computation — the
witnesses were the only creative input.

(For the road not taken: `Divides`, also in `std/modular.ctea`, is
reflexive and transitive but *not* symmetric — 3 divides 12, not vice
versa. Relations like that, "orderings" rather than "samenesses," get
the name *partial order* once you add antisymmetry. The exercises let
you certify the two properties the library already proves.)

## 7.7 Common mistakes

Run [`code/ch07-mistakes.ctea`](code/ch07-mistakes.ctea) — intended to
fail.

One formerly common mistake is gone: `intro`, `split`, `left`, `right`,
and `exists` now look through a folded definition when its outer shape
requires it. An `intro x` aimed directly at `Reflexive(R)` therefore
opens the hidden `forall`; explicit `unfold Reflexive` remains useful
when you want to show that step.

**Mistake 1: unfolding the wrong property.** Automatic unfolding cannot
make an unrelated name occur in the goal:

```text
error: docs/book/code/ch07-mistakes.ctea:17: theorem `wrong_property` failed: no occurrence of definition `Symmetric` in goal `Reflexive(fun x y : Nat => ModEq(m, x, y))`
  note: target: Reflexive(fun x y : Nat => ModEq(m, x, y))
```

Harmless, but common once a file juggles three look-alike definitions
— and worth showing because the message names both what you asked for
and what's actually there. Read errors like a detective: the checker
always tells you which world *it* is living in.

**Mistake 2: wishful symmetry.** The file claims `le` is symmetric and
plays the proof as far as it goes. After `unfold`, intros, and
assuming `h : le(x, y)`, the goal is `le(y, x)` — and the only thing
in reach is `h` itself:

```text
error: docs/book/code/ch07-mistakes.ctea:28: theorem `le_symmetric_wish` failed: exact proof does not solve the goal: proof has type `le(x, y)`, but expected `le(y, x)`
  note: target: le(y, x)
  note: the open arithmetic goal does not follow from the current hypotheses: it is false when x = 0, y = 1. Reconsider the earlier proof steps.
```

(The `help:` paragraph is Chapter 2's usual `exact` advice — check
your terminal.) Look at the failure point: the proof dies *exactly
where the two arguments trade places* — `le(x, y)` offered, `le(y, x)`
owed. The extra note also gives the concrete failed branch: `x = 0`
and `y = 1` make `le(x, y)` true and `le(y, x)` false. That is
precisely what `le_not_symmetric` in Section 7.4 proves. Failed wish,
then proved refutation: that pair of theorems is the complete
etiquette for suspicion.

## 7.8 Exercises

Open [`code/ch07-exercises.ctea`](code/ch07-exercises.ctea) — the
three property definitions are at the top of the file. Clear the
`sorry` flags.

- **Exercise 7.1** `ModEq(10, 23, 3)` — a concrete congruence: find
  `a` and `b` with `23 + 10*a = 3 + 10*b`, and let `refl` check the
  arithmetic.
- **Exercise 7.2** divisibility is reflexive — after the `unfold` and
  `intro`, the library's `divides_refl` is exactly the goal.
- **Exercise 7.3** mutual liking is symmetric — Section 7.5's trick on
  a fresh relation.
- **Exercise 7.4** divisibility is transitive — `apply divides_trans`
  and let your two hypotheses tell the checker what the middle number
  is.
- **Exercises 7.5–7.7** *same mood* — the named relation
  `SameMood(x, y) := Happy(x) <-> Happy(y)` — is an equivalence
  relation, one property per exercise. Remember `<->` is a conjunction
  of implications: `split` proves it, `.left`/`.right` use it.
  Transitivity is the meatiest: chain the two iffs in both directions.
- **Exercise 7.8** prove `Equivalence(SameMood)`, reusing 7.5–7.7
  after `unfold Equivalence` — and enjoy that the proof is three
  `exact`s naming theorems *you* proved.

Solutions: [`code/ch07-solutions.ctea`](code/ch07-solutions.ctea).

---

*Next: [Chapter 8 — Functions](08-functions.md). A function is a
relation with two promises kept — every input gets an output, and no
input gets two. We'll make that slogan literal, meet injections and
surjections, and prove that the natural numbers contain a perfect copy
of themselves with one number left over.*
