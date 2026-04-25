# First-Order Predicate Logic (CS 250 Module 4)

Module 4 adds two things to propositional logic: **predicates** (claims
about elements of a domain) and **quantifiers** (`∀`, `∃`). Cetacea
supports both directly. This is also where you start writing proofs that
look most like the math you'll see in upper-division courses.

## Setting up a domain

You don't have to use a specific domain. For each problem, declare:

- a **sort** (a domain),
- any **predicates** (functions from your domain to `Prop`),
- any **functions** (operations on your domain),
- any **constants** (named elements of your domain).

```text
sort Person

const alice : Person
const bob : Person

func mother : Person -> Person

pred Student(Person)
pred Knows(Person, Person)
```

You'll find a worked-out tiny domain in `examples/library_patterns.ctea`
and another one in `examples/fol.ctea`.

## ∀-introduction and elimination

The companion file is [`code/03_first_order.ctea`](code/03_first_order.ctea).

**∀-elimination** (instantiating a universal): if you have
`h : forall x : A, P(x)` and you have a specific `a : A`, then
`h a` is a proof of `P(a)`.

```text
theorem use_forall
  (P : Person -> Prop)
  : (forall x : Person, P(x)) -> P(alice) := by
  intro h
  exact h alice
```

That's it for the elim side — `h alice` *is* the proof.

**∀-introduction**: to prove `forall x : A, P(x)`, write `intro x`
(introducing a fresh element of `A`) and then prove `P(x)`.

```text
theorem forall_self
  (A : Type)
  (P : A -> Prop)
  : (forall x : A, P(x)) -> forall x : A, P(x) := by
  intro h
  intro x
  exact h x
```

The freshness condition Module 4 talks about is enforced for free:
because `x` is bound only inside the `intro`, the proof can't accidentally
use a property of any specific element.

## ∃-introduction and elimination

**∃-introduction**: to prove `exists x : A, P(x)`, supply a witness with
`exists term` and then prove `P(term)`.

```text
theorem alice_exists : Student(alice) -> exists x : Person, Student(x) := by
  intro h
  exists alice
  exact h
```

**∃-elimination**: to *use* a hypothesis `h : exists x : A, P(x)`, do
`cases h with | intro x hx => ...` — that introduces a fresh witness
name `x` and a hypothesis `hx : P(x)`. You can then use them in the body.

```text
theorem ex_proj
  (P Q : Person -> Prop)
  : (exists x : Person, P(x) /\ Q(x)) -> exists x : Person, P(x) := by
  intro h
  cases h with
  | intro x hx =>
      exists x
      exact hx.left
```

The case body is indented under the `=>`. Indentation isn't strict but
must be consistent.

## The four "quantifier negation" laws

CS 250 Module 4 §3 gives the de Morgan rules for quantifiers:

- $\neg(\forall x. P(x)) \equiv \exists x. \neg P(x)$
- $\neg(\exists x. P(x)) \equiv \forall x. \neg P(x)$

Both directions of the second one are constructive. Of the first, only
one direction is constructive — the other needs classical logic. The
standard library provides the constructive halves.

```text
-- not_exists_to_forall_not: imported from std/fol.ctea.
-- (forall x, not P(x)) <-> not (exists x, P(x))    -- both constructive

-- not_forall_to_exists_not: only classically provable.
-- This isn't in the standard library; here's a sketch.

mode classical

theorem not_forall_to_exists_not
  (A : Type)
  (P : A -> Prop)
  : not (forall x : A, P(x)) -> exists x : A, not P(x) := by
  intro h
  by_contra hn
  apply h
  intro x
  by_contra hpx
  apply hn
  exists x
  exact hpx
```

The "neighborhood" of these four laws — what's constructively
provable and what isn't — is one of the most useful things to internalize
from this module. It pays off later in the course when proof-by-
contradiction starts feeling natural.

## Equality

Equality has its own rules: reflexivity (`refl`), and substitution into
predicates (`rewrite h`).

```text
theorem alice_eq_self : alice = alice := by
  refl

theorem rewrite_demo
  (P : Person -> Prop)
  : alice = bob -> P(alice) -> P(bob) := by
  intro h
  intro hp
  rewrite h
  exact hp
```

`rewrite h` rewrites the **right-hand side** of the equality back to
the left-hand side in the current goal. So if `h : x = y`, every
occurrence of `y` in the goal gets replaced with `x`. Read the message
from the kernel — it's the most common place students get tangled.

If you need the other direction (rewrite an `x` to a `y`), use
`eq_subst_left` from `std/eq.ctea` directly. The `rewrite` tactic
doesn't accept a compound proof expression like `rewrite eq_symm h`,
so the cleanest approach is `apply` with explicit schema arguments:

```text
theorem rewrite_back
  (P : Person -> Prop)
  : alice = bob -> P(bob) -> P(alice) := by
  intro h
  intro hp
  apply eq_subst_left {A := Person; P := P; x := alice; y := bob}
  exact h
  exact hp
```

`eq_subst_left` says: from `x = y` and `P(y)`, conclude `P(x)`. Filling
in the schema makes that exactly the lemma we need.

## Module 4 worked exercises

Each of these is checked in [`code/03_first_order.ctea`](code/03_first_order.ctea).

### Exercise 6 (a): `forall x, exists y, x + y = 0` over the integers

We don't have integers in Cetacea, only `Nat`. So we'll instead state
this kind of `forall-exists` proof at the level of an arbitrary domain
with a relation that has the inverse property.

```text
theorem forall_exists_inverse
  (A : Type)
  (R : A -> A -> Prop)
  : (forall x : A, exists y : A, R(x, y))
    -> forall x : A, exists y : A, R(x, y) := by
  intro h
  exact h
```

This is intentionally trivial — the *real* exercise is to *use* such a
hypothesis. See `forall_exists_chain` in the companion file.

### Exercise 8: `forall x, P(x) /\ Q(x)) <-> ((forall x, P(x)) /\ (forall x, Q(x)))`

Both directions are in `std/fol.ctea` as `forall_and_left`,
`forall_and_right`, and `forall_and_intro`. Try to write your own version
without looking and then compare.

### Negation of nested quantifiers

The companion file works `not (forall x, exists y, R(x, y))` into
`exists x, forall y, not R(x, y)`. This needs classical logic.

## Try it

- Negate "every student in CS 250 has solved every homework problem" by
  introducing `Student(Person)` and `Solved(Student, Problem)` as a
  two-place predicate, stating the formula, and trying to prove it
  equivalent to the negation. Quantifier order matters — see the next
  bullet.
- Pick a relation `R : A -> A -> Prop`. Prove `forall x, exists y, R(x, y) -> exists y, forall x, R(x, y)` is **not** valid by trying to
  prove it and seeing what goes wrong. Then prove the (true) converse
  `exists y, forall x, R(x, y) -> forall x, exists y, R(x, y)`. The
  asymmetry is exactly the point of Module 4 §5.
