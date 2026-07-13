# Chapter 13 — Finite Types and Honest Counting

> **Files for this chapter:**
> [`hol-code/ch13-examples.ctea`](hol-code/ch13-examples.ctea) ·
> [`hol-code/ch13-mistakes.ctea`](hol-code/ch13-mistakes.ctea) (intended to fail) ·
> [`hol-code/ch13-exercises.ctea`](hol-code/ch13-exercises.ctea) ·
> [`hol-code/ch13-solutions.ctea`](hol-code/ch13-solutions.ctea) ·
> [`assignment policy`](hol-code/ch13-solutions.ctea-assignment)

This chapter begins the experimental second part of the book on Cetacea's
`hol` branch. The logic you use here is still first-order logic with induction.
What changes is the library: lists can now contain values of *any* type, and a
checked predicate can say that such a list counts every value exactly once.

## 13.1 What does it mean for a type to have three values?

Consider a datatype with exactly the constructors we want:

```text
data Traffic
| red
| yellow
| green
```

On paper we immediately write “there are three traffic signals.” A proof
assistant is entitled to ask what that sentence means. Three constructor names
have appeared, but counting needs more than typography. We need to exhibit the
three values, show that none was counted twice, and show that no value was
missed.

The witness is the list

```text
F.cons(red, F.cons(yellow, F.cons(green, F.nil)))
```

which we will often typeset as `[red, yellow, green]` in prose. Cetacea does
not yet have bracket notation; in checked source, the nested `cons` expression
is the list.

The import at the top of this chapter's files is new:

```text
import std/hol/finite@1 as F
```

This installs two versioned, kernel-checked packages. `std/hol/finite@1` owns
the cardinality predicate; its dependency `std/hol/list@1` owns `List`, `nil`,
`cons`, `Member`, `Nodup`, and `length`. The shared prefix `F` is only a source
abbreviation. The final receipt still says which package supplied every fact.

Most importantly, `F.List Traffic` is a real type. Chapter 10 had one
monomorphic `List` whose elements were always naturals. Here the same checked
list construction works for `Traffic`, `One`, or any later datatype.

## 13.2 `HasCard` is a package of evidence

For `xs : F.List A` and `n : Nat`, the proposition

```text
F.HasCard(xs, n)
```

means all three of the following:

1. `F.Nodup(xs)` — the enumeration contains no duplicate;
2. `F.length(xs) = n` — it has the claimed number of positions; and
3. `forall x : A, F.Member(x, xs)` — every value of `A` occurs.

The checked introduction theorem exposes that definition without asking us to
unfold package internals:

```text
F.has_card_intro :
  F.Nodup(xs) ->
  F.length(xs) = n ->
  (forall x : A, F.Member(x, xs)) ->
  F.HasCard(xs, n)
```

This is the constructive meaning of a finite type in this course: we possess a
complete, duplicate-free enumeration. Nothing searches an arbitrary set and
guesses its size. The proof carries the evidence.

## 13.3 The one-value type, one job at a time

The examples file starts with the smallest possible datatype:

```text
data One
| only
```

We first prove the three components separately. Duplicate-freedom peels the
outer `cons` with the right-to-left direction of `nodup_cons`:

```text
theorem one_nodup :
  F.Nodup(F.cons(only, F.nil)) := by
  apply (F.nodup_cons {
    A := One;
    h := only;
    t := (F.nil : F.List One)
  }).right
  split
  intro member
  exact F.member_nil {A := One; x := only} member
  exact F.nodup_nil {A := One}
```

Why the type annotation on `F.nil`? The empty list alone contains no element
from which the checker could infer `A`. In this context we mean the empty list
of `One`, so we say so. Context often infers the type automatically, but a bare
polymorphic `nil` is deliberately ambiguous.

Length is computation exposed through checked equations:

```text
theorem one_length :
  F.length(F.cons(only, F.nil)) = 1 := by
  rewrite -> F.length_cons {
    A := One;
    h := only;
    t := (F.nil : F.List One)
  }
  rewrite -> F.length_nil {A := One}
  refl
```

Coverage follows the datatype. An arbitrary `x : One` has one constructor
case, and that value is the head of the list:

```text
theorem one_coverage :
  forall x : One, F.Member(x, F.cons(only, F.nil)) := by
  intro x
  induction x with
  | only =>
      apply (F.member_cons {
        A := One;
        x := only;
        h := only;
        t := (F.nil : F.List One)
      }).right
      left
      trivial
```

Now the final count is almost anticlimactic:

```text
theorem one_has_card :
  F.HasCard(F.cons(only, F.nil), 1) := by
  apply F.has_card_intro {
    A := One;
    xs := F.cons(only, F.nil);
    n := 1
  }
  exact one_nodup
  exact one_length
  exact one_coverage
```

That last proof is short for a good mathematical reason: its three obligations
already have names. Formalization is often less painful when a large claim is
decomposed along the meaning of its definition.

## 13.4 Three constructors expose the real cost

For `[red, yellow, green]`, length is three applications of `length_cons` and
one `length_nil`. Coverage has one induction arm per signal. In the `green`
arm, membership chooses the tail twice and then the head:

```text
| green =>
    apply (F.member_cons { ... }).right
    right
    apply (F.member_cons { ... }).right
    right
    apply (F.member_cons { ... }).right
    left
    trivial
```

Duplicate-freedom is the longest part. To show that `red` is absent from the
tail, `member_cons` turns a hypothetical membership proof into

```text
red = yellow \/ F.Member(red, [green])
```

The first branch contradicts datatype constructor disjointness. The second is
peeled once more; `red = green` is also impossible, and membership in `nil`
is impossible by `member_nil`. Then the same argument repeats for `yellow`.

This is elementary mathematics, but the complete proof in the solutions file
is long. Do not mistake length for depth: the proof repeats a tiny idea because
the current surface makes every list position and every package parameter
explicit. Section 13.8 returns to that friction honestly.

## 13.5 Taking `HasCard` apart again

Once cardinality has been established, later theorems should not carry three
unrelated hypotheses forever. The package provides checked projections:

```text
F.has_card_nodup
F.has_card_length
F.has_card_coverage
```

They support the familiar introduction/elimination rhythm from Chapter 2.
`has_card_intro` builds a witness; the projections consume one. The examples
file reconstructs the whole bundle:

```text
theorem has_card_components
  (A : Type) (xs : F.List A) (n : Nat) :
  F.HasCard(xs, n) ->
  F.Nodup(xs) /\
    (F.length(xs) = n /\ (forall x : A, F.Member(x, xs))) := by
  intro cardinality
  split
  exact F.has_card_nodup {A := A; xs := xs; n := n} cardinality
  split
  exact F.has_card_length {A := A; xs := xs; n := n} cardinality
  exact F.has_card_coverage {A := A; xs := xs; n := n} cardinality
```

The definition remains transparent to the kernel, but student proofs use a
small public interface. That separation lets the library improve without
rewriting every exercise.

## 13.6 The assignment really is first-order

Run the complete solutions under the chapter policy:

```sh
cargo run -p cetacea_cli -- \
  --assignment docs/book/hol-code/ch13-solutions.ctea-assignment \
  docs/book/hol-code/ch13-solutions.ctea
```

The policy permits exactly `std/hol/finite@1` and its List dependency. It
forbids classical reasoning, new axioms, and `sorry`, and its maximum fragment
is `fol+induction`.

Polymorphic library code does not automatically make a concrete theorem HOL.
Every statement in this chapter specializes `List` to ordinary first-order
data. Datatype induction and constructor disjointness add induction, not
higher-order quantification. The checker classifies the completed exercises
accordingly.

## 13.7 Common mistakes

Run [`hol-code/ch13-mistakes.ctea`](hol-code/ch13-mistakes.ctea), which is
intended to fail.

**Mistake 1: treating cardinality as computation.** `refl` proves an equality;
`HasCard` asks for three pieces of evidence:

```text
error: docs/book/hol-code/ch13-mistakes.ctea:16: theorem `count_by_refl` failed: refl expects an equality goal
```

**Mistake 2: leaving polymorphic `nil` ambiguous.** In
`F.length(F.nil) = 0`, even the result `0` does not reveal what element type the
list has:

```text
error: docs/book/hol-code/ch13-mistakes.ctea:19: theorem `ambiguous_empty_length` has invalid statement
```

Write `(F.nil : F.List One)` where the surrounding expression cannot supply
the type.

**Mistake 3: expecting every biconditional to be a simp rule.** The natural
attempt is attractive:

```text
simp [F.nodup_cons, F.nodup_nil, F.member_nil]
```

but today's simplifier accepts equality rules, not the constructive
biconditionals used to characterize `Nodup` and `Member`:

```text
error: docs/book/hol-code/ch13-mistakes.ctea:27: theorem `simp_nodup` failed: simp rule `F.nodup_cons` must prove a term equality
```

For now, use `.left` or `.right` explicitly. This is a limitation of the tactic
surface, not of the logic.

## 13.8 Exercises

Open [`hol-code/ch13-exercises.ctea`](hol-code/ch13-exercises.ctea). Rather
than hiding one enormous `sorry`, the file separates the proof into the jobs
you have just seen.

- **Exercise 13.1** proves the length of `[red, yellow, green]`. Use three
  `length_cons` rewrites and `length_nil`.
- **Exercise 13.2** proves coverage. Induct on `x : Traffic`; choose a path
  through `member_cons` matching the constructor.
- **Exercise 13.3** proves `Nodup`. Peel the list from the outside, use
  `member_cons` to expose impossible equalities, and let `contradiction` use
  datatype no-confusion.
- **Exercise 13.4** packages the three named facts with `has_card_intro`.
- **Exercise 13.5** recovers the components of an arbitrary witness with the
  three projections.

Solutions: [`hol-code/ch13-solutions.ctea`](hol-code/ch13-solutions.ctea).

### What this chapter has measured

The final packaging proof is pleasant. Consuming `HasCard` is pleasant. The
constructor-by-constructor enumeration proof is not yet pleasant: it repeats
long nested list terms, explicit schema arguments, and manual navigation
through biconditionals. That is now a measured textbook problem with a checked
acceptance case, not a speculative complaint. Any future enumeration tactic or
library combinator must shorten Exercise 13.3 while preserving its trust-free
`fol+induction` receipt.

---

*Next: [Chapter 14 — Bijections and the HOL Boundary](14-bijections.md).
Once a type has been counted, can we transfer that count to a different
representation without enumerating everything again? Yes—but generic `map`
crosses a logical boundary we should make visible.*
