# Chapter 14 — Bijections and the HOL Boundary

> **Files for this chapter:**
> [`hol-code/ch14-examples.ctea`](hol-code/ch14-examples.ctea) ·
> [`hol-code/ch14-mistakes.ctea`](hol-code/ch14-mistakes.ctea) (intended to fail) ·
> [`hol-code/ch14-exercises.ctea`](hol-code/ch14-exercises.ctea) ·
> [`hol-code/ch14-solutions.ctea`](hol-code/ch14-solutions.ctea) ·
> [`HOL assignment policy`](hol-code/ch14-solutions.ctea-assignment) ·
> [`intentionally too-weak policy`](hol-code/ch14-solutions-fol.ctea-assignment)

## 14.1 Same size, different names

A coin has two faces. A bit has two values. We could enumerate both types from
scratch, repeating Chapter 13 twice, but mathematics offers the better idea:
pair every coin face with exactly one bit.

```text
data Coin
| heads
| tails

data Bit
| zero_bit
| one_bit
```

The examples file defines the pairing in both directions:

```text
defrec encode (c : Coin) : Bit
| heads => zero_bit
| tails => one_bit

defrec decode (b : Bit) : Coin
| zero_bit => heads
| one_bit => tails
```

These are definitions, not uninterpreted `func` declarations. Their equations
are checked computations, not axioms. Structural induction proves that the two
functions undo each other:

```text
theorem decode_encode (c : Coin) : decode(encode(c)) = c := by
  induction c with
  | heads =>
      refl
  | tails =>
      refl
```

The reverse theorem follows the constructors of `Bit`. Both proofs are
constructive `fol+induction`: the function names occur only as ordinary,
saturated applications such as `decode(encode(c))`.

Together, these laws say that `encode` is a **bijection**. The left-inverse
law

```text
forall x : A, g(f(x)) = x
```

makes `f` injective: two inputs cannot collapse to one output, because applying
`g` recovers each input. The right-inverse law

```text
forall y : B, f(g(y)) = y
```

makes `f` surjective: every target `y` is reached from `g(y)`.

## 14.2 Mapping an enumeration

The cardinality package supplies a polymorphic operation whose mathematical
type is

```text
map : (A -> B) -> List A -> List B
```

`F.map(encode, xs)` applies `encode` to each position of `xs`. Three checked
theorems describe what happens to the three components of `HasCard`:

```text
F.nodup_map_injective
F.map_length
F.map_coverage_surjective
```

- A left inverse prevents new duplicates.
- Mapping does not change the number of list positions.
- A right inverse turns source coverage into target coverage.

This is exactly the decomposition Chapter 13 taught us to look for.

## 14.3 Why `map` is genuinely higher-order

Compare two expressions:

```text
encode(x)
F.map(encode, xs)
```

In the first, `encode` is used as a function symbol and immediately receives
its argument. First-order logic allows that. In the second, `encode` itself is
an argument to `map`: a function is being passed as a value. That is a
higher-order term.

Cetacea does not blur this distinction. A theorem schema may quantify over a
function symbol while using it only in saturated applications and remain
first-order. A statement containing generic `map`, however, is classified
`hol`. Importing a powerful package is not what raises the fragment; actually
forming the higher-order statement does.

This is the architecture's intended compromise. We can teach ordinary
first-order proofs under a restricted profile, then opt into HOL for exercises
whose mathematics honestly manipulates functions.

## 14.4 Transporting `HasCard`

The chapter's central theorem says that mapping a bijection transports a
cardinality witness:

```text
theorem has_card_map_bijection
  (A : Type) (B : Type)
  (f : A -> B) (g : B -> A)
  (xs : F.List A) (n : Nat) :
  F.HasCard(xs, n) ->
  (forall x : A, g(f(x)) = x) ->
  (forall y : B, f(g(y)) = y) ->
  F.HasCard(F.map(f, xs), n) := by
```

After introducing the three hypotheses, apply `has_card_intro` to the mapped
list. Duplicate-freedom comes from `nodup_map_injective` and the source
projection:

```text
exact F.nodup_map_injective {
  A := A; B := B; f := f; g := g; xs := xs
} left_inverse (F.has_card_nodup {
  A := A; xs := xs; n := n
} source_cardinality)
```

Length is the small equational bridge:

```text
rewrite -> F.map_length {A := A; B := B; f := f; xs := xs}
exact F.has_card_length {A := A; xs := xs; n := n} source_cardinality
```

Coverage uses the other inverse:

```text
exact F.map_coverage_surjective {
  A := A; B := B; f := f; g := g; xs := xs
} right_inverse (F.has_card_coverage {
  A := A; xs := xs; n := n
} source_cardinality)
```

No package theorem asks us to believe “bijections preserve cardinality” as an
opaque slogan. We reconstruct it from the three reasons it is true.

## 14.5 Passing checked definitions as values

Now specialize the theorem to `encode` and `decode`:

```text
theorem encoded_coin_has_same_cardinality
  (xs : F.List Coin) (n : Nat) :
  F.HasCard(xs, n) -> F.HasCard(F.map(encode, xs), n) := by
  intro source_cardinality
  apply has_card_map_bijection {
    A := Coin; B := Bit; f := encode; g := decode; xs := xs; n := n
  }
  exact source_cardinality
  intro x
  exact decode_encode {c := x}
  intro y
  exact encode_decode {b := y}
```

This example found and forced a real implementation repair. Before this
chapter, declared `func` symbols could fill `f`, but student-defined structural
functions such as `encode` were rejected in the function-valued position. The
only workaround would have replaced the two `defrec`s with trusted function
equations—logically worse and pedagogically backwards. The compatibility
bridge now accepts a monomorphic structural definition at its checked arrow
type, and the HOL kernel receives the original definition. No axiom is added.

Notice the fine-grained result: `decode_encode` and `encode_decode` stay
`fol+induction`; only the theorem that passes `encode` to `map` is `hol`.

## 14.6 A profile failure is useful feedback

The correct assignment policy says

```text
profile = "hol"
```

and permits exactly the cardinality, finite, and List package closure. Run it:

```sh
cargo run -p cetacea_cli -- \
  --assignment docs/book/hol-code/ch14-solutions.ctea-assignment \
  docs/book/hol-code/ch14-solutions.ctea
```

The neighboring `ch14-solutions-fol.ctea-assignment` is intentionally too
weak. Run the same solution against it:

```sh
cargo run -p cetacea_cli -- \
  --assignment docs/book/hol-code/ch14-solutions-fol.ctea-assignment \
  docs/book/hol-code/ch14-solutions.ctea
```

The proofs themselves are accepted, but policy rejects `ex14_3` through
`ex14_7` because their statement and dependency fragment is `hol`. It does not
reject `ex14_1` or `ex14_2`. That is the boundary working theorem by theorem,
not a whole file being branded “higher-order” because of one import.

## 14.7 Common mistakes

Run [`hol-code/ch14-mistakes.ctea`](hol-code/ch14-mistakes.ctea), intended to
fail.

**Mistake 1: supplying only one side of a bijection.** A left inverse gives the
injectivity needed for `Nodup`, but target coverage still needs a right
inverse. After every available hypothesis is spent, the checker says exactly
what is missing:

```text
error: docs/book/hol-code/ch14-mistakes.ctea:11: theorem `one_sided_not_enough` failed: unsolved goal `forall y : B, f(g(y)) = y`
```

**Mistake 2: confusing equal list lengths with equal cardinalities.**
`map_length` proves only the middle component. It says nothing about duplicate
outputs or whether every target value is reached:

```text
error: docs/book/hol-code/ch14-mistakes.ctea:29: theorem `length_is_not_cardinality` failed: theorem `F.map_length` does not match goal `F.HasCard(F.map(encode, xs), F.length(xs))`; add explicit arguments if this theorem is intended to apply
```

The type mismatch is the mathematics: an equality proof is not a cardinality
witness.

## 14.8 Exercises

Open [`hol-code/ch14-exercises.ctea`](hol-code/ch14-exercises.ctea).

- **Exercises 14.1–14.2** prove that `encode_answer` and `decode_answer`
  are inverses. Follow the constructors; these are `fol+induction` proofs.
- **Exercise 14.3** applies `map_length` to the concrete structural function.
  This is the first `hol` statement.
- **Exercise 14.4** isolates preservation of `Nodup` from a left inverse.
- **Exercise 14.5** isolates preservation of coverage from a right inverse.
- **Exercise 14.6** assembles the generic `HasCard` transport theorem.
- **Exercise 14.7** specializes it to the checked answer/bit encoding.

Solutions: [`hol-code/ch14-solutions.ctea`](hol-code/ch14-solutions.ctea).

### What this chapter has measured

The logic boundary is understandable when attached to one concrete syntactic
event: passing `encode` into `map`. The checked library decomposition is also a
good teaching fit. The remaining friction is mostly elaboration ceremony:
nearly every package theorem application repeats `A`, `B`, `f`, `g`, and `xs`
even when the goal visibly determines them. Better goal-directed schema
inference could shorten the proof without changing its logic or trust.

The next vertical theorem should be the pigeonhole principle. It will test
whether `HasCard` and bijection/injection support scale from “transport a
witness” to an actual counting argument, and whether the current arithmetic
and list APIs expose the right induction invariant.

---

*Back to [Chapter 13 — Finite Types and Honest Counting](13-finite-types.md) ·
[full outline](OUTLINE.md).*
