# Chapter 15 — Pigeonhole, One Element at a Time

> **Companion files:**
> [`hol-code/ch15-examples.ctea`](hol-code/ch15-examples.ctea) ·
> [`hol-code/ch15-mistakes.ctea`](hol-code/ch15-mistakes.ctea) (intended to fail) ·
> [`hol-code/ch15-exercises.ctea`](hol-code/ch15-exercises.ctea) ·
> [`hol-code/ch15-solutions.ctea`](hol-code/ch15-solutions.ctea) ·
> [`HOL assignment policy`](hol-code/ch15-solutions.ctea-assignment) ·
> [`intentionally too-weak policy`](hol-code/ch15-solutions-fol.ctea-assignment)

Put three letters into two mailboxes. Some mailbox receives at least two
letters. Put thirteen people into twelve birth months. Some month contains at
least two of them. This is the **pigeonhole principle**:

> No function from a finite set of size `n + 1` to a finite set of size `n`
> is injective.

The slogan is immediate. A generic checked proof is not. This chapter is the
first place where the three components of `HasCard` have to cooperate in an
inequality, rather than merely travel together across a bijection.

The result will also answer a design question from Chapter 14. We do not need
to retreat from HOL or replace restricted course modes. In the final theorem's
surface statement, `f` is used only as a saturated function symbol, so the
statement itself fits the first-order schema discipline. The proof becomes
genuinely higher-order at `map(f, xs)`. Its two central list-counting lemmas
remain constructive `fol+induction`; the final receipt records the transitive
HOL dependency instead of laundering it through the first-order-looking
conclusion.

## 15.1 State the theorem negatively

Here is the theorem proved in the companion file:

```text
theorem pigeonhole
  (A : Type) (B : Type) (f : A -> B)
  (xs : F.List A) (ys : F.List B) (n : Nat) :
  F.HasCard(xs, succ(n)) ->
  F.HasCard(ys, n) ->
  (forall x1 x2 : A, f(x1) = f(x2) -> x1 = x2) ->
  False
```

Read `xs` as a complete, duplicate-free enumeration of the source and `ys`
as one of the target. The last premise is injectivity in its ordinary
function form. The conclusion says that the three assumptions cannot all be
true.

Textbooks often state the positive version:

```text
exists x1 : A, exists x2 : A,
  (not x1 = x2) /\ f(x1) = f(x2)
```

The negative theorem is the right constructive interface here. Refuting
`forall x1 x2, ...` does not, in intuitionistic logic, automatically produce
the two witnesses hidden by the failed universal. A positive theorem is a
reasonable later exercise under classical mode, or with computational finite
data that includes the decisions needed to search for a collision. We will
not silently spend excluded middle just to make the conclusion resemble the
English slogan.

## 15.2 The proof has three layers

The argument can be seen as a small pipeline:

```text
source HasCard(succ n)
        |
        | map f; injectivity preserves Nodup
        v
duplicate-free list map(f, xs) ---- every member lies in ----> target ys
        |                                                     |
        | duplicate-free inclusion cannot increase length    | HasCard(n)
        v                                                     v
 length(map(f, xs)) <= length(ys)       hence       succ(n) <= n
                                                        |
                                                        v
                                                      False
```

Chapter 14 already supplies `map_length`. Two bridges were still absent:

1. a list-counting theorem saying that a duplicate-free included list cannot
   be longer than its container; and
2. preservation of `Nodup` from ordinary injectivity, not from a separately
   supplied global inverse.

Both are constructive. Both are useful beyond pigeonhole.

## 15.3 Remove an occurrence by using its proof

The key list invariant sounds like this:

```text
F.Nodup(xs) ->
(forall x : A, F.Member(x, xs) -> F.Member(x, ys)) ->
le(F.length(xs), F.length(ys))
```

Induction on `xs` removes its head. To use the induction hypothesis, we must
also remove one occurrence of that head from `ys`. A programming-language
implementation might ask for decidable equality and run an `erase` function.
The proof does not need to decide equality globally. We already possess
`F.Member(h, ys)`, and that proof tells us whether the occurrence is at the
head or in the tail.

The helper returns the remaining list together with exactly the facts the
counting proof needs:

```text
theorem member_remove_one
  (A : Type) (a : A) (ys : F.List A) :
  F.Member(a, ys) ->
  exists zs : F.List A,
    F.length(ys) = succ(F.length(zs)) /\
    (forall x : A,
      (not x = a) ->
      F.Member(x, ys) ->
      F.Member(x, zs))
```

If `a` is the current head, choose the tail as `zs`. If `a` occurs farther
down, apply the induction hypothesis there and put the current head back. The
second conjunct says that removing `a` preserves every *other* member.

This is proof-relevant programming in a very modest form. We did not add an
equality oracle to `HasCard`; we consumed the disjunction already present in
the membership evidence.

## 15.4 Count a duplicate-free inclusion

Now induct on `xs`. It matters where the quantifier over `ys` appears:

```text
theorem nodup_inclusion_length_le
  (A : Type) (xs : F.List A) :
  forall ys : F.List A,
  F.Nodup(xs) ->
  (forall x : A, F.Member(x, xs) -> F.Member(x, ys)) ->
  le(F.length(xs), F.length(ys))
```

Leaving `ys` under the `forall` gives the induction hypothesis for *every*
container. In the successor case we need it at the smaller list `zs`, not at
the original `ys`.

The empty case is `0 <= length(ys)`. In the cons case:

1. `nodup_cons` says the head is absent from the source tail and the tail is
   duplicate-free;
2. inclusion puts the head in `ys`;
3. `member_remove_one` produces `zs`, one element shorter than `ys`;
4. every source-tail member is different from the head, so it remains in
   `zs`;
5. the induction hypothesis gives `length(t) <= length(zs)`; and
6. adding one to both sides and rewriting the two lengths gives the result.

The containing list does **not** need `Nodup`. Extra duplicates only make it
longer, so they cannot invalidate the upper bound.

Direct

```text
induction xs with
| nil => ...
| cons h t ih => ...
```

now works for an imported polymorphic `F.List A`. It elaborates to the
package's checked induction receipt and stays `fol+induction`; students do not
have to spell out a predicate argument to `F.list_induction`.

## 15.5 A mapped member has a source

Chapter 14 proved that `map` preserves `Nodup` when the user supplies a left
inverse. Pigeonhole begins with ordinary injectivity instead. The missing
fact is:

```text
theorem member_map_witness
  (A : Type) (B : Type) (f : A -> B)
  (xs : F.List A) (y : B) :
  F.Member(y, F.map(f, xs)) ->
  exists x : A, F.Member(x, xs) /\ f(x) = y
```

Induction follows the mapped list. The base and step are exposed by two new
checked computation equations:

```text
F.map_nil
F.map_cons
```

They are theorems backed by the structural definition of `map`, not new
reduction axioms. The cons case says either `y = f(h)` or `y` occurs in the
mapped tail. Choose `h` in the first case and use the induction hypothesis in
the second.

The witness theorem turns an alleged duplicate `f(h)` in `map(f, t)` into an
`x` in `t` with `f(x) = f(h)`. Injectivity gives `x = h`, contradicting the
source's `Nodup` evidence. Thus:

```text
theorem nodup_map_of_injective ... :
  (forall x1 x2 : A, f(x1) = f(x2) -> x1 = x2) ->
  F.Nodup(xs) ->
  F.Nodup(F.map(f, xs))
```

These two statements are honestly HOL: `f` is supplied as a value to `map`.

## 15.6 Assemble pigeonhole

The final proof is short compared with its list infrastructure. From source
cardinality and injectivity, obtain:

```text
have mapped_nodup : F.Nodup(F.map(f, xs)) := by
  apply nodup_map_of_injective {A := A; B := B; f := f; xs := xs}
  exact injective
  exact F.has_card_nodup {
    A := A; xs := xs; n := succ(n)
  } source_cardinality
```

Target coverage makes every mapped output a member of `ys`. Apply the list
bound to obtain:

```text
le(F.length(F.map(f, xs)), F.length(ys))
```

Finally, `map_length` and the two `has_card_length` projections turn that into
`le(succ(n), n)`. A one-line mathematical impossibility still needs a small
induction lemma:

```text
theorem succ_not_le_self (n : Nat) : le(succ(n), n) -> False
```

Applying it closes the proof. No axiom, `sorry`, classical rule,
extensionality, or choice appears anywhere in the dependency closure.

## 15.7 The profile boundary is executable

Run the solution policy:

```sh
cargo run -p cetacea_cli -- \
  --assignment docs/book/hol-code/ch15-solutions.ctea-assignment \
  docs/book/hol-code/ch15-solutions.ctea
```

It permits HOL but forbids classical reasoning, new axioms, and incomplete
proofs. Exercises 15.1, 15.2, and 15.5 certify as `fol+induction`. Exercises
15.3 and 15.4 are HOL because they pass `f` to `map`. The final theorem has a
first-order-looking normalized proposition, but its proof necessarily depends
on those HOL map facts, so its required fragment is HOL.

The neighboring FOL policy is deliberately too weak:

```sh
cargo run -p cetacea_cli -- \
  --assignment docs/book/hol-code/ch15-solutions-fol.ctea-assignment \
  docs/book/hol-code/ch15-solutions.ctea
```

It accepts the list and arithmetic pieces, then rejects Exercises 15.3, 15.4,
and 15.6. That is the intended coexistence model: restricted assignments do
not gain HOL by importing the same file, and HOL assignments do not silently
gain classical logic.

## 15.8 Common mistakes

Run [`hol-code/ch15-mistakes.ctea`](hol-code/ch15-mistakes.ctea), intended to
fail.

**Mistake 1: introducing a dependent hypothesis before induction.** If
`member_a : Member(a, ys)` is in the context, it cannot remain unchanged while
`ys` becomes both `nil` and `cons(h,t)`. The diagnostic now knows that the
imported datatype is a List and gives the right constructor skeleton:

```text
cannot induct on `ys` while hypothesis `member_a` depends on it (induction variable has type `F.List A`)
```

Induct while membership is still an implication in the target, then introduce
it inside each arm. For a proof already in context, `revert member_a` performs
the same rearrangement.

**Mistake 2: treating length preservation as pigeonhole.** `map_length` is an
equality, not a contradiction:

```text
theorem `F.map_length` does not match goal `False`
```

The missing mathematics is exactly `Nodup`, inclusion in the exhaustive
target list, and the strict arithmetic comparison.

**Mistake 3: treating a negation as witnesses.** The checker reports the
difference without euphemism:

```text
proof has type `not (forall x1 : A, forall x2 : A, ...)`,
but expected `exists x1 : A, exists x2 : A, ...`
```

Changing modes may justify the logical conversion; it does not make the two
types identical in constructive mode.

## 15.9 Exercises

Open [`hol-code/ch15-exercises.ctea`](hol-code/ch15-exercises.ctea).

- **Exercise 15.1** removes one proved member while preserving all unequal
  members.
- **Exercise 15.2** proves the duplicate-free inclusion length bound. Keep
  `ys` generalized.
- **Exercise 15.3** extracts a source witness from mapped membership.
- **Exercise 15.4** proves `Nodup` preservation from ordinary injectivity.
- **Exercise 15.5** proves `not le(succ(n), n)`.
- **Exercise 15.6** assembles the generic constructive pigeonhole theorem.

Solutions: [`hol-code/ch15-solutions.ctea`](hol-code/ch15-solutions.ctea).

### What this chapter has measured

The theorem is expressible and teachable on the current HOL architecture, and
restricted FOL units still have a meaningful role. The experiment did not
argue for a separate second prover. It did reveal the next library boundary.
The final assembly is about forty lines; the reusable removal, inclusion, and
map-witness infrastructure is roughly two hundred. Those lemmas should become
a checked counting library before finite-union cardinality repeats them.

Three surface repairs paid for themselves immediately: direct induction over
imported `List A`, checked `map_nil`/`map_cons`, and fragment classification
that hides only the internal predicate-valued implementation helper for `le`.
Remaining friction is mostly elaboration: package theorem applications repeat
many inferable parameters; `rewrite ... at h` is not available; and term
variables cannot yet be generalized by `revert`. None is a logical obstacle,
but all three lengthen the student proof.

The next counting target should be finite-union cardinality. It can reuse the
same inclusion bound and will tell us whether the removal lemma is the right
public abstraction or merely a pigeonhole-specific proof device.

---

*Back to [Chapter 14 — Bijections and the HOL Boundary](14-bijections.md) ·
[full outline](OUTLINE.md).*
