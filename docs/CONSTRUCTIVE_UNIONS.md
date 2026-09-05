# Constructing a finite union with overlap

`std/hol/finite_union.ctea` constructs a duplicate-free union witness from two
duplicate-free input lists. Unlike the earlier union bound, it does not ask
the caller to supply the output list.

The extra input is explicit decidability of membership in the second list:

```text
forall x : A, Member(x, ys) \/ not Member(x, ys)
```

This is a hypothesis to prove or provide. The library does not silently assume
excluded middle or decidable equality for an arbitrary type.

## The two interfaces

`union_enumeration` takes `Nodup(xs)`, `Nodup(ys)` and those membership
decisions. It proves that some list `zs` is duplicate-free and satisfies

```text
forall x : A, Member(x, zs) <-> Member(x, xs) \/ Member(x, ys)
```

`has_size_union_exists` works with the set-relative interface from Chapter 16.
Given `HasSize(S, xs, m)`, `HasSize(T, ys, n)` and decisions for membership in
`T`, it proves

```text
exists zs : List A,
  HasSize(union(S, T), zs, length(zs)) /\ le(length(zs), add(m, n))
```

Thus the result contains an actual enumeration witness and its size bound.
The proof translates set-membership decisions into list-membership decisions
using the supplied `HasSize` evidence.

## How the construction works

### Reuse equality decisions

For arbitrary lists, prove decidable equality on the element type once:

```text
forall x y : A, x = y \/ not x = y
```

`member_decidable` turns this into membership decisions for any list `xs`.
Its proof checks the head for equality and, when they differ, uses the tail's
decision. The empty case always returns nonmembership.

`union_enumeration_of_decidable_eq` and `has_size_union_of_decidable_eq` accept
this equality premise directly, supplying the membership decisions internally.
The example proves `colour_equality` by cases on the two colours, then uses it
for arbitrary colour lists and set enumerations. Deciding every equality is
stronger than proving reflexivity; the regression suite rejects replacing the
decision proof with `left; refl` for arbitrary distinct variables.

For natural numbers, that equality proof is already available:

```cetacea
import builtin:std/hol/nat_decidable.ctea as D
```

`D.nat_eq_decidable` proves `forall n m : Nat, n = m \/ not n = m` by
induction, using constructor disjointness and successor injectivity. Pass it
to the equality-based union interfaces or to `member_decidable`. The
[numeric examples](hol/examples/nat_union.ctea) construct arbitrary numeric
list/set union witnesses this way. The result remains constructive: deciding
natural-number equality does not introduce excluded middle for arbitrary
propositions, nor does the disjunction prove either branch in isolation.

### Build the witness

The proof inducts on `xs`, keeping `ys` fixed. The empty case returns `ys`.
At a head `h`, first construct the tail's union witness. If `h` already belongs
to `ys`, reuse that witness. Otherwise prepend `h`. The input's duplicate-free
proof says `h` is absent from the tail, and the membership decision says it is
absent from `ys`, so prepending it preserves duplicate-freedom.

The proof explicitly chooses each branch from a supplied disjunction. Both
engines check it constructively at `fol+induction`, without axioms or holes.
It produces existential evidence; it does not add an executable source term
`union_list(xs, ys)` or infer decidable equality for an arbitrary type.

## Try an overlap

[The checked example](hol/examples/overlapping_union.ctea) uses two colours.
The first list contains red and blue; the second contains blue. Appending them
would repeat blue. The example applies `union_enumeration` and proves the
membership decisions by cases on the colour, using `finite` for the concrete
positive and negative membership facts. No classical mode is needed.

The module ships with native and Wasm builds and works in virtual projects.
The regression suite checks the witness receipts, rejects unfinished decision
proofs and rejects a list that repeats blue as a duplicate-free witness.
