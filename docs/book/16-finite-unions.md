# Chapter 16 — Finite Unions Need Relative Evidence

> **Companion files:**
> [`hol-code/ch16-examples.ctea`](hol-code/ch16-examples.ctea) ·
> [`hol-code/ch16-mistakes.ctea`](hol-code/ch16-mistakes.ctea) (intended to fail) ·
> [`hol-code/ch16-exercises.ctea`](hol-code/ch16-exercises.ctea) ·
> [`hol-code/ch16-solutions.ctea`](hol-code/ch16-solutions.ctea) ·
> [`assignment policy`](hol-code/ch16-solutions.ctea-assignment) ·
> [`checked counting module`](../../std/hol/counting.ctea)

For finite sets, one of the first useful counting rules is

```text
|S union T| <= |S| + |T|.
```

If the sets are disjoint, the inequality becomes equality. On paper this is
often justified by saying “put the two lists together.” That sentence hides
two separate obligations:

1. the combined list contains exactly the union; and
2. the combined list has no duplicates.

This chapter makes both obligations explicit. It also finds a real modeling
boundary: Chapter 13's `HasCard(xs,n)` counts an entire type, whereas union is
an operation on two particular subsets of one carrier type. Counting subsets
needs evidence relative to a `Set A`.

## 16.1 `HasCard` and `HasSize` answer different questions

Recall the old witness:

```text
F.HasCard(xs, n)
```

Its coverage field says

```text
forall x : A, F.Member(x, xs)
```

so `xs` enumerates every value of type `A`. There is no set argument. If `S`
and `T` are two subsets of the same `A`, neither subset can be substituted for
that missing argument.

The checked counting module therefore introduces set-relative evidence:

```text
C.HasSize(S, xs, n)
```

This transparently means

```text
C.Nodup(xs) /\
(C.length(xs) = n /\
  (forall x : A, C.Member(x, xs) <-> x in S))
```

The final biconditional is essential. The left-to-right direction says the
list contains no values outside `S`; the right-to-left direction says no
member of `S` was omitted.

The module exports a checked constructor and projections:

```text
C.has_size_intro
C.has_size_nodup
C.has_size_length
C.has_size_members
```

`HasCard` remains the convenient interface for finite *types*. `HasSize` is
the interface for finite *sets*. Neither has to impersonate the other.

## 16.2 A checked source module before a frozen builtin

The chapter begins with

```text
import ../../../std/hol/counting.ctea as C
```

This is a normal source import. Every theorem in the module is proved in
Cetacea, replayed by the HOL checker, and contributes its actual receipt to
clients. The module itself imports the versioned `List A` package, so the
outer alias consistently exposes `C.List`, `C.Member`, `C.append`, and the
new counting theorems.

It is deliberately a checked source module rather than `std/hol/counting@1`
today. Chapter 15 showed that member removal and inclusion bounds were
reusable; this chapter tests which set-relative definitions belong beside
them. Freezing a builtin ID before distinguishing `HasSize` from `HasCard`
would have preserved the wrong abstraction more efficiently.

The reusable surface now contains:

```text
C.HasSize
C.member_append
C.member_remove_one
C.nodup_inclusion_length_le
```

The first two were added for this chapter. The latter two are the checked
counting core extracted from pigeonhole.

## 16.3 Membership in an append

The list theorem behind union is

```text
C.Member(x, C.append(xs, ys)) <->
  C.Member(x, xs) \/ C.Member(x, ys)
```

Its proof is structural induction on `xs`. The empty case reduces append to
`ys`; the cons case combines `member_cons` with the induction hypothesis.

Given exact size witnesses for `S` and `T`, the first exercise turns set-union
membership into appended-list membership:

```text
theorem union_member_in_append ... :
  C.HasSize(S, xs, m) ->
  C.HasSize(T, ys, n) ->
  x in union(S, T) ->
  C.Member(x, C.append(xs, ys))
```

`simp at x_in_union` exposes the disjunction `x in S \/ x in T`. In either
branch, the right-hand direction of `has_size_members` finds the value in the
appropriate list, and `member_append` places it in the combined list.

Notice the evidence flow. Set membership does not magically become list
membership; the relevant `HasSize` witness performs the conversion.

## 16.4 Disjoint union: append is exact

Appending two duplicate-free lists can still create a duplicate across the
join. We first prove the precise missing condition:

```text
theorem nodup_append_of_disjoint
  (A : Type) (xs : C.List A) :
  forall ys : C.List A,
  C.Nodup(xs) ->
  C.Nodup(ys) ->
  (forall x : A,
    C.Member(x, xs) -> C.Member(x, ys) -> False) ->
  C.Nodup(C.append(xs, ys))
```

Keep `ys` generalized and induct on `xs`. For `cons(h,t)`, duplicate-freedom
of the source says `h` is absent from `t`. The cross-list premise says `h` is
also absent from `ys`. Since `member_append` says those are the only two ways
to occur in `append(t,ys)`, the new head is safe. The induction hypothesis
handles the tail.

Now a disjoint union can construct its own exact witness:

```text
theorem has_size_disjoint_union ... :
  C.HasSize(S, xs, m) ->
  C.HasSize(T, ys, n) ->
  (forall x : A, x in S -> x in T -> False) ->
  C.HasSize(
    union(S, T),
    C.append(xs, ys),
    add(m, n)
  )
```

The three `HasSize` fields come from three independent facts:

```text
set disjointness + source Nodup  ---> Nodup(append(xs,ys))
length_append + source lengths   ---> length(append(xs,ys)) = m+n
member_append + exact coverage   ---> append enumerates union(S,T)
```

No equality decision, classical rule, or set extensionality is required.

## 16.5 Arbitrary union: count a supplied witness

When `S` and `T` overlap, raw append can repeat their common members. The
general theorem therefore accepts an already duplicate-free enumeration `zs`
of the union:

```text
theorem finite_union_cardinality_le ... :
  C.HasSize(S, xs, m) ->
  C.HasSize(T, ys, n) ->
  C.HasSize(union(S, T), zs, k) ->
  le(k, add(m, n))
```

Every member of `zs` belongs to `S union T`, hence occurs in `xs` or `ys`,
hence occurs in `append(xs,ys)`. Chapter 15's packaged inclusion theorem gives

```text
C.length(zs) <= C.length(C.append(xs, ys)).
```

The three `has_size_length` projections and `length_append` rewrite this to
`k <= m+n`.

The proof is now mostly composition. The difficult removal induction from
Chapter 15 is used through one theorem application rather than copied. That is
the reuse gate this vertical was meant to test.

## 16.6 Why the general theorem takes `zs`

Why not construct an exact union enumeration from `xs` and `ys` in every
case? To remove cross-list duplicates algorithmically, we must decide for each
element of one list whether it occurs in the other. Generic `A` has equality,
but not decidable equality. A proof of

```text
x = y \/ (x = y -> False)
```

is additional computational information, not a consequence of the current
constructive interface.

There are three honest future APIs:

- accept `zs` as the theorem does here;
- accept decidable equality or decidable set membership and compute `zs`; or
- provide a classical corollary whose receipt records that choice.

The disjoint theorem needs none of these because its premise already tells us
that no cross-list removal is necessary.

## 16.7 The restricted profile still matters

Run the assignment policy:

```sh
cargo run -p cetacea_cli -- \
  --assignment docs/book/hol-code/ch16-solutions.ctea-assignment \
  docs/book/hol-code/ch16-solutions.ctea
```

All four exercises certify at `fol+induction`. The statements use first-order
sets, lists, equality, arithmetic, and structural recursion. No function or
predicate is passed as an object-level value, so this vertical does not cross
the HOL boundary at all.

That result is as important as Chapter 15's mixed result. Moving to a HOL
kernel did not turn every later exercise into HOL. A restrictive assignment
can use the new polymorphic libraries and still enforce the smaller fragment.

## 16.8 Common mistakes

Run [`hol-code/ch16-mistakes.ctea`](hol-code/ch16-mistakes.ctea), intended to
fail.

**Mistake 1: assuming append preserves `Nodup`.** Each input can be
duplicate-free while the same value occurs once in both:

```text
error: docs/book/hol-code/ch16-mistakes.ctea:19: theorem `append_is_not_automatically_nodup` failed: exact proof does not solve the goal: proof has type `C.Nodup(xs)`, but expected `C.Nodup(C.append(xs, ys))`
```

The missing premise is cross-list disjointness.

**Mistake 2: confusing a set with its enumeration.** These propositions live
at different interfaces:

```text
error: docs/book/hol-code/ch16-mistakes.ctea:28: theorem `set_union_membership_is_not_list_membership` failed: exact proof does not solve the goal: proof has type `x in union(S, T)`, but expected `C.Member(x, C.append(xs, ys))`
```

Use `has_size_members` for each source and `member_append` for the result.

**Mistake 3: replacing an upper bound with equality.** Overlap can make the
union strictly smaller than the sum:

```text
error: docs/book/hol-code/ch16-mistakes.ctea:40: theorem `overlap_does_not_give_exact_addition` failed: exact proof does not solve the goal: proof has type `C.HasSize(S, xs, m)`, but expected `C.HasSize(union(S, T), zs, add(m, n))`
```

Exact addition needs disjointness; arbitrary union gets `<=`.

## 16.9 Exercises

Open [`hol-code/ch16-exercises.ctea`](hol-code/ch16-exercises.ctea).

- **Exercise 16.1** crosses from membership in `S union T` to membership in
  `append(xs,ys)` using two `HasSize` witnesses.
- **Exercise 16.2** proves that disjoint duplicate-free lists append without
  duplicates.
- **Exercise 16.3** constructs the exact size witness for a disjoint union.
- **Exercise 16.4** proves the arbitrary finite-union upper bound by reusing
  `nodup_inclusion_length_le`.

Solutions: [`hol-code/ch16-solutions.ctea`](hol-code/ch16-solutions.ctea).

### What this chapter has measured

The Chapter 15 inclusion theorem is the right reusable abstraction: the final
arbitrary-union proof no longer repeats member removal. The vertical also
shows that `HasSize`, not `HasCard`, is the missing set-relative layer.

The largest remaining design choice is computational. A general constructive
union *existence* theorem needs a decidable equality/membership interface;
until that interface is designed, the checked source module should remain
visible and easy to revise rather than becoming an opaque builtin package.

Surface friction remains noticeable. Formula definitions are line-oriented,
large theorem applications repeat parameters that the goal often determines,
and projection results are easier to use with `apply` followed by `exact`
than as nested inline proof expressions. Those are tutorial-level usability
issues, not logical gaps, and they now have concrete examples to reproduce.

---

*Back to [Chapter 15 — Pigeonhole, One Element at a Time](15-pigeonhole.md) ·
[full outline](OUTLINE.md).*
