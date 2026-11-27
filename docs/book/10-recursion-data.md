# Chapter 10 — Recursion and Data: Building Your Own Worlds

> **Files for this chapter:**
> [`code/ch10-examples.ctea`](code/ch10-examples.ctea) ·
> [`code/ch10-mistakes.ctea`](code/ch10-mistakes.ctea) (intended to fail) ·
> [`code/ch10-exercises.ctea`](code/ch10-exercises.ctea) ·
> [`code/ch10-solutions.ctea`](code/ch10-solutions.ctea)

## 10.1 Renting versus owning

So far you've been a tenant. `Nat` came furnished — `+`, `*`, `-`,
`<=`, all built in, all computing on their own. Chapter 9's
whole drama played out inside someone else's arithmetic.

This chapter hands you the keys. You'll define your own recursive
functions over `Nat`, then declare entire new *types* of data — lists,
and in Chapter 11, trees — with their own recursive functions. Along
the way, a pleasant collapse: since definitions compute and `refl`
checks computations, *running your program* and *proving a theorem
about a specific input* become the same act. And at the end we'll
have an honest conversation about the one place in Cetacea's standard
library where something is taken on trust rather than proved — and
how the checker makes sure trust is always visible on the receipt.

## 10.2 `defrec`: definition by recursion

Chapter 9's induction principle said: to *prove* something about every
number, handle `0`, then handle `succ(k)` given the result for `k`.
Definition by recursion is the same idea pointed at *making* things
instead of proving them: to define a function on every number, say
what it returns at `0`, then say what it returns at `succ(k)` given
its value at `k`. In Cetacea this is `defrec`:

```text
defrec double (n : Nat) : Nat
| zero => 0
| succ k rec => succ(succ(rec))
```

One arm per way of building a number — the same two arms as
`induction`, and that's no accident. In the `succ` arm, `k` names the
predecessor and `rec` names the *already-computed recursive result*
`double(k)`. So the definition reads: double of `0` is `0`; double of
`k+1` is double of `k`, plus two.

Definitions made this way compute, and `refl` sees through them:

```text
theorem double_three : double(3) = 6 := by
  refl
```

There is something quietly radical here. In a programming class you'd
*run* `double(3)` and eyeball the `6`. Here the claim `double(3) = 6`
is a theorem, the "run" happens inside `refl`, and the checker's
`accepted` is your test passing — with a proof-shaped receipt.
Evaluating programs and checking proofs: same activity.

Symbolic inputs compute too, as long as the outermost constructor is
visible:

```text
theorem double_succ_demo (n : Nat) : double(succ(n)) = succ(succ(double(n))) := by
  refl
```

And the two views — recursion for building, induction for proving —
meet in the obvious question: is `double(n)` the same as `n + n`?
The definitions are different programs; the *values* agree, and the
proof is a Chapter 9 ladder along the very same skeleton:

```text
theorem double_is_add (n : Nat) : double(n) = n + n := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      rewrite <- ih
      refl
```

In the `succ` arm, `simp` computes `double(succ(k))` to
`succ(succ(double(k)))` and `succ(k) + succ(k)` to
`succ(succ(k + k))`, and `rewrite <- ih` bridges the gap. Recursion
and induction are twins: one builds along the structure, the other
climbs it.

One more `defrec` for the road — the sum `1 + 2 + ... + n`:

```text
defrec sumto (n : Nat) : Nat
| zero => 0
| succ k rec => succ(k) + rec

theorem sumto_four : sumto(4) = 10 := by
  refl
```

(Legend says Gauss did `sumto(100)` in his head. `refl` does it
without the head.)

## 10.3 Binary functions and the first-argument rule

`defrec` drives its recursion on the **first** argument. Extra
parameters may follow, and they simply ride along, fixed, through the
whole recursion. That's enough for the classic binary operations —
here is addition, built by hand:

```text
defrec addl (n : Nat) (m : Nat) : Nat
| zero => m
| succ k rec => succ(rec)
```

In the arms, `m` is in scope (it's the fixed passenger) and `rec`
abbreviates `addl(k, m)`. The two defining equations compute, so both
are theorems by `refl`:

```text
theorem addl_zero_left (m : Nat) : addl(0, m) = m := by
  refl

theorem addl_succ_left (n m : Nat) : addl(succ(n), m) = succ(addl(n, m)) := by
  refl
```

But now watch the asymmetry that Chapter 9 could only hint at. The
mirror-image fact `addl(n, 0) = n` — surely just as obvious? — does
**not** compute: the recursion inspects the *first* argument, `n` is
symbolic, and the term is stuck. For the built-in `+`, Cetacea's
simplifier papers over this by knowing both orientations; for *your*
definitions, no such favors. You climb:

```text
theorem addl_zero_right (n : Nat) : addl(n, 0) = n := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      rewrite -> ih
      refl
```

This is worth internalizing as a slogan: **one direction of a
recursive definition is free; the other costs an induction.** Which
direction is free is decided by which argument the recursion runs on.

And an honest note about that word "first": it's the default, not a
law. If you want a function that recurses on its second argument —
say, the textbook's addition, defined by `n + 0 = n` and
`n + succ(m) = succ(n + m)` — say so after the result type:

```text
defrec addr (n : Nat) (m : Nat) : Nat on m
| zero => n
| succ k rec => succ(rec)
```

Now `addr(n, 0) = n` is the free direction and `addr(0, m) = m` is the
one that costs an induction. The slogan doesn't change. Only which
side of it you're standing on.

## 10.4 `data`: types of your own

Numbers are one shape of data: built from a start (`0`) by repeating a
step (`succ`). But the world has other shapes, and Cetacea lets you
declare them with `data`. (Your own data types are switched on from
this chapter — if the checker asks for `logic hol`, the Section menu
is behind again.) The standard library's `std/list.ctea`, loaded by
the prelude, declares lists like this:

```text
data List (A : Type)
| nil
| cons(A, List A)
```

Read it like the rules for `Nat` in Section 9.2, with one blank to
fill in. For any type `A`: `nil` — the empty list — is a `List A`; and
if `h` is an `A` and `t` is a `List A`, then `cons(h, t)` — "`h` stuck
on the front of `t`" — is a `List A`. Fill the blank with `Nat` and
you get `List Nat`, lists of numbers; `List Person` would be lists of
Chapter 4's people. This chapter fills it with `Nat` throughout. The
list `[7, 4]` is `cons(7, cons(4, nil))`: same tower-building as
numerals, except each layer carries a value.

Everything from Sections 10.2–10.3 now replays, one-for-one, on your
new data. `defrec` over a `data` type takes one arm per constructor;
in each arm you bind one name per constructor argument, then one name
per *recursive* argument's already-computed result. The library
defines `length` that way, and it computes:

```text
theorem length_demo : length(cons(7, cons(4, nil))) = 2 := by
  refl
```

Here's our own — the sum of a list's elements:

```text
defrec sum (l : List Nat) : Nat
| nil => 0
| cons h t rec => h + rec

theorem sum_demo : sum(cons(1, cons(2, cons(3, nil)))) = 6 := by
  refl
```

In the `cons` arm: `h` and `t` are the constructor's two arguments,
and `rec` is `sum(t)` — one recursive result, because exactly one of
`cons`'s arguments (`t`) is itself a list. That bookkeeping — *arguments
first, then one `rec` per recursive argument* — matters more when a
constructor has several recursive arguments, as Chapter 11's trees
will.

Binary `defrec` works over data too. The library's list concatenation
is the `addl` pattern verbatim — recursion on the first list, second
list riding along:

```text
defrec append (A : Type) (l : List A) (r : List A) : List A
| nil => r
| cons h t => cons(h, append(t, r))
```

(Two things to notice. The `(A : Type)` is the same blank as in
`data List`, so one `append` serves lists of anything. And the library
spells its `cons` arm the other way: no `rec`, with the recursive call
`append(t, r)` written out where our `sum` said `rec`. Both spellings
mean the same thing. Bind only the constructor's own arguments and
you write the recursive call yourself; bind one more name per
recursive argument and the checker hands you the results.)

Either way its defining equations are *theorems*, provable by `refl`
(the library proves them as `append_nil` and `append_cons`):

```text
theorem append_cons_demo (h : Nat) (t : List Nat) (l : List Nat)
  : append(cons(h, t), l) = cons(h, append(t, l)) := by
  refl
```

A `defrec` can even cross worlds — number in, list out. `replicate`
builds the list of `n` copies of `x`:

```text
defrec replicate (n : Nat) (x : Nat) : List Nat
| zero => nil
| succ k rec => cons(x, rec)

theorem replicate_two : replicate(2, 9) = cons(9, cons(9, nil)) := by
  refl
```

## 10.5 What taking things on trust means

Everything above is *defined*, and every equation about it is
*proved*. It's worth pausing on how unusual that is — and on what the
alternative looks like, because Cetacea's standard library contains
exactly one alternative specimen, kept like a museum piece.

Chapter 1 promised that when the checker says `accepted`, your proof
is correct. Precisely: correct *given the axioms it uses*. An `axiom`
is a statement with no proof that the checker simply trusts. Chapter 6
came close to one: set extensionality can't be proved either, but it's
built into what `Set` *means* — a rule of the game, not a favor. An
`axiom` is a favor: a statement somebody adds to a file and asks the
checker to take on faith. The library has exactly one.
In `std/modular.ctea` (modular arithmetic — clock arithmetic, from
the CS 250 course this book shadows), congruence and divisibility are
defined honestly:

```text
def Divides (a : Nat) (b : Nat) : Prop := exists k : Nat, b = a * k
def ModEq (m : Nat) (x : Nat) (y : Nat) : Prop := exists a b : Nat, x + m * a = y + m * b
```

and a dozen theorems about them are proved from scratch. But one —
the bridge from "x is congruent to 0 mod m" back to "m divides x" —
needs order reasoning and subtraction-cancellation lemmas the library
doesn't have yet. Rather than fake it, the library says so, in the
open:

```text
axiom modeq_zero_to_divides (m x : Nat) : ModEq(m, x, 0) -> Divides(m, x)
```

What does using it cost? Load the examples file and compare these two
`accepted` lines — the same fact, proved two ways:

```text
accepted theorem divides_5_20_direct (constructive)
accepted theorem divides_5_20_via_modeq (constructive; axioms: modeq_zero_to_divides)
```

The first proof exhibits the witness directly (`5 * 4 = 20`, `refl`
does the arithmetic). The second applies the axiom bridge, then proves
the remaining premise `ModEq(5, 20, 0)` — and the checker
*permanently stamps the receipt*.
Any theorem that uses an axiom, directly or through other theorems,
carries an `axioms:` list on its accepted line. This is Chapter 3's
nutrition-label idea again: there, the label said which *logic* a
proof consumed; here it says which *trust*. An axiom-free accepted
line means "true, given nothing but the rules." An `axioms:` line
means "true, if you believe these." Both are useful; only the checker
keeps you from confusing them.

A word of calibration: in this book, axioms are for *documented gaps*
(the one above) and for *wiring up a toy world* (Chapter 12 will
declare a row of light bulbs that way). What they are not for is
skipping work — every axiom you
write is a permanent asterisk on every theorem downstream of it. When
you're tempted, remember the pattern of this chapter: Cetacea's
`defrec` got binary parameters precisely so that `append` could stop
being four axioms and start being a definition. Trust, replaced by
construction, one release at a time.

## 10.6 Common mistakes

Load [`code/ch10-mistakes.ctea`](code/ch10-mistakes.ctea) — intended
to fail.

**Mistake 1: redeclaring a name the library owns.** The prelude puts
everything — yours and the library's — in one global namespace, and
`length` is taken:

```text
error: docs/book/code/ch10-mistakes.ctea:13: `length` is already declared as a definition
```

When this bites, you were usually about to redefine something that
already exists (use the library's!) or reusing a good name for a new
idea (pick another — this book's `_demo` suffixes are one convention).

**Mistake 2: miscounting a `defrec` arm's binders.** The `cons` arm
below binds `h` and `rec` but forgets the tail `t`:

```text
error: docs/book/code/ch10-mistakes.ctea:22: `rec` has type `List Nat`, but `Nat` was expected here
```

This one takes a second to decode, and the decoding is the lesson.
Names in an arm are just names; the checker goes by *position*. Two
names for `cons` means the short spelling from Section 10.4 — the
constructor's two arguments and nothing else — so the name `rec` got
attached to the *tail*. Then `h + rec` tries to add a number to a
list, and that's the complaint you see. Calling a list `rec` doesn't
make it a result. The rule from Section 10.4, with the counts filled
in: two constructor arguments, then one recursive result — three
names, in that order.

**Mistake 3: expecting `refl` to do induction's job.** The Section
10.3 slogan, violated on purpose. `append` recurses on its first
argument, so `append(l, nil)` is stuck while `l` is symbolic:

```text
error: docs/book/code/ch10-mistakes.ctea:28: theorem `append_nil_right` failed: `refl` failed: after computation the two sides are `append(l, nil)` and `l`, which differ
  note: target: append(l, nil) = l
```

(And no, `simp` doesn't save this one either.) This is
`addl_zero_right` all over again — the free direction is
`append(nil, l) = l`; the other one costs an induction. But wait:
an induction on *what*? `l` isn't a number. It's a list... which is
built from `nil` by `cons`... which means it should have a ladder of
its own. Hold that thought for one page.

## 10.7 Exercises

Open [`code/ch10-exercises.ctea`](code/ch10-exercises.ctea) — the
definitions are provided; the theorems are yours. As in Chapter 9,
first decide: computation, or climb?

- **Exercise 10.1** `sumto(5) = 15` — Gauss for small `n`.
- **Exercise 10.2** `triple(succ(n)) = succ(succ(succ(triple(n))))` —
  symbolic, but look at the outermost constructor.
- **Exercise 10.3** `triple(n) = n + double(n)` — two recursive
  definitions, related by induction; model it on `double_is_add`.
- **Exercise 10.4** `length(replicate(n, x)) = n` — a theorem
  spanning both worlds: induct on the number, get a fact about lists.
- **Exercise 10.5** `Divides(3, 12)`, by hand: `unfold Divides`, name
  the witness, `refl`.
- **Exercise 10.6** `Divides(3, 12)` again, via
  `apply modeq_zero_to_divides {m := 3; x := 12}` and a congruence
  proof (two witnesses this time). Then read your two accepted lines
  and find the asterisk.

Solutions: [`code/ch10-solutions.ctea`](code/ch10-solutions.ctea).

---

*Next: [Chapter 11 — Structural Induction](11-structural-induction.md),
where the cliffhanger resolves: every `data` type comes with its own
induction principle, read straight off the declaration — and
`append(l, nil) = l` falls in six lines.*
