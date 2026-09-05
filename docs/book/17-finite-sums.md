# Chapter 17 — Adding Up Finite Lists

Companion files:
[examples](hol-code/ch17-examples.ctea),
[exercises](hol-code/ch17-exercises.ctea),
[solutions](hol-code/ch17-solutions.ctea),
[mistakes](hol-code/ch17-mistakes.ctea),
[assignment policy](hol-code/ch17-solutions.ctea-assignment), and
[browser assignment](hol-code/ch17.ctea-task).

Suppose three groups submit 2, 5, and 2 projects. Their total is 9. The two
groups that submitted 2 projects still contribute separately: we are adding
entries in a list, not counting the distinct numbers in a set.

By the end of this chapter, you should be able to compute a concrete total,
use a known total when an entry is added, and combine totals without opening
up every list. Chapters 9 and 11 supply the induction background; Chapter 13
introduces the shared list notation.

## 17.1 A sum follows the list

The examples import two libraries:

```cetacea
import builtin:std/hol/sums.ctea as S
import std/hol/list@1 as L
```

`builtin:` selects the library shipped with the checker, including when your
file is outside the repository. `S` and `L` share the same list type.
`L.nil` is the empty list; `L.cons(h, t)` puts entry `h` before list `t`.

The sum of an empty list is zero. The sum of `L.cons(h, t)` is the head `h`
plus the sum of the tail `t`. The library defines this by structural recursion:

```cetacea
defrec sum (xs : L.List Nat) : Nat
| nil => 0
| cons h t rec => add(h, rec)
```

Here `rec` is the sum already computed for the tail. You do not need to copy
this definition into your file; use the imported name `S.sum`.

For a concrete list, computation does the work:

```cetacea
theorem three_entries : S.sum(L.cons(2, L.cons(5, L.cons(2, L.nil)))) = 9 := by
  simp
  refl
```

Try changing the claimed total to 7. The checker rejects it. It will not
discard a repeated entry just because the same value appeared earlier.

## 17.2 Unknown lists need laws

When `xs` is an unknown list, computation cannot inspect its entries. The
library gives us three checked laws:

| Law | Statement |
| --- | --- |
| `S.sum_nil` | `S.sum(L.nil) = 0` |
| `S.sum_cons` | `S.sum(L.cons(h, xs)) = add(h, S.sum(xs))` |
| `S.sum_append` | `S.sum(L.append(xs, ys)) = add(S.sum(xs), S.sum(ys))` |

`append` concatenates lists. Unlike a set union, it keeps every occurrence.
No disjointness or duplicate-free hypothesis is needed for its sum law.

For example, this proof uses the law directly:

```cetacea
theorem two_groups (xs ys : L.List Nat) :
  S.sum(L.append(xs, ys)) = add(S.sum(xs), S.sum(ys)) := by
  exact S.sum_append
```

The theorem parameters come from the goal. To use the law inside a larger
expression, write `rewrite -> S.sum_append`. For two nested concatenations,
rewrite once for the outer concatenation and again for the inner one. Then
`N.add_assoc` can change `add(add(a, b), c)` into `add(a, add(b, c))` after
importing `builtin:std/nat.ctea as N`.

## 17.3 Why the concatenation law holds

Read [the library proof](../../std/hol/sums.ctea). It inducts on the first
list `xs`.

For the empty list, appending `ys` gives `ys`, and the empty sum contributes
zero. For `L.cons(h, t)`, append preserves the first entry `h`. The induction
hypothesis combines the totals of `t` and `ys`; associativity then puts the
head contribution in the right place.

This proof is constructive and checked by both proof engines. The library
does not assume the sum law as an axiom. You can use it in the restricted
`fol+induction` assignment profile.

## 17.4 Your turn

Open the exercise file and replace each `sorry`:

1. Compute a three-entry total containing a zero and a repeated value.
2. Given the total of `xs`, prove the total after adding a head entry of 4.
3. Given totals for `xs` and `ys`, prove their combined total.
4. Combine three lists and associate the numerical additions to the right.

For exercise 2, introduce the known total, rewrite with `S.sum_cons`, and
then use the hypothesis. Exercise 3 follows the same pattern with
`S.sum_append`. Exercise 4 needs two applications of that law followed by
associativity. Check after each step and read the remaining goal.

The mistakes file contains three intentionally rejected proofs. Compare each
claimed equation with the correct library law: which contribution vanished?

## 17.5 Check the completed assignment

In the browser, open the exercise source and load `ch17.ctea-task` through the
assignment control. An unfinished proof can be saved, but it does not satisfy
the assignment. The selected task requires all four original statements and
rejects holes, new axioms, and classical reasoning. Library theorems and helper
proofs are allowed; the task does not enforce a particular tactic sequence.

With the native checker:

```sh
target/debug/cetacea_cli --assignment \
  docs/book/hol-code/ch17-solutions.ctea-assignment \
  docs/book/hol-code/ch17-exercises.ctea
```

Run this from the repository, or use the paths where you saved the two files.
The completed solutions pass the same policy. A source file containing
`sorry` can receive an ordinary incomplete result while assignment acceptance
is false; those are separate checks.

Natural-number list sums are a useful step toward counting vertex degrees.
A graph proof must still define degrees and justify its vertex and edge
enumerations. This chapter does not yet prove the handshake theorem.
