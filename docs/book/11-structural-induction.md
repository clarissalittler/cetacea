# Chapter 11 — Structural Induction: Proofs That Follow the Data

> **Files for this chapter:**
> [`code/ch11-examples.ctea`](code/ch11-examples.ctea) ·
> [`code/ch11-mistakes.ctea`](code/ch11-mistakes.ctea) (intended to fail) ·
> [`code/ch11-exercises.ctea`](code/ch11-exercises.ctea) ·
> [`code/ch11-solutions.ctea`](code/ch11-solutions.ctea)

## 11.1 The cliffhanger

Chapter 10 ended with the checker refusing something perfectly true:

```text
theorem append_nil_right (l : List) : append(l, nil) = l := by
  refl
```

Appending the empty list changes nothing — of course. But `append`
recurses on `l`, `l` is a variable, and the computation is stuck at
the starting line. We faced this exact situation with numbers in
Section 9.4, and the cure there was induction: since every `Nat` is
built from `0` by `succ`, prove the claim for `0`, then show it
survives each `succ`.

So look at how a `List` is built:

```text
data List
| nil
| cons(Nat, List)
```

Every list is built from `nil` by finitely many `cons`es. The same
argument should work: prove the claim for `nil`, then show it survives
each `cons`. It does work — it's called **structural induction**, and
the wonderful thing is that you've already learned it. Chapter 9's
induction on `Nat` wasn't a special fact about numbers; it was the
general principle, applied to the simplest interesting `data` type.
This chapter applies it to the rest of them.

## 11.2 Reading the principle off the declaration

Here is the recipe, and it *is* the chapter — everything else is
practice:

> **To prove `P(x)` for every `x` of a data type: one case per
> constructor. In each case, bind the constructor's arguments, and
> receive one induction hypothesis per recursive argument.**

Apply it to `List`. Two constructors, two cases:

- `nil` has no arguments: prove `P(nil)` outright. The base of the
  ladder.
- `cons(Nat, List)` has two arguments — a head `h : Nat` and a tail
  `t : List` — of which one (`t`) is recursive, i.e. is itself a
  `List`. So: prove `P(cons(h, t))` for arbitrary `h` and `t`, given
  **one** induction hypothesis, `ih : P(t)` — the claim for the tail,
  the list one layer *inside* the one you're proving.

The `induction` tactic takes exactly this shape, and the cliffhanger
resolves:

```text
theorem append_nil_demo (l : List) : append(l, nil) = l := by
  induction l with
  | nil =>
      refl
  | cons h t ih =>
      simp
      rewrite -> ih
      refl
```

The `nil` arm owes `append(nil, nil) = nil` — that's the free
direction, `refl`. The `cons` arm opens at

```text
h : Nat, t : List, ih : append(t, nil) = t  |-  append(cons(h, t), nil) = cons(h, t)
```

`simp` fires `append`'s cons equation on the left:

```text
ih : append(t, nil) = t  |-  cons(h, append(t, nil)) = cons(h, t)
```

and the two sides now differ only where `ih` bridges: `rewrite -> ih`
turns `append(t, nil)` into `t`, and `refl` closes. Six lines,
exactly the promised shape — and notice it's the very skeleton of
`sub_self_demo` and `addl_zero_right`, transplanted to a new species.

## 11.3 Length of an append

The flagship list theorem — concatenating adds the lengths (it's
`length_append` in `std/list.ctea`):

```text
theorem length_append_demo (l1 : List) (l2 : List)
  : length(append(l1, l2)) = add(length(l1), length(l2)) := by
  induction l1 with
  | nil =>
      refl
  | cons h t ih =>
      simp
      rewrite -> ih
      refl
```

Two decisions worth narrating. First: induct on `l1`, not `l2` — why?
Because `append` and `length` both recurse on their first argument, so
that's where computation will unfold. (Try `l2`: you'll be stuck
immediately, with an `ih` no rewrite can use. Choosing the induction
variable to match the recursion is most of the art in these proofs.)

Second, the `cons` arm. It opens owing
`length(append(cons(h, t), l2)) = add(length(cons(h, t)), length(l2))`,
and `simp` pushes computation through every function in sight —
`append`'s cons equation, then `length`'s, then `add`'s:

```text
ih : length(append(t, l2)) = add(length(t), length(l2))
  |-  succ(length(append(t, l2))) = succ(add(length(t), length(l2)))
```

Under the `succ`s, the goal *is* `ih`. `rewrite -> ih`, `refl`. The
rhythm — `simp` to compute one layer, `rewrite` the hypothesis,
`refl` — is so reliable that this book's remaining proofs barely
deviate from it. The proofs follow the data.

## 11.4 Trees: two hypotheses per node

Lists reuse `Nat`'s ladder shape: each constructor contains at most
one smaller copy of the type. The recipe gets properly interesting on
the first type that *branches*:

```text
data Tree
| leaf
| node(Tree, Nat, Tree)
```

A `Tree` is either a bare `leaf`, or a `node` carrying a left subtree,
a `Nat` label, and a right subtree. Two recursive functions, using the
Chapter 10 machinery — `size` counts the nodes, `mirror` swaps every
left subtree with its right sibling, all the way down:

```text
defrec size (t : Tree) : Nat
| leaf => 0
| node l v r recl recr => succ(add(recl, recr))

defrec mirror (t : Tree) : Tree
| leaf => leaf
| node l v r recl recr => node(recr, v, recl)
```

Look at the `node` arms closely: five binders. First the three
constructor arguments `l`, `v`, `r`; then — because *two* of those
arguments are recursive — two recursive results, `recl` and `recr`,
in the same order as the arguments they belong to. In `size`, `recl`
is `size(l)` and `recr` is `size(r)`.

A quick sanity computation (draw it!):

```text
theorem mirror_concrete
  : mirror(node(leaf, 1, node(leaf, 2, leaf)))
    = node(node(leaf, 2, leaf), 1, leaf) := by
  refl
```

Now run the recipe on the `data Tree` declaration to get its proof
principle. `leaf`: no arguments, no hypotheses — prove `P(leaf)`
outright. `node`: bind `l`, `v`, `r`; recursive arguments `l` and `r`
mean **two** induction hypotheses, `ihl : P(l)` and `ihr : P(r)`. To
prove something about a node, you may assume it about *both* subtrees.
The arm reads `| node l v r ihl ihr =>` — constructor arguments
first, then the hypotheses, mirroring `defrec` exactly.

For reference, the recipe applied to everything you've met:

| Declaration | Arms of `induction ... with` |
|---|---|
| `Nat`: `0`, `succ(Nat)` | `\| zero =>` · `\| succ k ih =>` |
| `List`: `nil`, `cons(Nat, List)` | `\| nil =>` · `\| cons h t ih =>` |
| `Tree`: `leaf`, `node(Tree, Nat, Tree)` | `\| leaf =>` · `\| node l v r ihl ihr =>` |

The shape of the proof is the shape of the data. Once you can read a
`data` declaration, you can read off the skeleton of every proof about
it — before you know what the theorem says.

## 11.5 Mirror preserves size

The chapter's centerpiece: flipping a tree doesn't change how many
nodes it has.

```text
theorem mirror_size_demo (t : Tree) : size(mirror(t)) = size(t) := by
  induction t with
  | leaf =>
      refl
  | node l v r ihl ihr =>
      simp
      rewrite -> ihl
      rewrite -> ihr
      rewrite -> add_comm {n := size(l); m := size(r)}
      refl
```

The `leaf` arm computes. The `node` arm opens with both hypotheses in
hand — `ihl : size(mirror(l)) = size(l)` and
`ihr : size(mirror(r)) = size(r)` — and `simp` computes `mirror`,
then `size`, on the left:

```text
ihl : ..., ihr : ...
  |-  succ(add(size(mirror(r)), size(mirror(l)))) = succ(add(size(l), size(r)))
```

Read the left side: the mirror put *r*'s size first — the subtrees
traded places. The two rewrites clean up the mirrors
(`rewrite -> ihl` turns `size(mirror(l))` into `size(l)`, likewise
`ihr`), leaving

```text
succ(add(size(r), size(l))) = succ(add(size(l), size(r)))
```

— true, but not *identical*: the sum is flipped, and this is
arithmetic, not tree structure. So the last step borrows Chapter 9's
crown jewel from the library, instantiated to say exactly
`add(size(l), size(r)) = add(size(r), size(l))`:
`rewrite -> add_comm {n := size(l); m := size(r)}`, then `refl`. A
structural induction with an equational cameo — most interesting
proofs about data end this way, structure and arithmetic doing one
step each.

## 11.6 Common mistakes

Run [`code/ch11-mistakes.ctea`](code/ch11-mistakes.ctea) — intended
to fail. All three mistakes are misreadings of the recipe, and the
checker recites the correct reading back each time.

**Mistake 1: arms out of declaration order.** `List` declares `nil`
first, so the `nil` arm comes first — the proof below leads with
`cons`:

```text
error: docs/book/code/ch11-mistakes.ctea:14: theorem `arms_out_of_order` failed: induction arm `cons` does not match constructor `nil`; arms must follow the declaration order
  note: target: append(l, nil) = l
```

The declaration is the source of truth, for order as for everything
else.

**Mistake 2: forgetting the induction hypothesis binder.**
`| cons h t =>` looks plausible — two arguments, two names:

```text
error: docs/book/code/ch11-mistakes.ctea:25: theorem `missing_binders` failed: induction arm `cons` expects 3 binder(s): one per constructor argument, then one induction hypothesis per recursive argument
  note: target: append(l, nil) = l
```

Two constructor arguments *plus one hypothesis* for the recursive one:
three binders. If you forget, the checker's message is the recipe of
Section 11.2, word for word.

**Mistake 3: one hypothesis where two are owed.** The tree version of
the same miscount — `| node l v r ih =>`:

```text
error: docs/book/code/ch11-mistakes.ctea:44: theorem `one_ih_for_node` failed: induction arm `node` expects 5 binder(s): one per constructor argument, then one induction hypothesis per recursive argument
  note: target: le(0, size(t))
```

Three arguments, two of them recursive: five binders. When in doubt,
don't count from memory — count from the `data` declaration. (And
remember Chapter 9's freshness rule: all these binders must be new
names. `| node l v r ihl ihr =>` inside a theorem that already has a
variable `v` will be rejected as shadowing.)

## 11.7 Exercises

Open [`code/ch11-exercises.ctea`](code/ch11-exercises.ctea). The data
types and definitions are provided — including `leaves`, which counts
a tree's leaves. Before each proof, say the skeleton out loud: which
variable, which arms, how many binders.

- **Exercise 11.1** a concrete `size` — count first, then `refl`.
- **Exercise 11.2** `append(append(l1, l2), l3) = append(l1, append(l2, l3))`
  — associativity of append, same skeleton as `length_append_demo`.
- **Exercise 11.3** `sum(append(l1, l2)) = add(sum(l1), sum(l2))` —
  like `length_append_demo`, plus one arithmetic cameo:
  `add_assoc {n := h; m := sum(t); k := sum(l2)}`.
- **Exercise 11.4** `mirror(mirror(t)) = t` — mirroring is its own
  undo. Two hypotheses, two rewrites, no arithmetic at all.
- **Exercise 11.5** `leaves(mirror(t)) = leaves(t)` — mirror
  preserves the leaf count too; model it on `mirror_size_demo`.
- **Exercise 11.6 (challenge)** `leaves(t) = succ(size(t))` — every
  tree has exactly one more leaf than it has nodes. (Surprised? Check
  it on `mirror_concrete`'s tree first.) The arithmetic cameo this
  time is `add_succ_right {n := size(l); m := size(r)}`.

Solutions: [`code/ch11-solutions.ctea`](code/ch11-solutions.ctea).

---

*Next: [Chapter 12 — Strong Induction, and Where to Go Next](12-strong-induction.md).
Ordinary induction hands you the claim for the rung just below. But
some definitions look* two *rungs down, or further — and for those,
you'll want the claim for every rung below. One last principle, and
then: the view from the top of the ladder.*
