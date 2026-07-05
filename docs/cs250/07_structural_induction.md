# Data Types and Structural Induction (CS 250 Modules 8–10)

Modules 8–10 of the course move from natural numbers to recursively
defined *structures*: sequences, recurrences, and inductively defined
sets like lists and trees, with structural induction as the proof
principle. Cetacea now supports this directly: you can declare an
inductive data type with `data`, define recursive functions over it with
`defrec`, and prove things about it with the same `induction ... with`
tactic you used for `Nat`.

The companion file is
[`code/07_structural_induction.ctea`](code/07_structural_induction.ctea).

One restriction up front: data types are **monomorphic**. There is no
`List A` for arbitrary `A` — the standard library's `List` is a list of
`Nat`, full stop. For course-sized examples that's usually enough; see
`LIMITATIONS.md`.

## Declaring a data type

```text
data Tree
| leaf
| node(Tree, Nat, Tree)
```

Each `|` line is a constructor. A constructor with no arguments (`leaf`)
becomes a constant; a constructor with arguments (`node`) becomes a
function. Argument types may mention the data type itself — those are
the *recursive* arguments, and they're what induction will recurse on.

The standard library already declares lists of naturals in
`std/list.ctea`, imported by the prelude:

```text
data List
| nil
| cons(Nat, List)
```

## Recursive definitions with `defrec`

`defrec`, which you met in tutorial 04 for `Nat`, now works over any
data type. One arm per constructor, in declaration order. In each arm
you bind one name per constructor argument, and then — after those —
one name per *recursive* argument, holding the already-computed
recursive result:

```text
defrec sum (l : List) : Nat
| nil => 0
| cons h t rec => add(h, rec)
```

In the `cons` arm, `h` and `t` are the constructor arguments and `rec`
is `sum(t)`. For `Tree` there are two recursive arguments, so two
recursive-result binders, in order:

```text
defrec size (t : Tree) : Nat
| leaf => 0
| node l v r recl recr => succ(add(recl, recr))
```

Both `simp` and `refl` compute `defrec` definitions. In fact `refl` now
normalizes both sides of an equality by itself, so pure computation
facts close in one step, no `simp` needed:

```text
theorem length_two_demo : length(cons(1, cons(2, nil))) = 2 := by
  refl

theorem size_node (l : Tree) (v : Nat) (r : Tree)
  : size(node(l, v, r)) = succ(add(size(l), size(r))) := by
  refl
```

`defrec` is still *unary* — it recurses over one argument, and the arm
bodies are terms built from the binders. Binary operations like
`append` are introduced as functions with their textbook recursion
equations as axioms, just as in tutorial 04. `std/list.ctea` does
exactly that:

```text
func append : List -> List -> List

axiom append_nil (l : List) : append(nil, l) = l
axiom append_cons (h : Nat) (t : List) (l : List)
  : append(cons(h, t), l) = cons(h, append(t, l))
```

## Structural induction on lists

`induction l with` takes one arm per constructor, in declaration order.
The arm binds the constructor arguments, then one induction hypothesis
per recursive argument. This is the Module 10 structural-induction rule,
verbatim: to prove `P(l)` for all lists, prove `P(nil)` and prove
`P(cons(h, t))` assuming `P(t)`.

The classic first theorem — length distributes over append — is
`length_append` in `std/list.ctea`; here it is re-derived:

```text
theorem length_append_demo (l1 : List) (l2 : List)
  : length(append(l1, l2)) = add(length(l1), length(l2)) := by
  induction l1 with
  | nil =>
      rewrite -> append_nil {l := l2}
      simp
      refl
  | cons h t ih =>
      rewrite -> append_cons {h := h; t := t; l := l2}
      simp
      rewrite -> ih
      refl
```

The shape of each arm: rewrite with the recursion equation for that
constructor, let `simp` compute the `defrec` and arithmetic parts, then
use the induction hypothesis. The companion file proves `sum_append` the
same way (it needs one extra `rewrite add_assoc` at the end — try to see
why before peeking).

Note the binders `h`, `t`, `ih` must be *fresh* names: reusing a name
already in scope (including the induction variable itself) is rejected
with `induction binder would shadow an existing variable`. That also
applies to `Nat` induction's `| succ k ih` binders now.

## Structural induction on trees

A tree node has two recursive arguments, so the `node` arm gets two
induction hypotheses, bound after the constructor arguments:

```text
theorem mirror_size (t : Tree) : size(mirror(t)) = size(t) := by
  induction t with
  | leaf =>
      rewrite -> mirror_leaf
      refl
  | node l v r ihl ihr =>
      rewrite -> mirror_node {l := l; v := v; r := r}
      simp
      rewrite -> ihl
      rewrite -> ihr
      rewrite -> add_comm {n := size(l); m := size(r)}
      refl
```

Here `mirror` (swap the subtrees, everywhere) is axiomatized with one
equation per constructor, since its result type is `Tree` rather than
`Nat`. The final `add_comm` step is the mathematical heart of the proof:
mirroring swaps the sizes of the two subtrees, and addition doesn't
care.

## Strong induction on Nat

Module 9's recurrences often need *strong* (course-of-values)
induction: to prove `P(succ(k))` you may assume `P(m)` for **every**
`m <= k`, not just for `k`. This is `strong_induction` in
`std/nat.ctea`:

```text
strong_induction (P : Nat -> Prop) (n : Nat)
  : P(0)
    -> (forall k : Nat, (forall m : Nat, le(m, k) -> P(m)) -> P(succ(k)))
    -> P(n)
```

It is a theorem, not a tactic — derived from ordinary induction via
`strong_induction_bounded` — so you use it with `apply`, giving `P` as a
predicate lambda explicitly (the checker cannot infer it from the goal):

```text
theorem zero_le_all (n : Nat) : le(0, n) := by
  apply strong_induction {P := fun m : Nat => le(0, m); n := n}
  simp
  trivial
  intro k
  intro hk
  simp
  trivial
```

After the `apply`, the first goal is `P(0)` and the second is the step;
in the step, `hk : forall m : Nat, le(m, k) -> P(m)` is the strong
hypothesis.

That example never uses `hk`. Where strong induction earns its keep is a
recurrence that reaches back further than one step. The companion file
axiomatizes `g(succ(k)) = g(pred(k))` — the recursion looks up `g` at
`pred(k)`, which is *not* the immediate predecessor of `succ(k)` — and
proves `g(n) = 0`:

```text
theorem g_always_zero (n : Nat) : g(n) = 0 := by
  apply strong_induction {P := fun m : Nat => g(m) = 0; n := n}
  exact g_zero
  intro k
  intro hk
  rewrite -> g_step {k := k}
  apply hk
  exact pred_le
```

Ordinary induction would hand you `P(k)` only; `apply hk` works for any
`m` once you show `le(m, k)`, which `pred_le : le(pred(n), n)` supplies.
The library also has `strong_induction_bounded`, `le_zero_inv`, and
`le_succ_inv` — the order lemmas its own proof is built from.

## Try it

- Prove `append_nil_length` from `std/list.ctea` yourself: no induction
  needed.
- Define `defrec depth (t : Tree) : Nat` (the depth of a tree) and prove
  `depth(node(leaf, v, leaf)) = 1` by `refl`.
- Prove `mirror(mirror(t)) = t` by structural induction on `t`, using
  the `mirror_leaf` and `mirror_node` axioms.
- Prove `le(length(l), length(append(l, l2)))`... is harder than it
  looks — you'll want lemmas relating `le` and `add` first. Good
  stretch exercise.
