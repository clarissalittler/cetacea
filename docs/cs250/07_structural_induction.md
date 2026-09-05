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
`list.List A` for arbitrary `A` — the standard library's `list.List` is a list of
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
data list.List
| list.nil
| list.cons(Nat, list.List)
```

## Recursive definitions with `defrec`

`defrec`, which you met in tutorial 04 for `Nat`, now works over any
data type. One arm per constructor, in declaration order. In each arm
you bind one name per constructor argument, and then — after those —
one name per *recursive* argument, holding the already-computed
recursive result:

```text
defrec sum (l : list.List) : Nat
| list.nil => 0
| list.cons h t rec => add(h, rec)
```

In the `list.cons` arm, `h` and `t` are the constructor arguments and `rec`
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
theorem length_two_demo : list.length(list.cons(1, list.cons(2, list.nil))) = 2 := by
  refl

theorem size_node (l : Tree) (v : Nat) (r : Tree)
  : size(node(l, v, r)) = succ(add(size(l), size(r))) := by
  refl
```

`defrec` is still *unary* — it recurses over one argument, and the arm
bodies are terms built from the binders. Binary operations like
`list.append` are introduced as functions with their textbook recursion
equations as axioms, just as in tutorial 04. `std/list.ctea` does
exactly that:

```text
func list.append : list.List -> list.List -> list.List

axiom list.append_nil (l : list.List) : list.append(list.nil, l) = l
axiom list.append_cons (h : Nat) (t : list.List) (l : list.List)
  : list.append(list.cons(h, t), l) = list.cons(h, list.append(t, l))
```

## Structural induction on lists

`induction l with` takes one arm per constructor, in declaration order.
The arm binds the constructor arguments, then one induction hypothesis
per recursive argument. This is the Module 10 structural-induction rule,
verbatim: to prove `P(l)` for all lists, prove `P(list.nil)` and prove
`P(list.cons(h, t))` assuming `P(t)`.

The classic first theorem — length distributes over append — is
`list.length_append` in `std/list.ctea`; here it is re-derived:

```text
theorem length_append (l1 : list.List) (l2 : list.List)
  : list.length(list.append(l1, l2)) = add(list.length(l1), list.length(l2)) := by
  induction l1 with
  | list.nil =>
      rewrite -> list.append_nil {l := l2}
      simp
      refl
  | list.cons h t ih =>
      rewrite -> list.append_cons {h := h; t := t; l := l2}
      simp
      rewrite -> ih
      refl
```

The shape of each arm: rewrite with the recursion equation for that
constructor, let `simp` compute the `defrec` and arithmetic parts, then
use the induction hypothesis. The companion file proves `sum_append` the
same way (it needs one extra `rewrite nat.add_assoc` at the end — try to see
why before peeking).

Note the binders `h`, `t`, `ih` must be *fresh* names: reusing a name
already in scope (including the induction variable itself) is rejected
with `induction binder would shadow an existing variable`. That also
applies to `Nat` induction's `| succ k ih` binders now.

## Structural induction on trees

A tree node has two recursive arguments, so the `node` arm gets two
induction hypotheses, bound after the constructor arguments:

```text
defrec mirror (t : Tree) : Tree
| leaf => leaf
| node l v r recl recr => node(recr, v, recl)

theorem mirror_size (t : Tree) : size(mirror(t)) = size(t) := by
  induction t with
  | leaf =>
      refl
  | node l v r ihl ihr =>
      simp
      rewrite -> ihl
      rewrite -> ihr
      rewrite -> nat.add_comm {n := size(l); m := size(r)}
      refl
```

Here `mirror` (swap the subtrees, everywhere) is an ordinary `defrec` —
recursive definitions can return any type, including the data type
itself — so `simp` computes its equations directly and no axioms are
involved. The final `nat.add_comm` step is the mathematical heart of the
proof: mirroring swaps the sizes of the two subtrees, and addition
doesn't care.

## Strong induction on Nat

Module 9's recurrences often need *strong* (course-of-values)
induction: to prove `P(succ(k))` you may assume `P(m)` for **every**
`m <= k`, not just for `k`. This is `nat.strong_induction` in
`std/nat.ctea`:

```text
nat.strong_induction (P : Nat -> Prop) (n : Nat)
  : P(0)
    -> (forall k : Nat, (forall m : Nat, le(m, k) -> P(m)) -> P(succ(k)))
    -> P(n)
```

It is a theorem, not a tactic — derived from ordinary induction via
`nat.strong_induction_bounded` — so you use it with `apply`, giving `P` as a
predicate lambda explicitly (the checker cannot infer it from the goal):

```text
theorem zero_le_all (n : Nat) : le(0, n) := by
  apply nat.strong_induction {P := fun m : Nat => le(0, m); n := n}
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
axiomatizes `g(succ(k)) = g(nat.pred(k))` — the recursion looks up `g` at
`nat.pred(k)`, which is *not* the immediate predecessor of `succ(k)` — and
proves `g(n) = 0`:

```text
theorem g_always_zero (n : Nat) : g(n) = 0 := by
  apply nat.strong_induction {P := fun m : Nat => g(m) = 0; n := n}
  exact g_zero
  intro k
  intro hk
  rewrite -> g_step {k := k}
  apply hk
  exact pred_le
```

Ordinary induction would hand you `P(k)` only; `apply hk` works for any
`m` once you show `le(m, k)`, which `pred_le : le(nat.pred(n), n)` supplies.
The library also has `nat.strong_induction_bounded`, `nat.le_zero_inv`, and
`nat.le_succ_inv` — the order lemmas its own proof is built from.

## Try it

- Prove `list.append_nil_length` from `std/list.ctea` yourself: no induction
  needed.
- Define `defrec depth (t : Tree) : Nat` (the depth of a tree) and prove
  `depth(node(leaf, v, leaf)) = 1` by `refl`.
- Prove `mirror(mirror(t)) = t` by structural induction on `t` — `simp`
  computes the `mirror` equations for you.
- Prove `le(list.length(l), list.length(list.append(l, l2)))`... is harder than it
  looks — you'll want lemmas relating `le` and `add` first. Good
  stretch exercise.
