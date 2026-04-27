# Sets (CS 250 Module 1 + Cardinality intermezzo)

Cetacea has a typed set theory: `Set T` is a type for any sort `T`, and
the basic constructors are `empty(T)`, `singleton(x)`, `union(A, B)`,
`inter(A, B)`, `diff(A, B)`, `compl(A)`, `univ(T)`, and
`powerset(A)`. You can also write nonempty finite sets as
`{alice, bob}`. Membership is `x in A`, subset is `A subset B`, equality
of sets is plain `=`. Set extensionality is an axiom (`set_ext` in
`std/set.ctea`). The standard library proves a small algebra of
set-theoretic identities.

Set-builder notation is supported:

```text
{ x : T | P(x) }
```

so you can name predicate-defined sets with transparent term
definitions. What Cetacea still does not have is cardinalities,
Cartesian products as set objects, or empty finite-set literals without
an explicit element type. Use `empty(T)` for the empty set and the course
Python tools for counting exercises; Cetacea is the right tool here for
proving identities about set operations, powersets, finite sets, and
predicate-defined sets.

## Subset, union, intersection

The companion file is [`code/05_sets.ctea`](code/05_sets.ctea).

```text
import ../../../std/prelude.ctea

mode constructive

sort Person

const alice : Person
const bob : Person
pred Tall(Person)

theorem alice_in_singleton : alice in singleton(alice) := by
  simp
  refl
```

`simp` knows `x in singleton(y)` reduces to `x = y`, so this becomes
`alice = alice`, which `refl` closes.

Finite set literals reduce to the same singleton and union facts:

```text
theorem bob_in_pair : bob in {alice, bob} := by
  simp
  right
  refl
```

Complements are typed relative to the element type's universal set:

```text
theorem complement_intro_demo
  (A : Set Person)
  : (alice in A -> False) -> alice in compl(A) := by
  intro h
  simp
  exact h
```

Set builders reduce by substituting the element into the defining
predicate:

```text
def TallSet : Set Person := { x : Person | Tall(x) }

theorem alice_in_tall_set : Tall(alice) -> alice in TallSet := by
  intro h
  simp
  exact h
```

```text
theorem subset_refl_demo
  (T : Type)
  (A : Set T)
  : A subset A := by
  simp
  intro x
  intro hx
  exact hx
```

`simp` rewrites `A subset A` into the equivalent `forall x, x in A -> x in A` (this is what `simp` does for subset). Then it's a one-liner.

## Set extensionality

`set_ext` is an axiom: from `forall x, x in A <-> x in B`, conclude
`A = B`. This is the standard way to prove two sets are equal.

```text
theorem inter_comm_demo
  (T : Type)
  (A B : Set T)
  : inter(A, B) = inter(B, A) := by
  apply set_ext
  intro x
  simp
  split
  intro hx
  split
  exact hx.right
  exact hx.left
  intro hx
  split
  exact hx.right
  exact hx.left
```

This is in the standard library as `inter_comm`. Re-deriving it gives
you a feel for the rhythm: `apply set_ext`, `intro x`, `simp`, then
prove the biconditional in each direction.

The full `std/set.ctea` is worth reading as a small textbook on its
own. It does:

- Subset is reflexive, transitive, antisymmetric.
- Empty is a subset of everything.
- Intersection is commutative, associative, has empty as zero.
- Union is commutative, associative, has empty as identity.
- Subset properties of union and intersection.
- Difference and disjointness lemmas.
- Powerset introduction, elimination, and monotonicity.

## A larger CS 250 problem: distributivity

CS 250 Module 1 Exercise 8 asks you to prove
$A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$ by showing both
inclusions. In Cetacea:

```text
theorem inter_union_distrib
  (T : Type)
  (A B C : Set T)
  : inter(A, union(B, C)) = union(inter(A, B), inter(A, C)) := by
  apply set_ext
  intro x
  simp
  split
  -- inter(A, union(B, C)) ⊆ union(inter(A, B), inter(A, C))
  intro hx
  cases hx.right with
  | left hxB =>
      left
      split
      exact hx.left
      exact hxB
  | right hxC =>
      right
      split
      exact hx.left
      exact hxC
  -- union(inter(A, B), inter(A, C)) ⊆ inter(A, union(B, C))
  intro hx
  cases hx with
  | left hxAB =>
      split
      exact hxAB.left
      left
      exact hxAB.right
  | right hxAC =>
      split
      exact hxAC.left
      right
      exact hxAC.right
```

Reading this proof, you can see the underlying skeleton from CS 250:
"introduce an arbitrary element, argue both directions of containment."
Cetacea makes you commit to which direction at each step.

## Powersets

For powersets, `simp` turns membership into subset:

```text
theorem powerset_mono_demo
  (A B : Set Person)
  : A subset B -> powerset(A) subset powerset(B) := by
  intro hAB
  simp
  intro S
  intro hSA
  intro x
  intro hx
  apply hAB
  apply hSA
  exact hx
```

## Try it

- Module 1 Exercise 9: `A ⊆ B -> P(A) ⊆ P(B)` is now direct:
  `A subset B -> powerset(A) subset powerset(B)`. The proof is the same
  element-subset argument as on paper.
- Re-prove `union_comm` from scratch (without using the imported
  version).
- Module 1 Exercise 10 (inclusion-exclusion) is **not** doable directly
  in Cetacea — it requires arithmetic on cardinalities and Cetacea has
  no notion of "cardinality of a set."
