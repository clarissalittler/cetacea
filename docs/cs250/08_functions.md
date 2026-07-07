# Functions as Graphs (CS 250 functions module)

The course defines a function `f : A -> B` as a special kind of
relation: a set of pairs that is *total* (every `x` has an image) and
*single-valued* (at most one image per `x`). Cetacea's `std/fun.ctea`,
imported by the prelude, takes exactly that view. A function is
represented by its **graph**, a two-place predicate `G : A -> B -> Prop`
where `G(x, y)` reads "`f(x) = y`".

The companion file is [`code/08_functions.ctea`](code/08_functions.ctea).

## The four definitions

`std/fun.ctea` defines, each parameterized by the two types and the
graph:

```text
def Total        (A : Type) (B : Type) (G : A -> B -> Prop) : Prop := forall x : A, exists y : B, G(x, y)
def SingleValued (A : Type) (B : Type) (G : A -> B -> Prop) : Prop := forall x : A, forall y1 y2 : B, G(x, y1) -> G(x, y2) -> y1 = y2
def Injective    (A : Type) (B : Type) (G : A -> B -> Prop) : Prop := forall x1 x2 : A, forall y : B, G(x1, y) -> G(x2, y) -> x1 = x2
def Surjective   (A : Type) (B : Type) (G : A -> B -> Prop) : Prop := forall y : B, exists x : A, G(x, y)
def Bijective    (A : Type) (B : Type) (G : A -> B -> Prop) : Prop := Injective(G) /\ Surjective(G)
```

These are the course definitions, translated one-for-one: total and
single-valued make a relation a function; injective and surjective
classify it; bijective packages injective and surjective together.

## Connecting a declared `func` to its graph

When you declare a function symbol, its graph is the predicate lambda
`fun x y : A => f(x) = y` when the input and output types are both
`A`. For mixed types, annotate each binder:

```text
func mother : Person -> Person
func age : Person -> Nat

fun (x : Person) (n : Nat) => age(x) = n
```

Any declared `func` is automatically total and single-valued in the
model, and both facts are *provable* about its graph:

```text
theorem mother_total : Total(fun x y : Person => mother(x) = y) := by
  unfold Total
  intro x
  exists mother(x)
  refl
```

Totality is a one-witness proof: the image of `x` is `mother(x)` itself.
Single-valuedness is two rewrites — if `mother(x) = y1` and
`mother(x) = y2` then `y1 = y2`. The companion file also proves
`age_total` and `age_single_valued` using the mixed graph syntax.

## The identity function

The identity function's graph relates `x` to `y` exactly when `x = y`.
The library proves `id_injective` and `id_surjective`, and packages the
bundle as `id_bijective`:

```text
theorem person_id_bijective : Bijective(fun x y : Person => x = y) := by
  exact id_bijective {A := Person}
```

For a proof written out by hand rather than by library reference, here
is successor-is-injective, which reduces to `succ_inj` from
`std/nat.ctea`:

```text
theorem succ_graph_injective : Injective(fun n m : Nat => succ(n) = m) := by
  unfold Injective
  intro x1
  intro x2
  intro y
  intro h1
  intro h2
  apply succ_inj
  rewrite -> h2
  exact h1
```

(Successor is *not* surjective — nothing maps to `0` — which is the
course's standard first example of the distinction.)

## Composition

Composition of functions is relation composition: the composite of
`F : A -> B` and `G : B -> C` relates `x` to `z` when some intermediate
`y` has `F(x, y)` and `G(y, z)`. The library proves the two classic
preservation theorems in this style:

- `compose_injective`: if `F` and `G` are injective, the composite
  relation is injective.
- `compose_surjective`: if `F` and `G` are surjective, every `z : C` is
  hit by the composite — `exists x, exists y, F(x, y) /\ G(y, z)`.

Applying them is a matter of supplying the graphs:

```text
theorem use_compose
  (F : Person -> Person -> Prop)
  (G : Person -> Person -> Prop)
  : Surjective(F) -> Surjective(G)
    -> forall z : Person, exists x : Person, exists y : Person, F(x, y) /\ G(y, z) := by
  intro hf
  intro hg
  exact compose_surjective {A := Person; B := Person; C := Person; F := F; G := G} hf hg
```

The proof of `compose_surjective` in `std/fun.ctea` is worth reading: it
is two nested `cases ... | intro ...` eliminations (get the preimage `y`
of `z` under `G`, then the preimage `x` of `y` under `F`) followed by
two `exists` introductions — precisely the informal proof from the
course, step for step.

## Try it

- Prove `Surjective(fun x y : Person => mother(x) = y) -> forall y :
  Person, exists x : Person, mother(x) = y` — it's just `unfold` and
  hypothesis shuffling, but it makes you read the definition.
- Prove that the constant-zero graph `fun n m : Nat => m = 0`... wait —
  is that even single-valued? Total? State and prove (or refute with a
  countermodel note) each of the four properties for it.
- Read `compose_injective` in `std/fun.ctea` and reconstruct the
  paper proof it encodes.
