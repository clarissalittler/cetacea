# Relations and Their Properties (CS 250 Module 1, end)

A *relation* on a set $A$ is a subset of $A \times A$. Module 1
introduces the three properties that show up over and over: reflexive,
symmetric, transitive. A relation that is all three is an *equivalence
relation*.

Cetacea has no built-in support for relations as objects (there's no
`Relation T` type), but you can model a relation as a binary predicate
`R : T -> T -> Prop`. Most of what Module 1 says about relations
translates to theorems quantified over a generic `R`.

## Relation properties as definitions

Cetacea has no built-in `Relation T` type, but formula definitions can
take predicate parameters. That lets us write the usual Module 1
properties directly:

```text
def Reflexive (A : Type) (R : A -> A -> Prop) : Prop := forall x : A, R(x, x)

def Symmetric (A : Type) (R : A -> A -> Prop) : Prop := forall x y : A, R(x, y) -> R(y, x)

def Transitive (A : Type) (R : A -> A -> Prop) : Prop := forall x y z : A, R(x, y) -> R(y, z) -> R(x, z)
```

When you use `Reflexive(R)`, the type parameter `A` is inferred from
the predicate argument `R`. You can also pass a small inline predicate
lambda, such as `Reflexive(fun x y : Person => x = y)`.

## Reflexivity, symmetry, transitivity inline

The companion file is [`code/06_relations.ctea`](code/06_relations.ctea).

```text
mode constructive

sort Thing

def Reflexive (A : Type) (R : A -> A -> Prop) : Prop := forall x : A, R(x, x)

def Symmetric (A : Type) (R : A -> A -> Prop) : Prop := forall x y : A, R(x, y) -> R(y, x)

def Transitive (A : Type) (R : A -> A -> Prop) : Prop := forall x y z : A, R(x, y) -> R(y, z) -> R(x, z)

-- A theorem with R abstract: if R is reflexive, every R(a, a) holds.
theorem refl_self
  (A : Type)
  (R : A -> A -> Prop)
  (a : A)
  : Reflexive(R) -> R(a, a) := by
  intro hrefl
  exact hrefl a

-- Equality is reflexive at every type.
theorem eq_is_refl (A : Type) (x : A) : x = x := by
  refl
```

`R(a, a)` is the canonical "use" of reflexivity, and the proof is
`hrefl a` — instantiating the universal at `a`.

## A reflexivity-from-witness puzzle

Module 1 Exercise 12 (the "classic bad argument") is about why
symmetry + transitivity does *not* imply reflexivity. The textbook's
counterexample is a relation on `{1, 2, 3}` that's symmetric and
transitive but isn't reflexive (because some element is not related to
*anything*).

The textbook's flawed argument *does* go through if every element has
*some* witness. We can prove that:

```text
theorem refl_from_witness
  (A : Type)
  (R : A -> A -> Prop)
  (x : A)
  : Symmetric(R)
    -> Transitive(R)
    -> (exists y : A, R(x, y))
    -> R(x, x) := by
  intro hsym
  intro htrans
  intro hwit
  cases hwit with
  | intro y hxy =>
      apply htrans x y x
      exact hxy
      apply hsym x y
      exact hxy
```

Reading the proof:

1. Open the existential to get a witness `y` and `hxy : R(x, y)`.
2. To prove `R(x, x)`, apply transitivity at `(x, y, x)`.
3. The first premise of trans is `R(x, y)` — that's `hxy`.
4. The second premise is `R(y, x)`. We get that from symmetry: from
   `R(x, y)`, conclude `R(y, x)`. So `apply hsym x y` then `exact hxy`.

The definitions use multi-binders such as `forall x y : A, ...`, which
parse as nested quantifiers. `apply htrans x y x` works by unfolding the
transparent definition in the hypothesis and passing three forall
arguments. One parser limitation remains: you cannot wrap proof
subexpressions in parens like `apply (htrans x y x)`.

## Equivalence relations and equality

Equality is the canonical equivalence relation:

```text
theorem eq_refl_demo (A : Type) (x : A) : x = x := by
  refl

theorem eq_sym_demo (A : Type) (x y : A) : x = y -> y = x := by
  exact eq_symm

theorem eq_trans_demo (A : Type) (x y z : A)
  : x = y -> y = z -> x = z := by
  exact eq_trans
```

`eq_symm` and `eq_trans` are imported from `std/eq.ctea`.

If you have your own equivalence relation (say, modular congruence,
which CS 250 Module 6 introduces), you can axiomatize its three
properties and then use them. Cetacea has no Modular type built in, so
you'd start something like:

```text
sort Z   -- the integers, abstractly
pred Cong(Z, Z)   -- "x ≡ y (mod m)" for a fixed implicit modulus

axiom cong_refl  : forall x : Z, Cong(x, x)
axiom cong_sym
  : forall x : Z, forall y : Z, Cong(x, y) -> Cong(y, x)
axiom cong_trans
  : forall x : Z, forall y : Z, forall z : Z,
      Cong(x, y) -> Cong(y, z) -> Cong(x, z)
```

This is enough to prove things like "Cong gives an equivalence
relation" or to do basic algebra modulo `m`. You'd be working in a
purely axiomatic theory at that point — Cetacea doesn't *know* anything
about modular arithmetic, you'd have given it the axioms by hand. Most
of CS 250 Module 6 is out of reach because of this.

## Try it

- Prove that the diagonal relation `D(x, y) = (x = y)` is reflexive,
  symmetric, and transitive.
- Prove: if `R` is symmetric and transitive, then for any `x`, the set
  `{ y : A | R(x, y) }` is closed under relatedness. In Cetacea terms,
  state and prove `forall y z : A, R(x, y) -> R(x, z) -> R(y, z)`.
  This is the key fact behind equivalence classes.
- Prove that the empty relation `Empty(x, y) := False` is symmetric and
  transitive (trivially) but not reflexive (unless the domain is empty).
