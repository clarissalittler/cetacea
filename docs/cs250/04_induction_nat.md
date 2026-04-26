# Natural-Number Induction (CS 250 Module 4 §6)

Cetacea has built-in `Nat`, with constructors `0` and `succ(n)`, plus
addition `add(n, m)`, multiplication `mul(n, m)`, truncated subtraction
`sub(n, m)`, and comparison `le(n, m)`. The `induction` tactic does
Module 4 §6's natural induction, exactly as advertised.

## Convention note: arithmetic simplification accepts both directions

The CS 250 textbook defines addition by recursion on the **second**
argument:

$$
n + 0 = n
\qquad
n + \text{succ}(m) = \text{succ}(n + m)
$$

Cetacea's built-in `add` recurses on the **first** argument:

$$
\text{add}(0, n) = n
\qquad
\text{add}(\text{succ}(n), m) = \text{succ}(\text{add}(n, m))
$$

The simplifier now recognizes both orientations. The left-recursive
equations are still the primitive implementation, but the textbook
right-recursive equations also compute:

```text
add(n, 0) = n
add(n, succ(m)) = succ(add(n, m))
```

The standard library has both worked out as `add_zero_left` and
`add_zero_right`.

## A direct computation proof: `add(n, 0) = n`

The companion file is [`code/04_induction_nat.ctea`](code/04_induction_nat.ctea).

```text
theorem add_zero_right_demo (n : Nat) : add(n, 0) = n := by
  simp
  refl
```

`simp` reduces the arithmetic expression, and `refl` closes the resulting
identity.

## Commutativity of addition

```text
theorem add_comm_demo (n m : Nat) : add(n, m) = add(m, n) := by
  induction n with
  | zero =>
      simp
      refl
  | succ n0 ih =>
      simp
      rewrite ih
      refl
```

The full proof is also in `std/nat.ctea` as `add_comm`. The neat thing
to notice: `simp` handles the recursive computation in each branch, and
the induction hypothesis supplies the remaining algebraic step.

## A custom unary recursive definition

For recursion driven by one natural number, use `defrec`:

```text
defrec double (n : Nat) : Nat
| zero => 0
| succ k rec => succ(succ(rec))

theorem double_succ_demo (n : Nat)
  : double(succ(n)) = succ(succ(double(n))) := by
  simp
  refl
```

The successor arm receives the predecessor `k` and the recursive result
`rec`, so the definition is structurally recursive. `simp` computes the
zero case and the successor case.

## A custom right-recursive addition

If you want a second addition-like operation with the textbook's
right-recursive equations, you can axiomatize it. `defrec` handles
unary recursion, but it does not define binary operations such as
addition directly. This example is mostly an exercise, because Cetacea's
built-in `add` already computes these equations:

```text
mode constructive

func myadd : Nat -> Nat -> Nat

axiom myadd_zero_right (n : Nat) : myadd(n, 0) = n
axiom myadd_succ_right (n m : Nat) : myadd(n, succ(m)) = succ(myadd(n, m))

-- The reversed axiom for use with rewrite, derived.
theorem myadd_succ_right_rev (n m : Nat)
  : succ(myadd(n, m)) = myadd(n, succ(m)) := by
  rewrite myadd_succ_right {n := n; m := m}
  refl

theorem myadd_zero_n (n : Nat) : myadd(0, n) = n := by
  induction n with
  | zero =>
      exact myadd_zero_right
  | succ k ih =>
      rewrite myadd_succ_right_rev {n := 0; m := k}
      rewrite ih
      refl
```

Notice we still have to *axiomatize* these binary recursion equations
rather than write a binary recursive function. For purposes of doing the
textbook exercises in Cetacea, this is fine for short proofs but gets
tedious; see `LIMITATIONS.md`.

## Module 4 Exercise 11: `0 · n = 0`

Multiplication is built in. Like addition, `simp` recognizes both the
left-recursive equations and the textbook right-recursive equations:

```text
mul(0, n) = 0
mul(succ(n), m) = add(m, mul(n, m))
mul(n, 0) = 0
mul(n, succ(m)) = add(n, mul(n, m))
```

So both `0 * n = 0` and `n * 0 = 0` are direct computation proofs in
Cetacea:

```text
theorem zero_mul_n_builtin (n : Nat) : mul(0, n) = 0 := by
  simp
  refl
```

The *textbook-style* exercise is still useful if we axiomatize a
right-recursive multiplication:

```text
func mymul : Nat -> Nat -> Nat

axiom mymul_zero_right (n : Nat) : mymul(n, 0) = 0
axiom mymul_succ_right (n m : Nat)
  : mymul(n, succ(m)) = add(mymul(n, m), n)

theorem zero_mymul_n (n : Nat) : mymul(0, n) = 0 := by
  induction n with
  | zero =>
      exact mymul_zero_right
  | succ k ih =>
      -- mymul(0, succ(k))
      --   = add(mymul(0, k), 0)   by mymul_succ_right
      --   = mymul(0, k)           by add_zero_right
      --   = 0                   by ih
      apply eq_trans {A := Nat; x := mymul(0, succ(k)); y := mymul(0, k); z := 0}
      apply eq_trans {A := Nat; x := mymul(0, succ(k)); y := add(mymul(0, k), 0); z := mymul(0, k)}
      exact mymul_succ_right
      exact add_zero_right
      exact ih
```

The proof is a pure equational chain. `eq_trans` from `std/eq.ctea`
takes you from `x = y` and `y = z` to `x = z`. Stitching three
equational steps takes two `eq_trans` invocations.

The high-level point is the same as in the textbook once you use the
textbook recursion convention: you can't get $0 \cdot n = 0$ for free
from right-recursive multiplication. It takes induction even though the
symmetric $n \cdot 0 = 0$ falls out of the definition.

## Try it

- Prove `add_assoc(n, m, k) : add(add(n, m), k) = add(n, add(m, k))`.
  It's already in `std/nat.ctea`. Try writing it before reading the
  proof.
- Read `succ_inj` in `std/nat.ctea`, then try proving it yourself from
  `pred_succ`.
- Define `triple(n)` with `defrec` and prove
  `triple(succ(n)) = succ(succ(succ(triple(n))))`.
