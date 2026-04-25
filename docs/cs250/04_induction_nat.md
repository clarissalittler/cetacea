# Natural-Number Induction (CS 250 Module 4 §6)

Cetacea has built-in `Nat`, with constructors `0` and `succ(n)`, plus
addition `add(n, m)`, multiplication `mul(n, m)`, truncated subtraction
`sub(n, m)`, and comparison `le(n, m)`. The `induction` tactic does
Module 4 §6's natural induction, exactly as advertised.

## Convention warning: addition recurses on the *left*

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

This means the "free" direction *flips*. In the textbook, $n + 0 = n$
falls out by definition, but $0 + n = n$ requires induction. In Cetacea
it's the other way: `add(0, n) = n` is the base case (one `simp` step),
and `add(n, 0) = n` is the one that needs induction. Don't fight this;
just notice it when you compare to the book.

The standard library has both worked out as `add_zero_left` and
`add_zero_right`. Read them side by side.

## A first proof: `add(n, 0) = n`

The companion file is [`code/04_induction_nat.ctea`](code/04_induction_nat.ctea).

```text
theorem add_zero_right_demo (n : Nat) : add(n, 0) = n := by
  induction n with
  | zero =>
      simp
      refl
  | succ k ih =>
      simp
      rewrite ih
      refl
```

Reading the proof:

- `induction n with | zero => ... | succ k ih => ...` is the literal
  form of Module 4's induction rule.
- In the `zero` arm the goal is `add(0, 0) = 0`. `simp` fires the
  built-in left-recursive equation `add(0, n) = n` to reduce it to
  `0 = 0`, which `refl` closes.
- In the `succ k ih` arm the goal is `add(succ(k), 0) = succ(k)`, with
  inductive hypothesis `ih : add(k, 0) = k`. `simp` fires the second
  equation, turning the goal into `succ(add(k, 0)) = succ(k)`. Then
  `rewrite ih` rewrites the right-hand `k` back to `add(k, 0)` (rewrite
  goes RHS-to-LHS in the goal), giving `succ(add(k, 0)) = succ(add(k, 0))`,
  and `refl` closes that.

## Commutativity of addition

```text
theorem add_comm_demo (n m : Nat) : add(n, m) = add(m, n) := by
  induction n with
  | zero =>
      simp
      rewrite add_zero_right {n := m}
      refl
  | succ n0 ih =>
      simp
      rewrite add_succ_right_rev {n := m; m := n0}
      rewrite ih
      refl
```

The full proof is also in `std/nat.ctea` as `add_comm`. The neat thing
to notice: every step is a *named* algebraic fact about `add`. The proof
is more or less a list of equational rewrites, the way you'd do
algebra on paper but with each step named.

The auxiliary `add_succ_right_rev` exists because `rewrite` only
matches the *right-hand side* of an equation in the goal. To go the
other direction you need the "reversed" equation. Both directions are
in `std/nat.ctea`.

## A textbook-style claim: `0 + n = n` (their `+`)

If you really want to prove things using the textbook's right-recursive
addition, you can axiomatize it. This is mostly an exercise — Cetacea's
built-in `add` is already there and the lemmas are already proved. But
it shows what happens when you commit to the textbook convention:

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

Notice we have to *axiomatize* the recursion equations rather than write
a recursive function — Cetacea has no `Definition` for recursive
functions over `Nat` outside the built-in `add`. For purposes of doing
the textbook exercises in Cetacea, this is fine for short proofs but
gets tedious; see `LIMITATIONS.md`.

## Module 4 Exercise 11: `0 · n = 0`

Multiplication is now built in. It follows the same left-recursive
convention as `add`:

```text
mul(0, n) = 0
mul(succ(n), m) = add(m, mul(n, m))
```

So the theorem `0 * n = 0` is definitional in Cetacea:

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
- Prove `succ_inj_via_add : forall n m : Nat, succ(n) = succ(m) -> n = m`.
  This one is hard without a `succ` injectivity rule built in — see
  `LIMITATIONS.md`.
- Define `double(n)` axiomatically as `add(n, n)` and prove
  `double(succ(n)) = succ(succ(double(n)))`. This is a cleaner
  variation on `add_succ_right`.
