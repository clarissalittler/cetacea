# Modular Arithmetic and Congruences (CS 250 Module 6)

Module 6 defines divisibility, then congruence mod $m$ as
"$x \equiv y \pmod m$ iff $m \mid x - y$", and shows that congruence is
an equivalence relation compatible with addition and multiplication.
Tutorial `06_relations.md` said most of this was out of reach and could
only be axiomatized. That is no longer true: `std/modular.ctea` now
proves essentially all of it, with exactly **one** axiom, and this
tutorial explains what was formalized, how, and where the one honest
gap is.

The companion file is [`code/09_modular.ctea`](code/09_modular.ctea).

## Divisibility is an existential

The course definition — $a \mid b$ iff $b = ak$ for some $k$ —
translates directly:

```text
def modular.Divides (a : Nat) (b : Nat) : Prop := exists k : Nat, b = mul(a, k)
```

So a divisibility proof is a *witness* plus a *computation*. That is
the whole game:

```text
theorem divides_4_20 : modular.Divides(4, 20) := by
  unfold modular.Divides
  exists 5
  refl
```

`unfold modular.Divides` exposes the existential, `exists 5` names the witness,
and `refl` checks `20 = mul(4, 5)` by actually computing the
multiplication. If you give a wrong witness, `refl` fails — the checker
does the arithmetic, not you.

`std/modular.ctea` proves the Module 6 divisibility facts generically:

| Theorem | Statement |
|---|---|
| `modular.divides_refl` | $a \mid a$ |
| `modular.divides_zero` | $a \mid 0$ |
| `modular.one_divides` | $1 \mid a$ |
| `modular.divides_trans` | $a \mid b$ and $b \mid c$ imply $a \mid c$ |
| `modular.divides_add` | $d \mid a$ and $d \mid b$ imply $d \mid a + b$ |
| `modular.divides_mul` | $d \mid a$ implies $d \mid ak$ |

The sum and chain rules can be used either by passing the premise
proofs as arguments to `exact`, or by `apply` followed by the two
folded `modular.Divides` subgoals:

```text
theorem divides_3_sum : modular.Divides(3, add(12, 9)) := by
  exact modular.divides_add {d := 3; a := 12; b := 9} modular.divides_3_12 divides_3_9

theorem divides_3_sum_by_apply : modular.Divides(3, add(12, 9)) := by
  apply modular.divides_add
  exact modular.divides_3_12
  exact divides_3_9

theorem divides_3_18 : modular.Divides(3, 18) := by
  exact modular.divides_trans {a := 3; b := 6; c := 18} divides_3_6 divides_6_18
```

## Congruence, without subtraction

Here is the formalization choice worth being honest about. The course
defines $x \equiv y \pmod m$ as $m \mid x - y$. Cetacea's `Nat` has
**truncated** subtraction: `sub(3, 7)` is `0`, not $-4$. Translating
the course definition literally would make congruence mean
$m \mid \dot{x - y}$, which is *wrong* — e.g. `sub(3, 7) = 0` and
everything divides 0, so 3 would be "congruent" to 7 mod anything.
You would have to bolt on a side condition or take the symmetric
conjunction, and either way the proofs fight the truncation constantly.

Instead, `std/modular.ctea` uses a subtraction-free formulation that is
equivalent over the integers:

```text
def modular.ModEq (m : Nat) (x : Nat) (y : Nat) : Prop := exists a b : Nat, add(x, mul(m, a)) = add(y, mul(m, b))
```

Read `modular.ModEq(m, x, y)` as $x \equiv y \pmod m$: *$x$ and $y$ become
equal after each is padded by some multiple of $m$*. If $x \geq y$ and
$m \mid x - y$, take $a = 0$ and $b = (x-y)/m$; conversely
$x + ma = y + mb$ gives $x - y = m(b - a)$ over $\mathbb{Z}$. The
definition is manifestly symmetric in $x$ and $y$ (swap the witnesses),
and it is constructively pleasant: every proof is again witnesses plus
computation.

The library calls this relation `modular.ModEq`. The module qualifier keeps
it separate from local predicates such as `Cong` in the relations unit.
The course uses the qualified prelude, so library declarations and student
proofs can share short names without colliding.

Concrete congruences read like clock arithmetic. 27 o'clock is
3 o'clock because $27 + 12 \cdot 0 = 3 + 12 \cdot 2$:

```text
theorem modeq_27_3_mod_12 : modular.ModEq(12, 27, 3) := by
  unfold modular.ModEq
  exists 0
  exists 2
  refl
```

A multi-binder existential is proved with one `exists` per binder, and
`refl` again does all the arithmetic.

## Congruence is an equivalence relation — proved, not axiomatized

This is the payoff of choosing the symmetric definition. All three
equivalence laws are *theorems* in `std/modular.ctea`, with no axioms:

- `modular.modeq_refl` — witnesses $a = b = 0$.
- `modular.modeq_sym` — swap the witnesses, flip the equation with `eq.eq_symm`.
- `modular.modeq_trans` — the interesting one. From $x + ma = y + mb$ and
  $y + mc = z + md$, the combined witnesses are $a + c$ and $d + b$:
  pad the first equation by $mc$, the second by $mb$, and re-associate
  until the middle $y$-terms line up. The proof is a chain of
  `rewrite` steps through `nat.add_assoc`, `nat.add_comm`, and distributivity.

Compatibility with arithmetic is also fully proved:

- `modular.modeq_add` — add two congruences componentwise.
- `modular.modeq_scale`, `modular.modeq_scale_right` — multiply both sides by a
  constant.
- `modular.modeq_mul` — multiply two congruences; derived by scaling each one
  and chaining through the midpoint $yu$ with `modular.modeq_trans`.
- `modular.modeq_add_multiple` — $x + mk \equiv x$: adding a multiple of the
  modulus never changes the residue class.

To make those proofs possible, `std/modular.ctea` first proves a block
of `Nat` lemmas that `std/nat.ctea` doesn't have yet: `modular.add_left_comm`,
`modular.add_middle_swap`, `modular.add_cancel_left`, both distributivity laws
(`modular.mul_add_left`, `modular.mul_add_right`), `modular.mul_comm`, and `modular.mul_assoc`. They
are ordinary induction-plus-rewrite proofs and are exported for reuse.

## Modular arithmetic without computing remainders

Module 6's punchline is that you can compute with *residues* instead
of numbers. The compatibility theorems are exactly that technique.
From $6 \equiv 1 \pmod 5$ you get $36 \equiv 1 \pmod 5$ without ever
dividing 36 by 5:

```text
theorem modeq_36_demo : modular.ModEq(5, mul(6, 6), mul(1, 1)) := by
  exact modular.modeq_mul {m := 5; x := 6; y := 1; u := 6; v := 1} modeq_6_1_mod_5 modeq_6_1_mod_5
```

Note the statement is `modular.ModEq(5, mul(6, 6), mul(1, 1))`, not
`modular.ModEq(5, 36, 1)`: theorem matching is syntactic, and `modular.modeq_mul`'s
conclusion has the shape `modular.ModEq(m, mul(x, u), mul(y, v))`. The
companion file proves `modular.ModEq(5, 36, 1)` too, directly by witnesses
($36 + 5\cdot0 = 1 + 5\cdot7$) — pick whichever shape your statement
needs.

The same works additively (`modeq_sum_demo` proves
$8 + 9 \equiv 3 + 4 \pmod 5$), and structurally: the companion file
proves from scratch that `succ` respects congruence, which is the
template for every hand-rolled `modular.ModEq` proof — `simp at h`, unpack the
two witnesses with nested `cases`, provide new witnesses, close with
`simp`/`rewrite`/`refl`.

## The one axiom, and why it's there

The bridge between the two notions is where the honesty comes in.
One direction is a theorem:

```text
theorem modular.divides_to_modeq_zero (m x : Nat) : modular.Divides(m, x) -> modular.ModEq(m, x, 0)
```

The converse — if $x \equiv 0 \pmod m$ then $m \mid x$ — is *true*,
but its proof needs machinery Cetacea's library doesn't have yet. From
$x + ma = mb$ you must produce $k$ with $x = mk$; the witness is
$k = b - a$, and justifying it requires an order argument ($a \le b$
when $m > 0$, plus the degenerate $m = 0$ case) and cancellation lemmas
relating truncated `sub` to `add`. Rather than fake it, the library
states it as an axiom with a comment saying exactly that:

```text
axiom modular.modeq_zero_to_divides (m x : Nat) : modular.ModEq(m, x, 0) -> modular.Divides(m, x)
```

Cetacea tracks axiom use per theorem, so anything downstream is
labeled. From the companion file's output:

```text
accepted theorem modeq_12_0_mod_3 (constructive)
accepted theorem residue_zero_divides (constructive; axioms: modular.modeq_zero_to_divides)
```

The first line (the proved direction) is axiom-free; the second wears
its dependency. This is the disciplined way to use axioms: the checker,
not the reader's trust, keeps score. Everything else in
`std/modular.ctea` — all equivalence laws, all compatibility laws —
reports `(constructive)` with no axiom list.

## Parity is just mod 2

A quick application of the general lemmas, no new proofs needed:

```text
theorem even_plus_even (a b : Nat)
  : modular.Divides(2, a) -> modular.Divides(2, b) -> modular.Divides(2, add(a, b)) := by
  exact modular.divides_add
```

Even + even = even, and even × anything = even (`modular.divides_mul`), each
in one line, because bare `exact` can infer the instantiation from the
goal here.

## Try it

The companion file ends with four exercises stated with `sorry`, so the
file checks but reports them as `incomplete theorem`. Complete the drafts:

1. `exercise_divides_5_35` — find the witness.
2. `exercise_modeq_23_3_mod_10` — 23 and 3 share a last digit; find
   the two padding witnesses (one is 0).
3. `exercise_modeq_double` — doubling respects congruence. One `exact`
   with `modular.modeq_add`, using the same hypothesis twice.
4. `exercise_divides_sum_of_multiples` — $d \mid dk + dj$. Unfold,
   give the witness `add(k, j)`, and rewrite with `modular.mul_add_right`.

Harder follow-ons, in the library rather than the companion file:

- Prove `modular.ModEq(m, x, y) -> modular.ModEq(m, add(x, k), add(y, k))` directly
  from `modular.modeq_add` and `modular.modeq_refl`.
- The textbook "casting out nines" fact $10 \equiv 1 \pmod 9$, then
  $100 \equiv 1 \pmod 9$ via `modular.modeq_mul`.
- If you want a real project: prove the axiom. You'll need lemmas
  connecting `sub`, `add`, and `le` (start with
  `le(a, b) -> add(a, sub(b, a)) = b`), the cancellation lemma
  `modular.add_cancel_left` (already proved in `std/modular.ctea`), and a case
  split on `m = 0`. When it's done, delete `axiom` and watch the
  `axioms:` annotations disappear from the CLI output.
