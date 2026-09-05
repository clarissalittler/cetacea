# Chapter 20 — Divisibility and Clock Arithmetic

Companion files: [examples](hol-code/ch20-examples.ctea),
[exercises](hol-code/ch20-exercises.ctea),
[solutions](hol-code/ch20-solutions.ctea),
[mistakes](hol-code/ch20-mistakes.ctea),
[assignment policy](hol-code/ch20-solutions.ctea-assignment), and
[browser assignment](hol-code/ch20.ctea-task).

At 27 hours, a 12-hour clock shows 3. The two numbers differ by two complete
cycles. Congruence expresses this relationship without treating 27 and 3 as
equal natural numbers. This chapter develops divisibility witnesses and uses
congruence laws to prove that congruent inputs give congruent polynomial values.

Use the existential proofs of Chapter 4 and the natural-number arithmetic of
Chapter 9. Import `builtin:std/modular.ctea as M`. The assignment uses the
`fol+induction` profile; these proofs need no classical reasoning or new axioms.

## 20.1 Divisibility means a witness

`M.Divides(a, b)` means `exists k : Nat, b = mul(a, k)`. To prove that 4 divides
20, provide the multiplier 5:

```cetacea
theorem four_divides_twenty : M.Divides(4, 20) := by
  unfold M.Divides
  exists 5
  refl
```

The witness is part of the proof. Choosing 4 leaves the false equation
`20 = 16`; the checker rejects that attempt even though the original
existential statement has a different, correct witness.

Every number divides zero by choosing multiplier zero. This includes zero
itself. But zero does not divide a positive number: multiplying zero cannot
produce one.

| Law | Use |
| --- | --- |
| `M.divides_refl` | A number divides itself. |
| `M.divides_zero` | A number divides zero. |
| `M.divides_trans` | Chain two divisibility proofs. |
| `M.divides_add` | A common divisor divides a sum. |
| `M.divides_mul` | A divisor of `a` also divides `mul(a, k)`. |

Exercise 2 combines the last two laws to prove that a common divisor of `a`
and `b` divides `a + 3b` (written `add(a, mul(b, 3))`). The proof constructs
no new arithmetic axiom; it reuses checked witness-producing arguments.

## 20.2 Congruence without subtraction

Cetacea's `Nat` subtraction is truncated: `sub(2, 9) = 0`. Consequently,
defining congruence by divisibility of `sub(x, y)` would lose information
whenever `y` is larger. For example, it would wrongly suggest that 2 and 9
are congruent modulo 5.

The library instead defines:

```text
M.ModEq(m, x, y) := exists a b : Nat,
  add(x, mul(m, a)) = add(y, mul(m, b))
```

You may add a multiple of the modulus to either side until they meet.
For 27 and 3 modulo 12, choose `a = 0` and `b = 2`: both sides become 27.
The two witnesses have different jobs; their order matters.

```cetacea
theorem clock_27_3 : M.ModEq(12, 27, 3) := by
  unfold M.ModEq
  exists 0
  exists 2
  refl
```

`M.modeq_refl`, `M.modeq_sym`, and `M.modeq_trans` establish the equivalence
relation laws. `M.modeq_add` and `M.modeq_mul` combine two congruences to
obtain a congruence between sums or products.

## 20.3 Congruent inputs, congruent outputs

Suppose `M.ModEq(m, x, y)`. Apply `M.modeq_mul` to this fact twice to obtain
congruence of `mul(x, x)` and `mul(y, y)`. Then combine it with
`M.modeq_refl {m := m; x := 1}` using `M.modeq_add`. The result is congruence
of `x*x + 1` and `y*y + 1`, the claim in Exercise 3.

This is a proof for arbitrary inputs, rather than a test of particular
numbers. Keep the variables symbolic while proving the law. Large concrete
natural-number expressions can still exceed the checker's normalization
limits; see [checking limits](../CHECKING_LIMITS.md). Small clock examples and
symbolic algebra are the route used here. The separate
[concrete modular-square example](../hol/examples/modular_square.ctea) also
checks the congruence of `27*27` and `3*3` modulo 12.

## 20.4 What does modulus zero mean?

The library permits modulus zero. Its definition then says that there exist
`a` and `b` with `x + 0*a = y + 0*b`. This is precisely equality of `x` and
`y`. It is not a claim that a clock with zero positions is useful.

Exercise 4 proves the forward implication. Introduce the congruence premise,
use `simp at congruent` to expose and simplify the definition, then take apart
its two existential witnesses with `cases`. The remaining equality is the
goal. The backward implication follows from `M.modeq_refl` and rewriting.

HOL replay checks the simplification beneath those existential binders.
Arithmetic that refers to an existential witness cannot be moved outside
its scope; the checker distinguishes it from arithmetic on the outer `x`
and `y`.

## 20.5 Exercises and grading

| Exercise | Goal | Hint |
| --- | --- | --- |
| `ex20_1` | Prove 4 divides 20. | Supply multiplier 5. |
| `ex20_2` | Preserve a common divisor under `a + 3b`. | Multiply the second divisibility fact, then add. |
| `ex20_3` | Preserve congruence under `x*x + 1`. | Use multiplication and addition compatibility. |
| `ex20_4` | Congruence modulo zero implies equality. | Expose the premise and eliminate its two witnesses. |

Replace every `sorry`, retaining the names and statements. The assignment
checks all four exact signatures, rejects unfinished proofs and new axioms,
and enforces constructive `fol+induction` dependencies.

```sh
cargo run -q -p cetacea_cli -- --assignment docs/book/hol-code/ch20-solutions.ctea-assignment docs/book/hol-code/ch20-exercises.ctea
```

In the browser, open the exercise file and load `ch20.ctea-task` as the
assignment. The example selector also includes this chapter. Export or save
your current work before replacing it with an example.

Run the mistakes file to inspect a wrong multiplier, an impossible zero-divisor
claim, and an invalid congruence justified by no clock cycles. Rejection of
one attempted witness is not, by itself, a proof that no witness exists.
