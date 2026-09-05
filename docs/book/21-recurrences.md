# Chapter 21 — Recurrences and Closed Forms

Companion files: [examples](hol-code/ch21-examples.ctea),
[exercises](hol-code/ch21-exercises.ctea),
[solutions](hol-code/ch21-solutions.ctea),
[mistakes](hol-code/ch21-mistakes.ctea),
[assignment policy](hol-code/ch21-solutions.ctea-assignment), and
[browser assignment](hol-code/ch21.ctea-task).

A machine begins with two tokens and gains three tokens each tick. You can
compute its next value from the current one, or describe its value directly
from the number of ticks. A recurrence gives the first description. A closed
form gives the second. Induction proves that they agree at every index.

This chapter uses natural-number induction from Chapter 9 and recursive
definitions from Chapter 10. The assignment uses `fol+induction` and
constructive proofs. No new axioms or classical cases are needed.

## 21.1 The starting value is part of the rule

```cetacea
defrec tokens (n : Nat) : Nat
| zero => 2
| succ k rec => add(3, rec)
```

The variable `rec` is the already computed value `tokens(k)`. The definition
therefore says `tokens(0) = 2` and `tokens(succ(k)) = add(3, tokens(k))`.

| Ticks | 0 | 1 | 2 | 3 | 4 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Tokens | 2 | 5 | 8 | 11 | 14 |

Index zero comes before any increment. Starting at five and using the same
update rule gives a different sequence. Both the initial value and the update
rule are necessary to determine the sequence.

Computing the five entries in this table does not prove a claim about every
index. The examples include a sequence whose first two values are zero
but whose next value is one; the mistakes file tries the false universal claim.

## 21.2 Prove the closed form by induction

After `n` ticks, the proposed value is `add(2, mul(n, 3))`. More generally,
from an initial value `a` and increment `d`, propose `add(a, mul(n, d))`.

The induction has two jobs:

1. At zero, the formula reduces to `a`, matching the initial value.
2. At `succ(k)`, rewrite the recurrence and use the induction hypothesis
   `f(k) = add(a, mul(k, d))`. Rearrange addition to match
   `add(a, mul(succ(k), d))`.

The arithmetic step uses the checked multiplication equation
`N.mul_succ_left` and addition's associativity and commutativity. Exercise 2
isolates that algebra; Exercise 3 uses it in the full induction proof.

The law applies to natural-number values and increments. It does not cover
negative increments or arbitrary recurrence-solving methods.

## 21.3 Use a general theorem at one index

```cetacea
import builtin:std/hol/recurrences.ctea as R
```

`R.constant_step_closed` takes proofs of the initial value and recurrence,
and concludes a statement beginning `forall n : Nat`. To obtain a particular
value, first establish that universal statement:

```text
have all_ticks : forall n : Nat, f(n) = add(2, mul(n, 3)) := by
  apply R.constant_step_closed {f := f; a := 2; d := 3}
  exact initial
  exact step
exact all_ticks 4
```

At index four, the right side computes to fourteen. Exercise 1 practices this
pattern. Directly applying a theorem whose conclusion is universal to a goal
about a single index does not automatically supply the index; the intermediate
`have` makes the specialization explicit.

## 21.4 Why there can be only one solution

Suppose two sequences `f` and `g` have the same initial value and follow the
same update function `step`. At index zero, they agree by assumption. If they
agree at `k`, then `step(k, f(k)) = step(k, g(k))`. The recurrence equations
identify these expressions with their next values.

This is `R.recurrence_unique`. Its state type `A` is arbitrary. The update
function has type `Nat -> A -> A`: it may depend on the index as well as the
previous state. Uniqueness does not prove that a sequence exists; it compares
two functions already supplied with evidence for the recurrence.

The examples compare the recursive token counter with a separately named
closed form:

```cetacea
def formula (n : Nat) : Nat := add(2, mul(n, 3))
def advance (n previous : Nat) : Nat := add(3, previous)
```

These named definitions can be passed as `g := formula` and
`step := advance`. Their arity, argument types, and result types are checked.
A second example compares sequences of `ready` and `busy` states, using an
update that toggles the state. This demonstrates that uniqueness is not
limited to sequences of numbers.

## 21.5 Exercises and grading

| Exercise | Task | Suggested approach |
| --- | --- | --- |
| `ex21_1` | Derive the value fourteen at index four. | Obtain a universal closed form, then specialize it. |
| `ex21_2` | Check the proposed closed form's update equation. | Expand multiplication at a successor and rearrange addition. |
| `ex21_3` | Prove the constant-step closed form. | Introduce the recurrence evidence, then induct on the index. |
| `ex21_4` | Prove uniqueness for an arbitrary state type. | Induct and rewrite both update equations. |

Replace every `sorry`, keeping theorem names and statements. The solutions
show the suggested induction proofs. The checker verifies statements and
trust conditions, so using the corresponding library theorem is also a valid
proof; the assignment does not enforce a particular proof method.

```sh
cargo run -q -p cetacea_cli -- --assignment docs/book/hol-code/ch21-solutions.ctea-assignment docs/book/hol-code/ch21-exercises.ctea
```

For the browser, open the exercise file and load `ch21.ctea-task` as the
assignment. The example selector includes the token and state-machine
examples. Save or export current work before replacing it with an example.

The mistakes file omits an initial-value premise, counts one extra tick, and
tries to infer a universal formula from a short prefix. The concrete
values in the examples certify; the attempted universal claim in the mistakes
file must fail.
The assignment rejects unfinished proofs, new axioms, and classical reasoning,
and checks all four required theorem signatures.
