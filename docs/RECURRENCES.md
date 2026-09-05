# Checked recurrence proofs

`builtin:std/hol/recurrences.ctea` supplies constructive proofs for sequences
indexed by natural numbers. The three laws and their chapter assignment certify in `fol+induction`. They introduce no new axioms or incomplete proofs.

## Uniqueness

`recurrence_unique` accepts an arbitrary state type `A`, two functions
`f g : Nat -> A`, and an update function `step : Nat -> A -> A`.
It requires:

- The same initial value: `f(0) = g(0)`.
- The recurrence equation for `f` at every index.
- The same recurrence equation for `g` at every index.

It concludes `forall n : Nat, f(n) = g(n)`. The proof is induction on the
index. The successor step rewrites both update equations and substitutes the
induction hypothesis into `step`.

This proves uniqueness for functions satisfying the premises. It does not
construct a sequence or prove existence for an arbitrary update function.
A concrete `defrec` definition provides a sequence in the worked example.

## Constant-step closed form

`constant_step_closed` proves that the equations

```text
f(0) = a
forall n : Nat, f(succ(n)) = add(d, f(n))
```

imply `forall n : Nat, f(n) = add(a, mul(n, d))`.
`constant_step_successor` separately checks the update equation for that
closed form. These laws cover natural-number initial values and increments;
negative increments and real-valued recurrences are outside this interface.

## Worked clients

The [recurrence example](hol/examples/recurrences.ctea) checks a machine that
starts with two tokens and gains three per tick. It proves the closed form,
computes fourteen tokens after four ticks, and compares the recursive sequence
with a separately named formula using uniqueness. A second client applies
uniqueness to a machine alternating between `ready` and `busy`, showing that
the generic result is not restricted to number-valued states.

These theorems conclude a universal statement after their premises. To prove
one particular index, first prove a `have all_ticks : forall k : Nat, ...`,
then use `exact all_ticks n`. The examples show this pattern explicitly.

Named monomorphic `def` functions can now be supplied as function arguments,
as can `func` and `defrec` symbols. For example, `g := formula` and
`step := advance` use the definitions' checked signatures. Arity, domain, and
result types are still constraints; names alone do not establish compatibility.
This does not add anonymous function-valued lambdas, partial application, or
implicit instantiation of polymorphic function definitions.

Core tests check the generic laws and concrete clients and reject an incorrect
initial value, an incorrect increment, and incompatible named-function
signatures. Wasm and native/browser grading cases cover the worked example
and rejection of a changed update rule. [Chapter 21](book/21-recurrences.md) supplies exercises, solutions,
deliberate mistakes, and a native/browser assignment policy. More general
recurrence solving is not claimed by these three laws.
