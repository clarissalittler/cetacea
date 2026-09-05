# Chapter 22 — Finite Probability by Counting

Companion files: [examples](hol-code/ch22-examples.ctea),
[exercises](hol-code/ch22-exercises.ctea),
[solutions](hol-code/ch22-solutions.ctea),
[mistakes](hol-code/ch22-mistakes.ctea),
[assignment policy](hol-code/ch22-solutions.ctea-assignment), and
[browser assignment](hol-code/ch22.ctea-task).

Choose uniformly from the four ordered outcomes of two coin tosses:
`hh`, `ht`, `th`, and `tt`. Exactly two begin with a head. Their probability is
therefore 2/4. The arithmetic is small; the useful work is specifying what we
count, which outcomes are equally likely, and why the count is correct.

This chapter uses the list sums from Chapter 17. Its proofs are constructive,
with the `hol` profile because generic `map` takes functions as arguments.
Cetacea checks natural-number counts and their identities. It does not yet
provide rational-number division or a probability-measure type. Fractions in
this chapter are the mathematical interpretation of those checked counts for
a nonempty, uniformly sampled list.

## 22.1 State the experiment before counting

The example defines a four-constructor `Outcome` type and lists each constructor
once. Choosing uniformly from that list models two fair independent coin tosses.
The code specifies this finite model; it does not prove that a physical coin
is fair or that two physical tosses are independent.

| Outcome | First head | Second head | Total heads |
| --- | ---: | ---: | ---: |
| `hh` | 1 | 1 | 2 |
| `ht` | 1 | 0 | 1 |
| `th` | 0 | 1 | 1 |
| `tt` | 0 | 0 | 0 |
| Sum | 2 | 2 | 4 |

The recursive functions `first_head` and `second_head` are event indicators:
each returns one when its event occurs and zero otherwise. For example,
`S.sum(C.map(first_head, outcomes)) = 2` is a checked event count.
`C.length(outcomes) = 4` is the checked sample size. Together these give the
probability 2/4 in the uniform model.

Lists count occurrences. The second example adds another `hh` ticket to the
front. There are now five tickets, three of which begin with a head. Uniform
sampling of tickets gives probability 3/5, even though there are still only
four distinct outcome values. An accidental duplicate changes the model.

## 22.2 Why the denominator cannot be zero

An empty list has a perfectly good sum, zero. It does not describe a uniform
choice of a ticket, because there is no ticket to choose. The expression 0/0
is not a probability.

`P.nonempty_denominator` proves that a cons list has nonzero length. Its proof
rewrites length to a successor and rules out equality with zero. Exercise 1
asks you to reconstruct this argument. The numerator identities below also
hold for empty lists, but their probability interpretation requires a nonempty
sample space separately.

## 22.3 Complementary events account for every ticket

For each outcome, `first_head(outcome) + first_tail(outcome) = 1`. This says
that precisely one of these two indicators contributes. Summing gives:

```text
first-head count + first-tail count = sample size
```

Dividing by the common nonzero sample size yields the familiar complement
identity, P(E) + P(not E) = 1. The checked theorem is the integer identity
`P.complement_counts`.

Its premise is required only on the listed outcomes:

```cetacea
forall x : A, C.Member(x, xs) -> add(f(x), g(x)) = 1
```

The two indicators cannot overlap or leave a listed outcome uncovered. There
is no condition on values that never occur in the list. Exercise 2 proves this
law by list induction: the empty case has two zero sums, while the cons case
adds one for the head and uses the induction hypothesis for the tail.

A function with natural-number outputs is not automatically an event
indicator. The `heads` function returns two at `hh`; it describes a payoff,
not a yes/no event. To use arbitrary functions as complementary indicators,
you must prove the displayed pointwise equation.

## 22.4 Expected values share the same denominator

For a natural-number payoff `f`, the expected value in this uniform model is
its total over the tickets divided by the number of tickets. The checked
`total_heads` theorem gives numerator four; the checked sample size is four.
The expected number of heads is thus 4/4 = 1.

Linearity follows by summing the pointwise equation `h(x) = f(x) + g(x)`:

```text
sum(h) = sum(f) + sum(g)
```

`P.numerator_add` checks this equality. All three expected values use the same
sample list and hence the same nonzero denominator. No independence premise
is needed. For example, adding the first-head indicator to itself still obeys
the same sum law, although those two copies are completely dependent.

The library covers natural-number payoffs. Negative or rational payoffs,
nonuniform probability weights, conditional probability and independence
proofs need further representations and laws; they are not supplied by this
chapter.

## 22.5 Exercises and grading

| Exercise | Task | Suggested approach |
| --- | --- | --- |
| `ex22_1` | Prove a nonempty list has nonzero length. | Rewrite length; a successor cannot equal zero. |
| `ex22_2` | Prove complementary counts sum to list length. | Induct on the list and regroup the two head contributions. |
| `ex22_3` | Combine known payoff totals `a` and `b`. | Use numerator linearity, then rewrite the two totals. |
| `ex22_4` | Compute the numerator of a constant payoff. | Use the checked constant-contribution sum law. |

Replace all four `sorry` placeholders, keeping names and statements. The policy
checks exact theorem signatures and rejects unfinished proofs, new axioms,
classical reasoning, extensionality and choice. Library proofs of the required
statements are permitted; the policy does not enforce an induction method.

```sh
cargo run -q -p cetacea_cli -- --assignment docs/book/hol-code/ch22-solutions.ctea-assignment docs/book/hol-code/ch22-exercises.ctea
```

In the browser, open the exercise file and load `ch22.ctea-task` as the
assignment. The example selector includes the coin-and-ticket example. Export
current work before replacing it with an example.

The mistakes file tries to use an empty denominator, drops the complementary
indicator premise, and confuses a constant payoff with its total. Each attempt
must be rejected. As an additional paper exercise, explain why the repeated
`hh` ticket changes the probability to 3/5 and why dividing by four would no
longer describe uniform sampling of those tickets.
