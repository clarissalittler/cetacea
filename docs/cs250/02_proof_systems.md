# Proof Systems for Propositional Logic (CS 250 Module 3)

This is the module where Cetacea earns its keep. Module 3 introduces a
*proof system* — introduction and elimination rules for each connective
— and asks you to chain those rules into formal derivations. Cetacea is
literally that proof system, with one tactic per rule.

## Rule-to-tactic dictionary

| Rule (CS 250 Module 3) | Cetacea tactic | Where the goal goes |
|---|---|---|
| Modus ponens (→-elim) | `apply h` (or `exact h x` for a forall) | discharges the goal, leaves the antecedent as a subgoal |
| Implication intro (→-I) | `intro h` | the assumption is named `h`; the new goal is the consequent |
| Conjunction intro (∧-I) | `split` | two new subgoals, one per conjunct |
| Conjunction elim (∧-E) | `h.left`, `h.right` (in a proof expression) | use one half of `h` |
| Disjunction intro (∨-I) | `left` or `right` | commit to one disjunct |
| Disjunction elim (∨-E, proof by cases) | `cases h with` | two subgoals, one per case |
| Bottom elim (⊥-E) | `contradiction` or `exfalso` | from `False` to anything |
| Top intro (⊤-I) | `trivial` or `exact True` | closes a `True` goal |
| Excluded middle | `by_cases h : P` (classical) | two subgoals: with `h : P` and with `h : not P` |
| Double-negation elim | `by_contra h` (classical) | turns target `P` into target `False` with hypothesis `h : not P` |

## Modus ponens, three ways

The companion file is [`code/02_proof_systems.ctea`](code/02_proof_systems.ctea).

The textbook's modus ponens is "from $p$ and $p \to q$, conclude $q$."
Cetacea has three reasonable ways to use it.

```text
-- (1) `exact` with the forward expression. We can't write `hpq hp` for
--     a non-forall implication, so this isn't directly available; see
--     the next two.

-- (2) `apply` the implication, then discharge its premise:
theorem mp_apply (P Q : Prop) : P -> (P -> Q) -> Q := by
  intro hp
  intro hpq
  apply hpq
  exact hp

-- (3) For deeper chains you can keep nesting:
theorem hypothetical_syllogism (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R := by
  intro hpq
  intro hqr
  intro hp
  apply hqr
  apply hpq
  exact hp
```

That last theorem is the *transitive property of implication*, also
known as *hypothetical syllogism*. The proof tree from CS 250 §3.5 maps
directly onto these four lines.

## Disjunctive syllogism

From the textbook:

> Premises: $p \vee q$, $\lnot q$. Conclusion: $p$.

In Cetacea:

```text
theorem disjunctive_syllogism_left (P Q : Prop) : P \/ Q -> not Q -> P := by
  intro hpq
  intro hnq
  cases hpq with
  | left hp =>
      exact hp
  | right hq =>
      exfalso
      apply hnq
      exact hq
```

Reading the proof: split into the two disjuncts; in the left case, we
already have what we want; in the right case, we have $q$ and $\lnot
q$, so we use ⊥-elimination (here `exfalso` followed by `apply hnq`
applied to `hq`) to discharge any goal — including $p$.

## Proof by contradiction (classical)

The textbook *derives* proof by contradiction from modus tollens and
double-negation elimination. In Cetacea you don't need to derive it;
`by_contra` does the right thing in one step.

```text
mode classical

theorem dne_via_contra (P : Prop) : not not P -> P := by
  intro hnn
  by_contra hn
  apply hnn
  exact hn
```

This is one of the rare places where the script in classical mode is
genuinely shorter than the constructive version (because the
constructive version doesn't exist at all — `not not P -> P` is the
canonical thing constructive logic refuses to prove).

## A worked Module 3 example: ¬p ∨ q from p → q

Module 3 §3.6 has this proof in semi-formal style:

> Theorem. Assuming $p \to q$, show $\lnot p \vee q$.

This needs excluded middle, so it's classical. In Cetacea:

```text
mode classical

theorem imp_to_or_classical (P Q : Prop) : (P -> Q) -> not P \/ Q := by
  intro hpq
  by_cases h : P
  -- case 1: P is true.
  right
  apply hpq
  exact h
  -- case 2: P is false.
  left
  exact h
```

Compare to the textbook proof: the cases on `P ∨ ¬P` map exactly to
`by_cases h : P`. In the `P` case we use modus ponens (here `apply`).
In the `¬P` case we just `left`-introduce `¬P` from the hypothesis. The
chain of `→`-introduction and `∨`-elimination in the book becomes one
short script.

## Two famous fallacies as failed proofs

Module 3 names the two classic invalid argument forms:

- **Converse error:** from `P -> Q` and `Q`, conclude `P`. **Invalid.**
- **Inverse error:** from `P -> Q` and `not P`, conclude `not Q`. **Invalid.**

If you try to prove either, Cetacea rejects you. You can verify this by
checking [`code/02_fallacies_negative.ctea`](code/02_fallacies_negative.ctea),
which is *intended to fail*. The error message tells you which step
couldn't go through.

This is one of the things a proof assistant is genuinely good for: the
fallacies feel plausible until you try to write them down. When you
can't, you've internalized why they're wrong.

## Try it

- Module 3 Exercise 8: from premises `p -> q` and `p -> r`, derive
  `p -> (q /\ r)`. Constructive. (See `mp_to_and` in the companion
  file.)
- Module 3 Exercise 9: from `p \/ q`, `not p`, and `q -> r`, derive
  `r`. Constructive.
- Module 3 Exercise 11(a): from excluded middle, derive double-negation
  elimination. (Both happen to already be in `std/prop.ctea` — try it
  yourself first and then compare.)
- Disjunctive syllogism in both directions (versions for `not p` and
  `not q` premise).

A useful exercise: take your **three favorite tautologies** from
Module 2 Exercise 4 and prove each of them as a Cetacea theorem, in
constructive mode where possible. The ones that need classical reasoning
will tell you something interesting about themselves.
