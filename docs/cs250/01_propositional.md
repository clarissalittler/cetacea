# Propositional Logic (CS 250 Module 2)

## What you can and can't do here

CS 250 Module 2 has two halves:

1. **Truth tables.** Compute the truth table of a formula, classify it
   as tautology / contradiction / contingent, check logical
   equivalence by comparing tables.
2. **Tautologies as reasoning patterns.** Modus ponens, De Morgan's
   laws, double negation, etc.

Cetacea **does not compute truth tables**. It is a proof system, not a
model checker. So the *first* half of Module 2 is out of scope.

But everything you'd verify *via* a truth table — every tautology — can
be re-proved as a theorem in Cetacea using natural-deduction tactics.
That's where the bridge with Module 3 starts. This tutorial is the
warm-up for that bridge.

## Constructive vs. classical, briefly

CS 250 uses *classical* propositional logic, where excluded middle
($p ∨ ¬p$) and double-negation elimination ($¬¬p ⊢ p$) are valid. The
tutorial here will mostly stay constructive (where everything is built
from the introduction/elimination rules of Module 3 alone) and switch
to `mode classical` only for the proofs that genuinely need it. The
distinction is one of the things you can *see* in Cetacea that's hard
to see on paper.

The same proof script ends up labeled `(constructive)` or `(classical)`
when the file is checked, depending on which rules it actually used.

## The connectives, with one example each

The companion file is [`code/01_propositional.ctea`](code/01_propositional.ctea).

### Conjunction

```text
theorem and_intro_demo (P Q : Prop) : P -> Q -> P /\ Q := by
  intro hp
  intro hq
  split
  exact hp
  exact hq

theorem and_elim_left_demo (P Q : Prop) : P /\ Q -> P := by
  intro h
  exact h.left
```

`split` is `∧`-introduction. `h.left` and `h.right` are `∧`-eliminations.

### Disjunction

```text
theorem or_intro_left_demo (P Q : Prop) : P -> P \/ Q := by
  intro hp
  left
  exact hp

theorem or_elim_demo (P Q R : Prop) : (P -> R) -> (Q -> R) -> P \/ Q -> R := by
  intro hpr
  intro hqr
  intro hpq
  cases hpq with
  | left hp =>
      apply hpr
      exact hp
  | right hq =>
      apply hqr
      exact hq
```

`left` and `right` are the two `∨`-introductions. `cases ... with`
is `∨`-elimination — proof by cases.

### Implication

```text
theorem imp_intro_demo (P Q : Prop) : P -> P -> Q -> P := by
  intro hp1
  intro hp2
  intro hq
  exact hp1
```

`intro` opens the implication. (For the elimination side, use `apply`
or function-application notation `h x`. We'll see that on the next
page.)

### Negation

`not P` is sugar for `P -> False`, so the rules for `¬` are just the
rules for `→` ending in `False`.

```text
theorem modus_tollens (P Q : Prop) : (P -> Q) -> not Q -> not P := by
  intro hpq
  intro hnq
  intro hp
  apply hnq
  apply hpq
  exact hp
```

This is exactly modus tollens: from `P → Q` and `¬Q`, conclude `¬P`.

### De Morgan's laws

The "easy" direction works constructively:

```text
theorem demorgan_easy (P Q : Prop) : not P \/ not Q -> not (P /\ Q) := by
  intro h
  intro hpq
  cases h with
  | left hnp =>
      apply hnp
      exact hpq.left
  | right hnq =>
      apply hnq
      exact hpq.right
```

The hard direction — `¬(P ∧ Q) → ¬P ∨ ¬Q` — is **not** constructively
provable. This is one of those places where the choice of logic
genuinely shows up. To prove it you have to switch:

```text
mode classical

theorem demorgan_hard (P Q : Prop) : not (P /\ Q) -> not P \/ not Q := by
  intro h
  by_contra hn
  apply h
  split
  by_contra hnp
  apply hn
  left
  exact hnp
  by_contra hnq
  apply hn
  right
  exact hnq
```

When the file is checked, this theorem is labeled `(classical)`.

### Excluded middle

`em` and `dne` are in `std/prop.ctea`. If you import the prelude you
can just use them.

```text
mode classical

theorem em_demo (P : Prop) : P \/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h
```

## Bridge to Module 3

Every line of a Cetacea propositional proof is one *introduction* or
*elimination* rule:

| CS 250 rule | Cetacea tactic | What it does |
|---|---|---|
| ∧-intro | `split` | Splits a goal `P /\ Q` into two goals |
| ∧-elim (left/right) | `h.left`, `h.right` | Pulls one conjunct out |
| ∨-intro (left/right) | `left`, `right` | Picks which side of a goal `P \/ Q` you'll prove |
| ∨-elim (proof by cases) | `cases h with` | Splits a hypothesis `P \/ Q` into two cases |
| →-intro | `intro h` | Assumes the antecedent, leaves the consequent as the new goal |
| →-elim (modus ponens) | `apply h` or `exact h x` | Uses an implication |
| ⊥-elim (anything from false) | `contradiction` or `exfalso` | If you have `False`, anything follows |
| ¬-intro | `intro hp` (and derive `False`) | Proves `not P` by deriving `False` from `P` |
| ¬-elim (DNE, classical) | `by_contra h` | Assumes `not P` and tries to derive `False` |
| Excluded middle (classical) | `by_cases h : P` | Considers `P` and `not P` as two subgoals |

Once you internalize this table, Module 3 stops being a pile of new
notation and just becomes "the names for the things Cetacea was making
you do anyway."

## Try it

Open [`code/01_propositional.ctea`](code/01_propositional.ctea) and run
it:

```sh
cargo run -p cetacea_cli -- docs/cs250/code/01_propositional.ctea
```

Then try the textbook exercises:

- Module 2 Exercise 6 (express XOR in terms of `/\`, `\/`, `not`):
  state and prove a theorem that says
  `xor(p, q) <-> (p /\ not q) \/ (not p /\ q)` — define `xor` as one
  side of the biconditional.
- Module 2 Exercise 7 (the equivalence `p -> (q /\ r) ↔ (p -> q) /\ (p -> r)`):
  prove the forward and backward implications. Both are constructive.
- Module 2 Exercise 11 (`φ` is a tautology iff `not φ` is a contradiction):
  this becomes a *theorem schema* in Cetacea over a Prop variable. Try
  it in classical mode. Note the asymmetry — one direction is
  constructive, the other isn't.

The textbook problems that ask you to *compute* truth tables (e.g. M2
Exercises 1, 2, 4, 5) are best done on paper or with the Python
companion file `code/module02_logic.py` from the course repo. Cetacea
is the right tool for the *equivalence* and *valid-argument* problems,
not the truth-table problems.
