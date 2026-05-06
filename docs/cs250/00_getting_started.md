# Getting Started

## What is Cetacea?

A *proof assistant*: you state a theorem and write a list of tactics
that build a proof. The checker reads your tactics, builds a formal
proof object, and confirms (or rejects) that the proof object actually
proves what you claimed.

Cetacea is much smaller than systems like Lean or Coq. That's a feature:
the entire surface — every tactic, every connective — fits into one
short reference document (`docs/USAGE.md`). For a course like CS 250,
where the point is to get a feel for natural deduction and not to ship a
research paper, that's the right size.

## Running

From the repo root:

```sh
cargo build
cargo run -p cetacea_cli -- docs/cs250/code/01_propositional.ctea
```

You should see lines like:

```
accepted theorem and_comm (constructive)
accepted theorem imp_trans (constructive)
...
```

If a proof fails, you get a single error line with the file, line
number, theorem name, and the immediate cause. In the browser UI, the
same checker also shows current goals, tactic hints, and repair
suggestions.

## A minimal `.ctea` file

```text
mode constructive

theorem and_comm (P Q : Prop) : P /\ Q -> Q /\ P := by
  intro h
  split
  exact h.right
  exact h.left
```

Three things to notice:

1. **`mode constructive`** at the top. Cetacea can also run in
   `mode classical`, which enables `by_cases` and `by_contra`. Most
   propositional and first-order proofs you'll write for CS 250 are
   constructive.
2. **Theorem statement** has parameters in parens, then `:`, then the
   formula, then `:= by`.
3. **Tactic script** under `by`. One tactic per line. Indentation
   doesn't have to be exact, but be consistent.

## Imports

To use the standard library:

```text
import ../std/prelude.ctea
```

The prelude pulls in `prop.ctea`, `fol.ctea`, `eq.ctea`, `nat.ctea`,
and `set.ctea`. Then you can write `exact imp_trans`, `apply add_comm`,
etc.

Imports are resolved relative to the file you're in. Most of the
runnable examples in `code/` import the prelude:

```text
import ../../../std/prelude.ctea
```

## The connective table

This is the entire propositional-and-FOL surface you'll need:

| Course notation | Cetacea | Built from |
|---|---|---|
| `T`, true | `True` | (built-in, but see below) |
| `F`, false | `False` | (built-in) |
| `P ∧ Q` | `P /\ Q` | (built-in) |
| `P ∨ Q` | `P \/ Q` | (built-in) |
| `¬P` | `not P` | sugar for `P -> False` |
| `P → Q` | `P -> Q` | (built-in) |
| `P ↔ Q` | `P <-> Q` | sugar for `(P -> Q) /\ (Q -> P)` |
| `∀x ∈ A. P(x)` | `forall x : A, P(x)` | (built-in) |
| `∃x ∈ A. P(x)` | `exists x : A, P(x)` | (built-in) |
| `x = y` | `x = y` | (built-in) |
| `x ∈ A` | `x in A` | (built-in, sets) |
| `A ⊆ B` | `A subset B` | (built-in, sets) |

Use `trivial` or `exact True` to prove a plain `True` goal.

## What if my proof doesn't go through?

You'll see something like:

```
error: <file>:7: theorem `t` failed: exact expression does not solve the goal:
  proof has type `Q`, but expected `P`
  note: target: P -> Q -> P
```

A few things to know:

- The `target:` line on the bottom is the current open subgoal at the
  failing tactic.
- The error points at the failing tactic line when Cetacea can identify
  it, including inside `cases` and `induction` blocks.
- "exact expression does not solve the goal" plus `expected: X` means
  the *open subgoal at that step* was `X`.

When you're stuck in the browser UI, put the cursor on a tactic line and
look at the Goals panel. In the CLI, you can temporarily insert
`show_goal` to make the checker report the current goal at that point.

## How to read the rest of these tutorials

Every tutorial has a runnable companion under `code/`. Try checking it
*before* you read the prose, so you've seen what a working file looks
like; then come back and read.
