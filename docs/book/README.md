# Proofs, Checked

**A First Course in Logic with the Cetacea Proof Assistant**

This is a textbook about logic and proof, written for students meeting
formal proof for the first time — roughly the audience of a
community-college discrete math course such as CS 250. It assumes no
prior experience with proofs, proof assistants, or advanced math.

What makes it different from other logic books: **every proof in it is
checked by a program.** The Cetacea proof assistant, which lives in this
repository, reads your proofs line by line and either accepts them or
tells you exactly where they go wrong. You never have to wonder whether
your proof is *really* right. You will still learn to read and write
proofs on paper — but here, paper proofs get a safety net.

The math leads and the tool follows. Cetacea shows up in every section,
but always in service of a logical idea, never the other way around. If
you want a pure reference manual for the language, that is
[`docs/USAGE.md`](../USAGE.md); if you want terse course-aligned
translations of CS 250 modules, see [`docs/cs250/`](../cs250/README.md).
This book is the slow, friendly path.

## What you need

Build the checker once, from the repository root:

```sh
cargo build
```

Then check any file like this (also from the repository root):

```sh
target/debug/cetacea_cli docs/book/code/ch01-examples.ctea
```

or equivalently `cargo run -p cetacea_cli -- <file>`. There is also an
interactive terminal UI (`cargo run -p cetacea_cli -- --tui <file>`)
that shows the proof state as you move your cursor through a proof —
worth trying once you are comfortable with the basics.

## How to use this book

Each chapter comes with three (sometimes four) companion files. Chapters 1–12
live in the frozen first-order corpus under [`code/`](code/). The experimental
finite-mathematics extension lives under [`hol-code/`](hol-code/) so its new
HOL surface can evolve without weakening that regression oracle.

| File | What it is |
|---|---|
| `chNN-examples.ctea` | Every worked proof from the chapter, runnable. It checks clean. |
| `chNN-exercises.ctea` | The chapter's exercises with `sorry` placeholder proofs. It checks as-is, but every theorem is reported as an `incomplete theorem`. Your job is to complete them. |
| `chNN-solutions.ctea` | Full solutions. Genuinely try the exercises first. |
| `chNN-mistakes.ctea` / `ch02-fallacies.ctea` | **Intended to fail.** Deliberately wrong proofs whose error messages the chapter dissects. Run them; read the errors. |
| `chNN-solutions.ctea-assignment` | For HOL-extension chapters, the policy fixing the fragment, imports, trust, and required signatures. |

From the repository root, `./scripts/check_all.sh` verifies the companion files,
requires each deliberately wrong theorem to fail independently, and checks the
book's quoted error headlines and acceptance receipts against current output.
For Chapters 13–15 it also runs the solution manifests and confirms that the
intentionally first-order Chapter 14 and Chapter 15 policies reject the mapped
theorems and their transitive clients.

The rhythm for each chapter:

1. Read the chapter with the examples file open next to it.
2. Run the examples file and watch every theorem get accepted.
3. Run the mistakes file and read what rejection looks like.
4. Open the exercises file and replace each `sorry` with a proof,
   re-running the checker as you go. The `incomplete theorem` markers
   are your to-do list; the chapter is done when they are all gone.

A small notational convention used throughout: when we narrate the
middle of a proof, we write the *goal state* as `hypotheses |- target`.
So `h : P /\ Q |- Q /\ P` reads "you have a hypothesis `h` proving
`P /\ Q`, and you must prove `Q /\ P`."

## Chapters

The twelve-chapter first-order course and three experimental finite-mathematics
chapters are drafted; [`OUTLINE.md`](OUTLINE.md) has a one-paragraph synopsis
of each.

| # | Chapter |
|---|---|
| 1 | [Propositions and How to State Them](01-propositions.md) |
| 2 | [Natural Deduction: Proof as a Game with Rules](02-natural-deduction.md) |
| 3 | [The Classical Moves: Excluded Middle and Friends](03-classical.md) |
| 4 | [Everyone, Someone, No One: Quantifiers](04-quantifiers.md) |
| 5 | [Equality: The Most Important Relation](05-equality.md) |
| 6 | [Sets: Collections You Can Reason About](06-sets.md) |
| 7 | [Relations: Structure Between Things](07-relations.md) |
| 8 | [Functions: Relations with Rules](08-functions.md) |
| 9 | [Induction: Climbing the Number Line](09-induction.md) |
| 10 | [Recursion and Data: Building Your Own Worlds](10-recursion-data.md) |
| 11 | [Structural Induction: Proofs That Follow the Data](11-structural-induction.md) |
| 12 | [Strong Induction, and Where to Go Next](12-strong-induction.md) |
| 13 | [Finite Types and Honest Counting](13-finite-types.md) |
| 14 | [Bijections and the HOL Boundary](14-bijections.md) |
| 15 | [Pigeonhole, One Element at a Time](15-pigeonhole.md) |

Chapters 13–15 require the `hol` branch. Their assignment manifests distinguish
concrete `fol+induction` work from the genuinely higher-order act of passing a
function to generic `map`.

## A word of encouragement

Formal proof has a reputation for being hard, and the first week can
feel like learning to write with your other hand. Two things to hold on
to. First, the checker's error messages are *for you* — Chapter 1
onward, this book teaches you to read them the way a musician reads
feedback from a tuner. Second, every proof in this book was rejected by
the checker at least once while being written. Rejection is the normal
state of a proof in progress. The only proof that never fails is the
one you never run.
