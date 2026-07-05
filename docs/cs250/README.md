# CS 250 in Cetacea

Tutorials that show how to do parts of the CS 250 course in Cetacea, the
small tactic-based prover at the root of this repo.

## Audience

These tutorials assume you have read (or are reading) the corresponding
CS 250 module and want to see the same material formally. They do not
re-teach the math; they translate it into Cetacea.

## What's here

| File | CS 250 module | Topic |
|---|---|---|
| `00_getting_started.md` | — | Installing, running, and the shape of a `.ctea` file |
| `01_propositional.md` | Module 2 | Propositional formulas, equivalences, de Morgan |
| `02_proof_systems.md` | Module 3 | Introduction/elimination rules as tactics |
| `03_first_order.md` | Module 4 | Quantifiers, predicates, equality |
| `04_induction_nat.md` | Module 4 (end) | Natural-number induction |
| `05_sets.md` | Module 1 / intermezzo | Sets and set extensionality |
| `06_relations.md` | Module 1 | Reflexive / symmetric / transitive relations |
| `07_structural_induction.md` | Modules 8–10 | Data types, recursion over them, structural and strong induction |
| `08_functions.md` | Functions module | Functions as graphs: total, single-valued, injective, surjective, composition |
| `09_modular.md` | Module 6 | Divisibility, congruence mod m as an equivalence, modular arithmetic |
| `LIMITATIONS.md` | — | What CS 250 topics Cetacea **can't** currently do, and rough edges I hit while writing these |

Each tutorial has a sibling runnable file in `code/`. Check it the same
way you'd check any Cetacea file:

```sh
cargo run -p cetacea_cli -- docs/cs250/code/01_propositional.ctea
```

## Recommended reading order

1. `00_getting_started.md` once.
2. Read `01` and `02` together — propositional logic and natural
   deduction. The truth-table side of Module 2 isn't in Cetacea (Cetacea
   is a proof system, not a model checker), but everything you'd prove
   *via* a truth table can be re-derived as a proof in `02`.
3. Then `03` and `04` to see quantifiers and induction.
4. `05` and `06` are about the parts of Module 1 that Cetacea supports.
5. `07` continues induction into lists, trees, and strong induction —
   read it after `04`, alongside Modules 8–10.
6. `08` builds on `03` and `06`: functions are just special relations,
   and the file makes that literal.
7. `09` does Module 6 with the equivalence-relation ideas from `06` and
   the arithmetic from `04` — it closes the modular-congruence gap that
   `06` had to axiomatize around.

## What you'll get out of this

The course's goal in Modules 2–4 is to make formal proofs feel like
something you can do, not just read. A proof assistant is the most
honest version of that experience: every inference is checked, the rules
are explicit, and the file is pass/fail. Cetacea is small enough that
the rules don't hide.

If you're stuck on a textbook exercise, doing the same exercise in
Cetacea sometimes makes it click — the tactics force you to identify
which rule you're using at each step.
