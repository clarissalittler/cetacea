# Cetacea

Cetacea is a small tactic-based theorem prover following the design in
`MiniTactic_Theorem_Prover_Design.pdf`.

The current implementation is the first vertical slice: propositional logic with
a trusted kernel, an untrusted tactic layer, and constructive/classical mode
tracking.

## Layout

- `crates/cetacea_core`: parser, propositional AST, tactics, proof objects, and
  kernel checker.
- `crates/cetacea_cli`: command-line checker.
- `examples/prop.ctea`: constructive and classical propositional examples.

## Run

```sh
cargo test
cargo run -p cetacea_cli -- examples/prop.ctea
```

The CLI prints each accepted theorem and the strongest mode used by its checked
proof object.

## Implemented

- `mode constructive` and `mode classical`
- theorem declarations with proposition parameters
- formulas: `True`, `False`, atoms, `not`, `/\`, `\/`, `->`, `<->`
- proof objects for natural-deduction rules over implication, conjunction,
  disjunction, truth, falsehood, theorem references, and classical rules
- tactics: `intro`, `exact`, `assumption`, `apply`, `split`, `left`, `right`,
  `cases`, `exfalso`, `contradiction`, `by_cases`, `by_contra`
- kernel reporting of constructive versus classical proof use

## Next Milestones

1. Improve diagnostics with source spans and proof-state rendering.
2. Add first-order terms, types, predicates, `forall`, and `exists`.
3. Add equality, `refl`, substitution, and rewriting.
4. Add typed sets and the set simplification layer.
5. Add natural numbers and induction.

