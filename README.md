# Cetacea

Cetacea is a small tactic-based theorem prover following the design in
`MiniTactic_Theorem_Prover_Design.pdf`.

The current implementation covers propositional logic plus an initial
first-order layer with typed variables, predicate applications, universal
quantification, and existential quantification. First-order declarations and
formula annotations are checked for known types, known predicates, predicate
arity, function arity, and argument type compatibility.

## Layout

- `crates/cetacea_core`: parser, AST, tactics, proof objects, and kernel
  checker.
- `crates/cetacea_cli`: command-line checker.
- `examples/prop.ctea`: constructive and classical propositional examples.
- `examples/fol.ctea`: first-order examples.

## Run

```sh
cargo test
cargo run -p cetacea_cli -- examples/prop.ctea
cargo run -p cetacea_cli -- examples/fol.ctea
```

The CLI prints each accepted theorem and the strongest mode used by its checked
proof object.

## Implemented

- `mode constructive` and `mode classical`
- `sort`, `const`, `func`, and `pred` declarations
- theorem declarations with proposition, predicate, type, and term parameters
- formulas: `True`, `False`, atoms, equality, `not`, `/\`, `\/`, `->`, `<->`
- first-order formulas: `forall x : T, P(x)` and `exists x : T, P(x)`
- validation for type names, predicate names, predicate arity, and predicate
  argument types
- validation for function names, function arity, and function argument types
- goal-directed schema instantiation for bare theorem references in `exact` and
  `apply`
- explicit theorem-instantiation syntax:
  `exact theorem_name {A := Person; P := Happy; x := alice}`
- proof objects for natural-deduction rules over implication, conjunction,
  disjunction, truth, falsehood, universal quantification, existential
  quantification, equality reflexivity, equality substitution, theorem
  references, and classical rules
- tactics: `intro`, `exact`, `assumption`, `apply`, `split`, `left`, `right`,
  `cases`, `exists`, `refl`, `rewrite`, `exfalso`, `contradiction`, `by_cases`,
  `by_contra`
- kernel reporting of constructive versus classical proof use

## Next Milestones

1. Improve diagnostics with source spans and proof-state rendering.
2. Improve theorem-instantiation diagnostics and broaden inference.
3. Add typed sets and the set simplification layer.
4. Add natural numbers and induction.
