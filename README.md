# Cetacea

Cetacea is a small tactic-based theorem prover following the design in
`MiniTactic_Theorem_Prover_Design.pdf`.

The current implementation covers propositional logic, a first-order layer with
typed variables, predicate applications, universal and existential
quantification, equality, transparent formula definitions, typed sets, and a
small natural-number layer with induction. Declarations and formula annotations
are checked for known types, known predicates, predicate arity, function arity,
definition arity, set element compatibility, and argument type compatibility.

## Layout

- `crates/cetacea_core`: parser, AST, tactics, proof objects, and kernel
  checker.
- `crates/cetacea_cli`: command-line checker.
- `std`: checked theorem-library files.
- `examples/prop.ctea`: constructive and classical propositional examples.
- `examples/fol.ctea`: first-order examples.
- `examples/set_nat.ctea`: typed set and natural-number simplification examples.

## Run

```sh
cargo test
cargo run -p cetacea_cli -- examples/prop.ctea
cargo run -p cetacea_cli -- examples/fol.ctea
cargo run -p cetacea_cli -- examples/set_nat.ctea
cargo run -p cetacea_cli -- std/set.ctea
cargo run -p cetacea_cli -- std/nat.ctea
```

The CLI prints each accepted theorem or axiom and the strongest mode used by
its checked proof object.

## Implemented

- `mode constructive` and `mode classical`
- `sort`, `const`, `func`, `pred`, formula `def`, and `axiom` declarations
  with type and term parameters
- theorem declarations with proposition, predicate, type, and term parameters
- built-in `Nat`, `Set T`, `0`, `succ(n)`, and `add(n, m)`
- typed set terms: `empty(T)`, `singleton(x)`, `union(A, B)`, `inter(A, B)`,
  and `diff(A, B)`
- formulas: `True`, `False`, atoms, equality, membership, subset, `not`, `/\`,
  `\/`, `->`, `<->`
- first-order formulas: `forall x : T, P(x)` and `exists x : T, P(x)`
- validation for type names, predicate names, predicate arity, and predicate
  argument types
- validation for function names, function arity, and function argument types
- validation for transparent formula definitions, including definition arity and
  inferred type parameters
- validation for typed set membership and subset compatibility
- axiom declarations for trusted principles such as set extensionality
- checked library files for propositional logic, first-order logic, equality,
  sets, and natural numbers
- goal-directed schema instantiation for bare theorem references in `exact` and
  `apply`
- explicit theorem-instantiation syntax:
  `exact theorem_name {A := Person; P := Happy; x := alice}`
- proof objects for natural-deduction rules over implication, conjunction,
  disjunction, truth, falsehood, universal quantification, existential
  quantification, equality reflexivity, equality substitution, natural-number
  induction, theorem references, and classical rules
- tactics: `intro`, `exact`, `assumption`, `apply`, `split`, `left`, `right`,
  `cases`, `exists`, `refl`, `rewrite`, `unfold`, `simp`, `induction`,
  `exfalso`, `contradiction`, `by_cases`, `by_contra`
- `simp` computation for transparent formula definitions, set membership,
  subset expansion, and the left-recursive `add` equations
- kernel reporting of constructive versus classical proof use

## Next Milestones

1. Improve diagnostics with source spans and proof-state rendering.
2. Improve theorem-instantiation diagnostics and broaden inference.
3. Add an import mechanism for checked library files.
4. Broaden `simp` with more computation rules and optional hypothesis
   simplification.
