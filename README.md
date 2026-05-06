# Cetacea

Cetacea is a small tactic-based theorem prover following the design in
`MiniTactic_Theorem_Prover_Design.pdf`.

The current implementation covers propositional logic, a first-order layer with
typed variables, predicate applications, universal and existential
quantification, equality, transparent formula and term definitions, typed sets,
primitive recursive `Nat` definitions, and a small natural-number layer with
induction. Declarations and formula annotations are checked for known types,
known predicates, predicate arity, function arity, definition arity, set element
compatibility, and argument type compatibility.

## Layout

- `crates/cetacea_core`: parser, AST, tactics, proof objects, and kernel
  checker.
- `crates/cetacea_cli`: command-line checker.
- `crates/cetacea_wasm`: WebAssembly exports for checking, goal stepping, and
  proof explanations.
- `web`: static browser UI.
- `docs/USAGE.md`: language and proving guide.
- `docs/DESIGN_AND_CODE.md`: implementation and design guide.
- `std`: checked theorem-library files.
- `std/prelude.ctea`: imports the current standard-library theorem files.
- `examples/prop.ctea`: constructive and classical propositional examples.
- `examples/fol.ctea`: first-order examples.
- `examples/set_nat.ctea`: typed set and natural-number simplification examples.
- `examples/library_patterns.ctea`: larger standalone proof patterns over a
  small first-order domain.
- `examples/imports.ctea`: example use of checked theorem-library imports.

## Run

```sh
cargo test
cargo run -p cetacea_cli -- examples/prop.ctea
cargo run -p cetacea_cli -- examples/fol.ctea
cargo run -p cetacea_cli -- examples/set_nat.ctea
cargo run -p cetacea_cli -- examples/library_patterns.ctea
cargo run -p cetacea_cli -- examples/imports.ctea
cargo run -p cetacea_cli -- std/prelude.ctea
cargo run -p cetacea_cli -- std/set.ctea
cargo run -p cetacea_cli -- std/nat.ctea
```

Run the terminal interactive mode with:

```sh
cargo run -p cetacea_cli -- --interactive examples/prop.ctea
```

Interactive commands include `theorems`, `select`, `reset`, `step`,
`goals`, `hints`, `search`, and `explain`.

Build the WebAssembly checker and serve the browser UI from the repository
root:

```sh
rustup target add wasm32-unknown-unknown
cargo build -p cetacea_wasm --target wasm32-unknown-unknown --release
python3 -m http.server 8000
```

Then open:

```text
http://localhost:8000/web/
```

The CLI prints each accepted theorem or axiom from the root file and the
strongest mode used by its checked proof object.
Diagnostics for checked declarations and parse errors include the file and
command or tactic line when the checker has path information. Parser
diagnostics also carry line-local token spans where the parser can identify the
offending token.

Import paths are resolved relative to the importing file first, then relative
to the current working directory. A file imported more than once is checked and
loaded once.

## Implemented

- `mode constructive` and `mode classical`
- file imports with `import path/to/file.ctea`
- source outline, cursor goal, tactic-step, and proof-explanation APIs for
  editor integrations
- terminal interactive mode with goal display, tactic hints, theorem search,
  stepping, and proof explanations
- WebAssembly exports and a static browser UI for checking, goal stepping,
  tactic hints, diagnostic help, theorem-library search, and proof explanations
- virtual imports for browser-hosted standard-library files
- `sort`, `const`, `func`, `pred`, formula and term `def`, unary `Nat`
  `defrec`, and `axiom`
  declarations
- theorem declarations with proposition, predicate, type, and term parameters
- built-in `Nat`, `Set T`, numeric Nat literals, `0`, `succ(n)`,
  `add(n, m)`, `mul(n, m)`, and `sub(n, m)`, plus Nat predicate `le(n, m)`
- typed set terms: `empty(T)`, `singleton(x)`, `union(A, B)`, `inter(A, B)`,
  `diff(A, B)`, `powerset(A)`, and set builders `{ x : T | P(x) }`
- formulas: `True`, `False`, atoms, equality, membership, subset, `not`, `/\`,
  `\/`, `->`, `<->`
- first-order formulas: `forall x : T, P(x)`, `exists x : T, P(x)`, and
  same-type multi-binders such as `forall x y : T, R(x, y)`
- validation for type names, predicate names, predicate arity, and predicate
  argument types
- validation for function names, function arity, and function argument types
- validation for transparent formula and term definitions, including definition
  arity, inferred type parameters, and proposition/predicate parameters
- validation for unary primitive recursive `Nat` definitions
- validation for typed set membership and subset compatibility
- axiom declarations for trusted principles such as set extensionality
- checked library files for propositional logic, first-order logic, equality,
  sets, and natural numbers
- checked standard-library prelude
- examples checked by the core test suite
- goal-directed schema instantiation for bare theorem references in `exact` and
  `apply`
- explicit theorem-instantiation syntax:
  `exact theorem_name {A := Person; P := Happy; x := alice}`
- proof objects for natural-deduction rules over implication, conjunction,
  disjunction, truth, falsehood, universal quantification, existential
  quantification, equality reflexivity, equality substitution, natural-number
  induction, theorem references, and classical rules
- tactics: `intro`, `exact`, `trivial`, `assumption`, `apply`, `split`,
  `left`, `right`, `cases`, `exists`, `refl`, `rewrite`, `unfold`, `simp`,
  `induction`, `exfalso`, `contradiction`, `by_cases`, `by_contra`,
  `show_goal`
- `simp` computation for transparent formula definitions, primitive recursive
  Nat definitions, set membership, subset expansion, Nat arithmetic and
  comparison, including terms nested under predicate and function arguments
- kernel reporting of constructive versus classical proof use
- command and tactic-line reporting for checker diagnostics

## Next Milestones

1. Improve diagnostics with more precise source spans and richer recovery
   suggestions.
2. Improve theorem-instantiation diagnostics and broaden inference.
3. Broaden `simp` with more computation rules and optional hypothesis
   simplification.
