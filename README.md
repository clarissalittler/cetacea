# Cetacea

Cetacea is a small tactic-based theorem prover following the design in
`MiniTactic_Theorem_Prover_Design.pdf`.

The current implementation covers propositional logic, a first-order layer with
typed variables, predicate applications, universal and existential
quantification, equality, transparent formula and term definitions, typed sets,
user-declared inductive data types with structural induction, primitive
recursive `defrec` definitions over `Nat` and data types, and a natural-number
layer with ordinary and strong induction. Declarations and formula annotations
are checked for known types,
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
- `docs/DISCRETE_MATH_GAP_AUDIT.md`: curriculum coverage audit and staged
  course-readiness plan.
- `std`: checked theorem-library files.
- `std/prelude.ctea`: imports the current standard-library theorem files.
- `std/list.ctea`: `List` data type over `Nat`, recursive `length` and
  `append`, and length/associativity lemmas.
- `std/fun.ctea`: functions modeled as graphs, with `Total`, `SingleValued`,
  `Injective`, `Surjective`, identity-function theorems, and composition
  theorems.
- `examples/prop.ctea`: constructive and classical propositional examples.
- `examples/fol.ctea`: first-order examples.
- `examples/fol_advanced.ctea`: harder first-order examples — quantifier
  distribution laws, the drinker's paradox, the barber paradox, relation
  classification (reflexive/symmetric/transitive/antisymmetric/Euclidean),
  exists-unique packaging, and the quantifier De Morgan biconditionals.
- `examples/set_nat.ctea`: typed set and natural-number simplification examples.
- `examples/library_patterns.ctea`: larger standalone proof patterns over a
  small first-order domain.
- `examples/imports.ctea`: example use of checked theorem-library imports.

## Run

```sh
cargo test
./scripts/check_all.sh
cargo run -p cetacea_cli -- examples/prop.ctea
cargo run -p cetacea_cli -- examples/fol.ctea
cargo run -p cetacea_cli -- examples/fol_advanced.ctea
cargo run -p cetacea_cli -- examples/set_nat.ctea
cargo run -p cetacea_cli -- examples/library_patterns.ctea
cargo run -p cetacea_cli -- examples/imports.ctea
cargo run -p cetacea_cli -- std/prelude.ctea
cargo run -p cetacea_cli -- std/set.ctea
cargo run -p cetacea_cli -- std/nat.ctea
```

The corpus script checks every standard-library, example, CS250, and book
companion file. Every theorem in a `mistakes`, `fallacies`, or `negative`
fixture must be individually rejected, so one earlier diagnostic cannot hide
an accidentally accepted teaching example. Quoted book error headlines and
acceptance receipts are also checked against live CLI output.

Use strict, machine-readable checking for assignments and automation with:

```sh
cargo run -p cetacea_cli -- --strict --json path/to/submission.ctea
```

`--strict` rejects root axioms and incomplete root theorems. The granular
`--deny-sorry`, `--deny-axioms`, and `--deny-classical` policies can be composed
when a course needs a different trust or logic boundary.

Run the full-screen terminal TUI with:

```sh
cargo run -p cetacea_cli -- --tui examples/prop.ctea
```

`--interactive` and `-i` are aliases for the TUI. In the TUI, arrow keys move
through and edit the source buffer while the goal pane updates from the cursor
position. Use `m` for the command menu, `F2` for the theorem outline, `F3` for
theorem search, `F4` for proof explanations, `F5` for diagnostics, `Ctrl-S` to
save, and `Ctrl-Q` to quit. The older command-oriented terminal shell remains
available with `--line`.

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

The browser UI is also deployed automatically to GitHub Pages by
`.github/workflows/pages.yml`, which builds the WebAssembly checker and
publishes the contents of `web/` on every push to `main`.

The CLI prints each accepted theorem or axiom from the root file and the
strongest mode used by its checked proof object. Accepted lines are printed
for every passing theorem even when other theorems in the file fail. A proof
that depends on axioms, directly or through other theorems, lists them, as in
`accepted theorem length_append (constructive; axioms: append_cons,
append_nil)`, and a proof that uses the `sorry` tactic (directly or through a
sorry'd theorem) is reported as `(constructive; incomplete: uses sorry)`.
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
- full-screen terminal TUI with source editing, cursor-sensitive goal display,
  tactic hints, theorem outline, theorem search, diagnostics, and proof
  explanations
- line-oriented terminal shell with goal display, tactic hints, theorem search,
  stepping, and proof explanations
- WebAssembly exports and a static browser UI for checking, goal stepping,
  tactic hints, diagnostic help, theorem-library search, and proof explanations
- virtual imports for browser-hosted standard-library files
- `sort`, `const`, `func`, `pred`, formula and term `def`, `defrec`,
  `data`, and `axiom` declarations
- monomorphic inductive `data` declarations whose constructors become
  constants or functions, with structural `induction ... with` over them,
  including one induction hypothesis per recursive constructor argument
- checked datatype no-confusion: distinct constructors are disjoint and
  equal applications of one constructor expose equality of corresponding
  arguments
- primitive recursive `defrec` definitions over `Nat` and over declared data
  types, computed by `simp` and `refl`; additional fixed parameters after the
  recursive one support binary operations such as
  `defrec append (l : List) (r : List) : List`
- theorem declarations with proposition, predicate, type, and term parameters
- built-in `Nat`, `Set T`, numeric Nat literals, `0`, `succ(n)`,
  `add(n, m)`, `mul(n, m)`, and `sub(n, m)`, plus Nat predicate `le(n, m)`
- typed set terms: `empty(T)`, `singleton(x)`, `union(A, B)`, `inter(A, B)`,
  `diff(A, B)`, `powerset(A)`, and set builders `{ x : T | P(x) }`
- formulas: `True`, `False`, atoms, equality, membership, subset, `not`, `/\`,
  `\/`, `->`, `<->`
- Unicode aliases for the connectives: `∧`, `∨`, `¬`, `→`, `↔`, `∀`, `∃`,
  `∈`, `⊆`
- first-order formulas: `forall x : T, P(x)`, `exists x : T, P(x)`, and
  same-type multi-binders such as `forall x y : T, R(x, y)`
- validation for type names, predicate names, predicate arity, and predicate
  argument types
- validation for function names, function arity, and function argument types
- validation for transparent formula and term definitions, including definition
  arity, inferred type parameters, and proposition/predicate parameters
- validation for primitive recursive definitions, including per-constructor
  case coverage and binder counts
- dot-qualified top-level declaration and reference names, `namespace` /
  `end` blocks that prefix declarations, and import aliases such as
  `import std/nat.ctea as nat`
- validation for typed set membership and subset compatibility
- axiom declarations for trusted principles such as set extensionality
- checked library files for propositional logic, first-order logic, equality,
  sets, natural numbers (including strong induction), lists, and functions as
  graphs
- checked standard-library prelude
- examples checked by the core test suite
- goal-directed schema instantiation for bare theorem references in `exact` and
  `apply`
- explicit theorem-instantiation syntax:
  `exact theorem_name {A := Person; P := Happy; x := alice}`
- proof objects for natural-deduction rules over implication, conjunction,
  disjunction, truth, falsehood, universal quantification, existential
  quantification, equality reflexivity, equality substitution, natural-number
  induction, structural induction, theorem references, and classical rules
- tactics: `intro`, `exact`, `trivial`, `assumption`, `apply`, `split`,
  `left`, `right`, `cases`, `exists`, `refl`, `rewrite`, `unfold`, `simp`,
  `induction`, `exfalso`, `contradiction`, `by_cases`, `by_contra`,
  `show_goal`, `sorry` (alias `admit`), and `have` for forward reasoning
  (`have h : P`, `have h : P := proof`, `have h := proof`)
- projections and parenthesized sub-expressions inside proof-expression
  arguments, as in `exact f h.left` and `rewrite -> hinj x y (h.left)`;
  projections bind tighter than application
- `sorry` closes any goal; the theorem is accepted but reported as
  `incomplete: uses sorry`, and incompleteness propagates to theorems that
  use a sorry'd theorem, so instructors can distribute homework skeletons
- `cases h with | intro hp hq => ...` on conjunction hypotheses as well as
  existentials
- `refl` normalizes both sides of an equality goal, so pure computation facts
  such as `add(n, 0) = n` and `mul(2, 3) = 6` close without a preceding `simp`
- `exists` validates its witness term and reports type mismatches at the
  tactic line
- `simp` computation for transparent formula definitions, primitive recursive
  `defrec` definitions, set membership, subset expansion, Nat arithmetic and
  comparison, including terms nested under predicate and function arguments
- kernel reporting of constructive versus classical proof use
- per-theorem status reporting: `accepted` lines are printed for every passing
  theorem even when other theorems fail, and each line lists the axioms the
  proof depends on, directly or transitively
- propositional countermodel feedback: when a failed statement or open goal is
  purely propositional and classically falsifiable, the error notes a
  falsifying assignment, and the Goals panel warns that the goal is not
  provable
- goal hints are speculatively executed, so failing suggestions are dropped
- TUI undo and redo with Ctrl-Z / Ctrl-Y
- browser UI localStorage autosave, a load-example menu, inline error markers,
  and live re-checking
- command and tactic-line reporting for checker diagnostics
- strict course checking with composable `--deny-sorry`, `--deny-axioms`, and
  `--deny-classical` policies, plus `--json` output for autograders and CI

## Next Milestones

1. Parameterized (polymorphic) data types, so `List` and `Tree` can be
   declared once for any element type. Deliberately deferred: it requires
   polymorphic function signatures and a type-application form threaded
   through the whole kernel, while concrete declarations such as
   `data NatList` cover the course exercises.
2. Mutual recursion and recursion on later `defrec` arguments.
3. Cardinality and counting support for the combinatorics side of a discrete
   math course.
4. Decision procedures for modular arithmetic goals.
5. Finish migrating book and course examples to qualified standard-library
   names where that removes `_demo` collision workarounds.
