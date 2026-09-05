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
- `docs/HANDS_ON_TUTORIAL.md`: an executable first tour and focused
  pain-point lab, with `docs/tutorial/PLAYGROUND.ctea` as its companion.
- `docs/book`: the in-progress course text, exercises, solutions, deliberate
  failures, and assignment policies.
- `docs/USAGE.md`: language and proving guide.
- `docs/STUDENT_READINESS.md`: current completion checklist and verified limits.
- `docs/BROWSER_ASSIGNMENTS.md`: assignment loading, grading parity and trust boundaries.
- `docs/WEB_DISTRIBUTION.md`: reproducible browser bundles and deployment checks.
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
- `std/hol/counting.ctea`: checked set-relative finite-size evidence and
  reusable List counting lemmas over the versioned logical List package,
  including disjoint-union addition and the union upper bound.
- `std/hol/pigeonhole.ctea`: the checked constructive pigeonhole principle
  and its propositional-injectivity map lemmas over `HasCard`.
- `std/hol/probability_counts.ctea`: checked complement counts and expectation
  numerators for finite uniform sampling; [Chapter 22](docs/book/22-finite-probability.md)
  supplies coin/ticket examples and a native/browser assignment.
- `std/hol/pigeonhole_classical.ctea`: a positive collision-witness theorem
  with explicitly tracked classical reasoning. The [example](docs/hol/examples/pigeonhole_collision.ctea)
  also exhibits a concrete pair constructively.
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
cargo run -p cetacea_cli -- docs/tutorial/PLAYGROUND.ctea
cargo run -p cetacea_cli -- std/prelude.ctea
cargo run -p cetacea_cli -- std/set.ctea
cargo run -p cetacea_cli -- std/nat.ctea
```

The corpus script checks every standard-library, example, CS250, book
companion, and hands-on tutorial source. Every theorem in a `mistakes`,
`fallacies`, or `negative` fixture must be individually rejected, so one
earlier diagnostic cannot hide an accidentally accepted teaching example.
Quoted book error headlines and acceptance receipts are also checked against
live CLI output.

Use strict, machine-readable checking for assignments and automation with:

```sh
cargo run -p cetacea_cli -- --strict --json path/to/submission.ctea
```

`--strict` rejects root axioms and incomplete root theorems. The granular
`--deny-sorry`, `--deny-axioms`, and `--deny-classical` policies can be composed
when a course needs a different trust or logic boundary.

Every check is certified by the HOL kernel (the H7 cutover, see
[`docs/hol/H7_DECISION.md`](docs/hol/H7_DECISION.md)): the teaching checker
elaborates proofs, explains goals, and produces diagnostics, and the HOL
replay decides acceptance. A declaration the teaching checker accepts but the
kernel cannot replay is reported as a failed declaration and the file is not
certified. `--legacy-only` runs the teaching checker alone for debugging and
never certifies a file; it is refused together with `--hol-profile` or
`--assignment`, which need kernel receipts. Exact logical imports such as
`import std/hol/list@1 as L`, `import std/hol/finite@1 as F`,
`import std/hol/graph@1 as G`, or `import std/hol/cardinality@1 as C` are checked by the kernel even under
`--legacy-only`, including when the package import is reached through another
source file. The finite package exposes its checked List dependency under the
same alias. The graph package supplies explicit directed paths and their
endpoint equations; [the path guide](docs/REACHABILITY.md) includes a checked
source-level concatenation proof. The cardinality package exposes checked
`map`, `map_nil`, `map_cons`, `map_length`, membership transport,
injective-Nodup, surjective coverage, and the final `cardinality_transport`
theorem. Because `map` consumes a function argument, its uses are honestly
reported as `hol`. The checked `std/hol/counting.ctea` source module builds
set-relative `HasSize` and first-order-inductive counting support over the List
package without forcing those clients into HOL.

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

For a self-contained copy with a visible build ID, use:

```sh
python3 scripts/build_web.py --output target/web-distribution
python3 -m http.server --bind 127.0.0.1 --directory target/web-distribution 8000
```

The output directory must be new. Its assets and Wasm are stored under a
build-specific path and described by a hash manifest. See
[`docs/WEB_DISTRIBUTION.md`](docs/WEB_DISTRIBUTION.md).

`.github/workflows/pages.yml` is configured to run the reusable CI workflow
before packaging and deploying this bundle on pushes to `main`. This describes
the checked-in configuration, not verification of a current remote deployment.

Browser checks are dual-certified: the teaching UI and the HOL replay must both
accept the file. Exact logical imports work in checking, goal stepping, and
proof explanations; the status and theorem library show the imported packages
and certified least fragment. The bundled HOL examples derive length over List
append and the cardinality of a one-constructor datatype through the public
package surfaces. Browser regressions also run the checked finite-union and
hands-on tutorial sources through their source-module imports.

The CLI prints each root declaration as `accepted theorem`, `incomplete
theorem`, or `trusted axiom`, together with the strongest mode used by a proof.
Status lines are printed for every retained declaration even when other
theorems in the file fail. A proof
that depends on axioms, directly or through other theorems, lists them, as in
`accepted theorem length_append (constructive; axioms: append_cons,
append_nil)`, and a proof that uses the `sorry` tactic (directly or through a
sorry'd theorem) is reported as `incomplete theorem ... (constructive; uses sorry)`.
Diagnostics for checked declarations and parse errors include the file and
command or tactic line when the checker has path information. Parser
diagnostics also carry line-local token spans where the parser can identify the
offending token.

Independent aliases of the same logical package share type and symbol identity.
For example, a value of `F.List Nat` can be passed to `C.length` when both aliases
refer to `std/hol/list@1`, including through finite, cardinality, or counting
imports. Goals may display the first imported spelling. See the checked
[`package-alias example`](docs/hol/examples/package_aliases.ctea).

Import paths are resolved relative to the importing file first, then relative
to the current working directory. If an exact `std/...` source is absent,
Cetacea uses the standard library bundled with the checker, so homework also
checks outside the repository. `import builtin:std/nat.ctea as nat` explicitly
selects that bundled copy. Its dependencies come from the same bundle. A file
imported more than once under the same alias is checked and loaded once.

The prelude's concrete `List` and counting's generic `List A` remain distinct:
combine them with `import std/hol/counting.ctea as Counting`. See the
[checked coexistence example](docs/hol/examples/prelude_counting.ctea).
A failed import publishes no partial declarations or receipts. Its diagnostic
points to the caller's import line, and later declarations wait until the import
is fixed; declarations checked before the import remain reported.

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
  tactic hints, diagnostic help, theorem-library search, proof explanations,
  and fail-closed HOL package certification
- virtual imports for browser-hosted standard-library files
- `sort`, `const`, `func`, `pred`, formula and term `def`, `defrec`,
  `data`, and `axiom` declarations
- monomorphic inductive `data` declarations whose constructors become
  constants or functions, with structural `induction ... with` over them,
  including one induction hypothesis per recursive constructor argument
- checked datatype no-confusion: distinct constructors are disjoint and
  equal applications of one constructor expose equality of corresponding
  arguments; built-in Nat numerals get the same treatment, so
  `contradiction` and `simp` refute decided-false closed equalities such
  as `1 = 2` and `succ(n) = 0` in both engines
- primitive recursive `defrec` definitions over `Nat` and over declared data
  types, computed by `simp` and `refl`; additional fixed parameters after the
  recursive one support binary operations such as
  `defrec append (l : List) (r : List) : List`
- theorem declarations with proposition, predicate, rank-one saturated
  function-symbol, type, and term parameters
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
- tactics: `intro`, `revert`, `exact`, `trivial`, `assumption`, `apply`, `split`,
  `left`, `right`, `cases`, `exists`, `refl`, `rewrite`, `unfold`, `simp`,
  `induction`, `exfalso`, `contradiction`, `by_cases`, `by_contra`,
  `finite`, `show_goal`, `sorry` (alias `admit`), and `have` for forward reasoning
  (`have h : P`, `have h : P := proof`, `have h := proof`)
- projections and parenthesized sub-expressions inside proof-expression
  arguments, as in `exact f h.left` and `rewrite -> hinj x y (h.left)`;
  projections bind tighter than application
- `sorry` closes any goal; the declaration is reported as an
  `incomplete theorem`, and incompleteness propagates to theorems that
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
- browser source/project open and download, autosave, recovery checkpoints,
  damaged-save recovery and concurrent-tab conflict protection
- separate instructor assignment loading with pinned libraries, shared native
  policy enforcement, saved task selection and explicit assignment feedback
- browser cancellation/recovery, diagnostic navigation, keyboard section links,
  theorem search and insertion, and live re-checking
- command and tactic-line reporting for checker diagnostics
- strict course checking with composable `--deny-sorry`, `--deny-axioms`, and
  `--deny-classical` policies, plus `--json` output for autograders and CI

## Next Milestones

The HOL replay is now part of production checking, with enforceable teaching
profiles and shared native/browser assignment policy. The remaining work is
tracked in [`docs/STUDENT_READINESS.md`](docs/STUDENT_READINESS.md); the older
[`docs/HOL_REARCHITECTURE_PLAN.md`](docs/HOL_REARCHITECTURE_PLAN.md) records the
architecture's staged development. Browser and source-level regression tests do
not establish classroom outcomes or a completed accessibility audit.

1. Add executable equality/membership decisions and a list-valued union API.
   [Constructive union witnesses](docs/CONSTRUCTIVE_UNIONS.md) are now checked
   from explicit logical membership decisions, including their size bound.
2. Publish stable checked source libraries as versioned logical packages
   without manually duplicating their proofs as Rust terms.
3. Build the next counting/graph verticals: handshake and finite-tree
   edge/vertex theorems.
4. Extend user-declared datatypes beyond the current monomorphic surface and
   add mutual recursion or recursion on later `defrec` arguments when a course
   example requires them.
5. Grow arithmetic with division/remainder, gcd, primes, integers, and useful
   decision procedures.
6. Complete checking resource budgets, source-library publication, accessibility
   verification and a real classroom pilot.
