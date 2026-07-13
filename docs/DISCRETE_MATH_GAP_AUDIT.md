# Cetacea and an Undergraduate Discrete-Mathematics Sequence

## Audit summary

Cetacea has substantially achieved the narrower goal in the original design
document: it is a credible teaching prover for natural deduction, typed
first-order logic, equality, elementary sets, relations and functions, and
introductory induction. Its kernel/tactic distinction, constructive/classical
mode reporting, axiom receipts, countermodels, goal stepping, and checked
exercise corpus are unusually well aligned with teaching.

It is not yet capable of carrying a complete undergraduate discrete-mathematics
sequence as the primary medium. The current book is accurately subtitled "A
First Course in Logic": it is a strong logic-and-proof spine for discrete math,
not yet a discrete-mathematics textbook or course platform.

The product claim should distinguish two targets:

- As a proof-and-logic companion for a discrete-math course, Cetacea is close
  to pilot-ready after a semantic-correctness and documentation pass.
- As the primary medium for a complete sequence, it still needs foundational
  work in finite mathematics, arithmetic, recursive predicates, graph theory,
  curriculum content, and classroom workflow.

"Via FOL" also needs a precise boundary. Reachability in arbitrary graphs is
not definable in bare FOL without encoding paths or adding transitive closure,
and counting needs finite witnesses or additional structure. A sounder product
description is:

> Many-sorted FOL with equality is the logical foundation; datatypes,
> structural recursion, induction, typed sets, and finite enumerations are
> conservative teaching extensions.

## Implementation status

Phase 0 began with the datatype semantic slice from this audit. The checker now
treats distinct constructors as disjoint and equal applications of the same
constructor as injective in every argument. Tactic-facing normalization keeps
same-constructor equality goals folded for proof-script stability, while kernel
conversion and projections may use the component equalities. The bounded FOL
countermodel search declines constructor claims until it can enforce datatype
constraints. Regression tests cover disjointness without a discriminator,
multi-argument injectivity, binder shadowing, and suppression of the old
one-element constructor countermodel.

Strict and machine-readable course checking is also implemented: `--strict`
rejects root axioms and direct or transitive `sorry`, the component policies
may be selected separately, `--deny-classical` enforces constructive work, and
`--json` reports declarations, diagnostics, policy settings, and violations.
The corpus check now uses that declaration-level output to require every theorem
in a book `mistakes`, `fallacies`, or `negative` fixture to fail individually;
this closes the hole where one earlier diagnostic could mask a later example
that had silently started checking. It also verifies every quoted error headline
and acceptance receipt against live CLI output. Diagnostic paths are now relative
to the working directory in both text and JSON, so those excerpts are portable.

The principal remaining Phase 0 work is further isolation of the trusted kernel
into a smaller module with a narrower environment interface.

## Evidence reviewed

The audit covered the original PDF design, `README.md`, the implementation and
namespace design guides, the roadmap and friction log, the standard library,
examples, the CS 250 tutorials, all twelve drafted book chapters and companion
files, the CLI/TUI, the Wasm boundary, and the browser UI.

At the time of the audit:

- all 238 Rust tests passed;
- the corpus script checked all 74 `.ctea` files with their expected positive,
  negative, or incomplete status;
- native release and Wasm release builds passed;
- the book contained roughly 33,600 words and 79 theorem exercises;
- strict Clippy failed with 41 warnings, chiefly large `Err` variants, although
  ordinary compilation and tests were clean.

## What already works well

- Tactics elaborate to proof objects that are independently checked.
- Constructive versus classical use is visible per theorem.
- Axiom dependencies and unfinished proofs propagate visibly.
- Countermodels give excellent feedback for false propositional, arithmetic,
  and small first-order claims.
- Goal stepping, speculative tactic hints, proof explanations, theorem search,
  a terminal UI, and a browser UI all exist.
- The book's worked-example / deliberate-mistake / exercise / solution rhythm
  is pedagogically strong.
- Propositional proof systems, quantifiers, equality, set algebra, relation
  properties, and introductory induction are a particularly good fit.

## Curriculum coverage

| Area | Current state | Main gap |
|---|---|---|
| Logic and natural deduction | Strong | No truth-table/model explorer; limited bridge back to polished prose proofs |
| First-order logic | Strong | Limited predicate/function abstraction and inference |
| Sets | Good for identities | No finiteness or cardinality |
| Relations | Good for local properties | Thin coverage of orders, closures, equivalence classes, and quotients |
| Functions | Adequate as graph predicates | Functions are not first-class objects; no function equality or generic function spaces |
| Induction | Good introductory examples | No hypothesis generalization; several ordinary induction patterns are rejected |
| Data and recursion | Useful but incomplete | Monomorphic types, no recursive propositions, no mutual/deeper recursion |
| Number theory | Partial | No division, remainder, gcd, primes library, integers, or arithmetic procedure |
| Recurrences | Partial | Primitive unary recursion and strong induction cover selected examples only |
| Counting/combinatorics | Blocked | No finite-cardinality foundation |
| Graph theory | Mostly blocked | No generic paths/reachability, degree, finite vertex counts, or graph invariants |
| Probability | Absent | Depends on the missing finite/counting layer |
| Classroom workflow | Prototype | No strict grading mode, assignment policy, multi-file browser projects, or stable releases |

## Phase 0: restore the logical and documentary contract

### Datatype constructor semantics

A concrete probe exposed the highest-priority semantic gap:

```text
data Bit
| off
| on

theorem constructors_distinct : off = on -> False := by
  ...
```

Immediately after the datatype declaration, Cetacea cannot prove this and its
countermodel search reports a one-element domain in which `off = on`. After
defining a recursive discriminator mapping `off` to `0` and `on` to `1`, the
claim becomes provable. Adding an ostensibly conservative recursive definition
therefore strengthens the theory.

Every datatype declaration should immediately provide, through trusted and
checked principles rather than ordinary axioms:

- constructor disjointness;
- constructor injectivity;
- exhaustiveness/case analysis;
- a sound induction principle;
- countermodels that respect those semantics, or decline to model datatype
  claims.

Acceptance tests should include `off != on`, `nil != cons(h, t)`, head and tail
injectivity for `cons`, and a check that adding a discriminator does not change
which constructor facts are derivable.

### Draft holes versus kernel proofs

This separation is now implemented:

- `DraftProof`, which may contain holes and supports editing;
- `KernelProof`, whose private representation can only be constructed after a
  recursive hole check and is the only proof type accepted by `check_proof`;
- distinct `Accepted`, `Incomplete`, and `TrustedAxiom` result states in the
  checker API, CLI, JSON, and Wasm JSON.
- matching `Kernel`, `Incomplete`, and `TrustedAxiom` evidence variants in the
  theorem environment, so a hole-bearing draft cannot occupy a kernel-proof
  field.

Incomplete declarations remain available to later drafts and taint dependents,
but they are never labeled accepted and their hole-bearing proof is never sent
through the kernel boundary.

### Generalized induction

`revert h` now moves the most recent proof hypothesis back into an implication
goal, allowing a variable-dependent hypothesis to be reintroduced separately
inside each induction arm. Kernel induction rejects dependent context only when
the induction proof actually uses that unreverted hypothesis.

Generalizing additional term variables still needs either term-level `revert`,
`generalize`, or `induction ... generalizing ...` syntax.

### Recursive propositions

Structurally recursive definitions currently return terms, not propositions.
This blocks natural definitions such as:

- every list element satisfies a predicate;
- membership and duplicate-freedom;
- sortedness;
- valid graph paths;
- syntax well-formedness;
- recursively defined relations.

Allowing structurally recursive formula definitions, including predicate
parameters, is the most useful expressiveness addition after datatype
semantics.

### Trusted-core boundary

The logical kernel is conceptually separated from tactics, but it remains
embedded in a roughly 20,000-line file containing parsing, elaboration,
normalization, countermodels, imports, and tests. Phase 0 should identify the
actual trusted computing base and move toward a small kernel module with an
explicit environment interface and adversarial tests.

### Documentation as executable behavior

The corpus script now confirms that every declared theorem in a negative file
fails, closing the masking bug found during this audit. The stale Chapter 7
"forgetting to unfold" example has been replaced. It also treats each quoted
error headline and acceptance receipt as an assertion about live output.
Diagnostic paths are rendered relative to the working directory, eliminating
the machine-specific absolute paths that were embedded throughout the book.

### Strict course and grading mode

The CLI now provides machine-readable strict checking with controls to:

- fail on direct or transitive `sorry`;
- fail on root axioms or classical reasoning; and
- emit declaration, diagnostic, and policy JSON suitable for an autograder.

Restricting allowed imports and freezing expected theorem signatures remain
outstanding; without those controls, a student can still change an assigned
statement or import a stronger library than intended.

## Phase 1: stabilize the existing book and tutorials

1. Finish generalized induction.
2. Add recursive proposition definitions.
3. Add proposition/iff rewriting and a controlled simplifier registry.
4. Preserve exact source spans for checked expressions and tactics.
5. Finish namespace migration in the book and tutorials.
6. Extend executable documentation beyond the now-checked diagnostic headlines
   and acceptance receipts to longer, generated transcript blocks where useful.
7. Add repeated "erase the tactics" exercises that turn checked derivations
   into polished prose proofs and assess proof exposition.

## Phase 2: finite mathematics

A total `card : Set T -> Nat` would be misleading because an arbitrary typed
set need not be finite. A more FOL-friendly design makes cardinality a relation
backed by finite evidence:

```text
HasCard(A, n) :=
  exists xs : List T,
    Nodup(xs) /\ Enumerates(xs, A) /\ length(xs) = n
```

This requires:

- parameterized `List T`;
- recursive predicates such as `Nodup` and `Enumerates`;
- constructor disjointness/injectivity;
- a finite-set and cardinality library.

It avoids dependent types and makes finiteness evidence explicit, which fits
Cetacea's teaching philosophy.

Representative acceptance theorems should include finite union cardinality,
bijections preserving cardinality, and the pigeonhole principle.

On the `hol` migration branch, explicit finite enumeration, bijection
transport, and the generic constructive pigeonhole principle now pass through
the public source surface as Chapters 13–15. The remaining Phase 2 acceptance
work is to package the reusable removal/inclusion counting lemmas and exercise
them in finite-union cardinality rather than copy the pigeonhole proof
infrastructure.

## Phase 3: complete the discrete-mathematics arc

Build on finite mathematics with:

- arithmetic: `<`, exponentiation, division/remainder, gcd, primes, and
  integers;
- bounded arithmetic automation;
- sequences, finite sums, and recurrence libraries;
- graph schemas `(V : Type) (E : V -> V -> Prop)`;
- `ValidPath(E, p)` and reachability;
- degree and finite-graph cardinalities;
- counting principles and elementary discrete probability.

Roadmap completion should be tested by representative end-of-unit theorems,
not only by syntax features. Useful targets include the pigeonhole principle,
division with remainder, elementary gcd facts, path concatenation, the
handshake lemma, and `|E| = |V| - 1` for finite trees.

## Book and platform work

The current book is the most mature part of the project, but a complete
discrete-math sequence still needs later arcs on finite sets and cardinality,
counting, number theory, sequences and recurrences, graph theory, and optionally
probability.

For classroom deployment, Cetacea should also gain:

- promotion of the experimental native HOL assignment manifests and
  allowed-import policies to the browser/grading surface;
- stable tagged releases rather than only a moving Pages build;
- browser import/export and multiple project files;
- packaged binaries or a simpler installation path;
- configurable hints for assessment settings;
- a published project license.

## Recommended ordering

1. Fix datatype semantics and datatype-aware feedback.
2. Separate incomplete drafts from kernel-valid proof objects.
3. Make book diagnostics executable and synchronized.
4. Add strict/machine-readable checking for course use.
5. Generalize induction and permit recursive propositions.
6. Add polymorphic lists and the finite-cardinality witness layer.
7. Grow the number-theory, counting, recurrence, and graph libraries against
   curricular acceptance theorems.
