# Cetacea HOL Re-architecture Plan

## Decision and scope

Cetacea will investigate a constructive, simply typed higher-order logical core
while preserving propositional, first-order, and first-order-with-induction
fragments as enforceable teaching modes.

This branch is an architectural experiment, not yet a commitment to replace the
current checker. No existing syntax or course file should be removed until the
prototype gate in this document passes.

The intended destination is deliberately smaller than a general-purpose proof
assistant:

- simple types, type constructors, and rank-1 polymorphic declarations;
- first-class functions and predicates;
- inductive datatypes and structurally terminating recursion;
- intuitionistic natural deduction as the base logic;
- explicit, tracked use of classical reasoning, extensionality, choice, and
  trusted axioms;
- no dependent types, universes, type classes, quotient kernel, general
  recursion, or tactic-generated trusted proof shortcuts.

The existing many-sorted FOL language remains a supported surface fragment. A
student should not need to know that a stronger internal core exists while
working through a propositional or FOL assignment.

## Why pause at this boundary

The existing core is a good fit for logic, relations, elementary sets, and
introductory induction. The next curriculum features are also the features that
would commit the representation most strongly:

- parameterized `List A` and other polymorphic datatypes;
- recursive predicates such as `All`, `Member`, `Nodup`, `Sorted`, and
  `ValidPath`;
- reusable function and predicate abstraction;
- finite enumerations and cardinality;
- graph and combinatorics libraries shared across vertex and element types.

All of these can be encoded over FOL, but the accumulation of schema parameters,
monomorphic duplicate libraries, and explicit graph encodings risks making the
representation dominate the mathematics. A small HOL-like core makes the
library natural while a fragment checker preserves the pedagogical distinction
between propositional, first-order, inductive, and higher-order reasoning.

The completed datatype, strict-policy, draft/kernel, executable-documentation,
and induction-reversion work is retained in either architecture.

## Non-negotiable invariants

1. **Kernel evidence has no holes.** `DraftProof` and `KernelProof` remain
   distinct, and no incomplete declaration is accepted as kernel evidence.
2. **The constructive base stays constructive.** Classical reasoning is an
   explicit proof feature, not an ambient property of “HOL mode.”
3. **Trust is transitive and visible.** A theorem inherits relevant features,
   axioms, and incomplete dependencies from everything it uses.
4. **FOL restrictions cannot be laundered through imports.** A first-order
   theorem proved using a higher-order lemma is not acceptable in an assignment
   that forbids higher-order reasoning merely because its final statement is
   first-order.
5. **Current course files are a compatibility suite.** Existing `.ctea` files
   retain their meaning, proof mode, diagnostics contract where promised, and
   accepted/incomplete/trusted status.
6. **Countermodels remain honest.** Model search runs only on formulas certified
   to be in a fragment it actually models.
7. **Definitions are conservative.** Recursive definitions must pass positivity
   and structural-termination checks; arbitrary equations are axioms, not
   definitions.

## Target logical core

### Types

The core type language should initially contain:

```text
A, B ::= Prop
       | α                         type variable
       | C A1 ... An               declared type constructor
       | A -> B                    function type
       | A * B                     product type (optional in the first spike)
```

`Prop` is a distinguished type of propositions. This is simple type theory, not
dependent type theory: term types do not depend on term values.

Rank-1 polymorphism is sufficient for the curriculum. Datatypes and declarations
may quantify over type parameters, but terms do not take polymorphic values as
ordinary arguments. The spike must decide whether polymorphic declarations are
checked schematically in the kernel or elaborated to explicit type parameters;
it must not rely on unchecked monomorphization.

### Terms and propositions

Core terms should include variables, constants, typed lambda abstraction,
application, datatype constructors, and eliminators. Logical constants have
typed core representations equivalent to:

```text
True False                  : Prop
and or implies              : Prop -> Prop -> Prop
not                         : Prop -> Prop
eq[A]                       : A -> A -> Prop
forall[A], exists[A]        : (A -> Prop) -> Prop
```

The surface syntax remains familiar:

```text
forall x : A, P(x)
exists x : A, P(x)
P /\ Q
fun x : A => t
```

Internally, quantification is allowed over every simple type. Fragment
classification determines when a particular use is first-order or
higher-order.

### Proofs

Keep explicit natural-deduction proof evidence rather than identifying proofs
with arbitrary terms. The current proof constructors provide a useful starting
point. Generalize their formula fields from the old `Formula` representation to
well-typed core terms of type `Prop`.

The kernel API should be narrow:

```rust
pub fn check(
    signature: &KernelSignature,
    context: &KernelContext,
    proof: &KernelProof,
    expected: &CoreTerm, // already checked to have type Prop
) -> Result<ProofReceipt, KernelError>;
```

Parsing, name resolution, implicit argument inference, tactic execution,
countermodel search, source locations, and educational suggestions stay outside
the trusted kernel module.

### Equality and extensionality

The kernel starts with typed equality introduction and substitution. Beta and
datatype computation are definitional equality. Function extensionality,
propositional extensionality, choice, quotient principles, and classical rules
must not silently enter definitional equality.

If supplied, they are explicit rules or named trusted principles whose use is
recorded in the theorem receipt. This avoids inheriting the usual classical HOL
foundation by accident.

### Inductive datatypes and recursion

The first supported form is strictly positive, parameterized inductive data:

```text
data List (A : Type)
| nil
| cons(A, List A)
```

The declaration elaborator generates constructor typing, no-confusion,
exhaustiveness, and induction metadata. Structural recursive definitions may
return any simple type, including `Prop`:

```text
defrec All (A : Type) (P : A -> Prop) (xs : List A) : Prop
| nil => True
| cons x tail rec => P(x) /\ rec
```

The termination checker accepts only recursive calls on declared recursive
constructor fields in the first implementation. Mutual, nested, course-of-
values, and general well-founded recursion are later extensions.

## Teaching fragments and receipts

“Mode” must become an auditable property of both statements and proofs rather
than a parser toggle.

### Statement classification

After elaboration, classify each theorem statement at its least required level:

1. **Prop** — propositional variables and logical connectives only.
2. **FOL** — quantifiers range only over first-order types; functions and
   predicates occur as saturated declared symbols; no function/predicate values,
   higher-order variables, or lambda values remain.
3. **FOL + inductive data** — the statement is first-order but mentions
   inductive types or recursively defined first-order symbols.
4. **HOL** — quantification over `Prop` or arrow types, function/predicate
   variables as values, partial application, or higher-order equality.

A first-order type contains no arrow and no `Prop` as a data component. This
rule must be centralized and unit tested.

### Proof features

Kernel and elaborator steps accumulate an explicit feature set such as:

```text
Classical
Induction
StructuralRecursion
HigherOrderAbstraction
HigherOrderInstantiation
FunctionExtensionality
PropositionalExtensionality
Choice
TrustedAxiom(name)
Incomplete(name)
```

Every theorem stores a receipt containing:

- least statement fragment;
- direct proof features;
- transitive proof features;
- axiom dependencies;
- incomplete dependencies;
- imported theorem dependencies needed for auditing.

Receipts are recomputed from checked evidence and dependency receipts, never
asserted by source annotations.

### Course policies

Extend the current strict checker with an assignment manifest:

```text
profile = "fol+induction"
allow_classical = false
allow_extensionality = false
allow_new_axioms = false
allowed_imports = ["std/prop.ctea", "std/nat.ctea"]
required_theorems = [
  { name = "exercise_3", statement = "...canonical form..." }
]
```

The checker rejects a declaration if its statement or transitive proof receipt
exceeds the profile. Required theorem signatures prevent students from proving a
weakened replacement. Import allowlists prevent capability escalation through a
stronger library.

The UI should display compact labels such as `fol`, `fol+induction`, or `hol`,
plus separate `classical`, `axioms: ...`, and `incomplete` markers.

## Software architecture

The current `cetacea_core/src/lib.rs` combines syntax, elaboration, tactics,
kernel checking, definitions, imports, models, and tests. The migration should
first introduce boundaries without changing behavior.

Target modules inside `cetacea_core` are:

```text
syntax/          surface AST, tokens, parser, source spans
resolve/         namespaces, imports, declaration identity
elab/            type inference, implicit arguments, surface-to-core lowering
core/            CoreType, CoreTerm, alpha-equivalence, substitution
kernel/          KernelSignature, KernelContext, KernelProof, proof checking
inductive/       positivity, constructor metadata, recursion/induction schemes
tactic/          goals, DraftProof, tactic elaboration, hints, explanations
fragment/        statement classification, feature receipts, policy checking
model/           propositional/FOL/arithmetic countermodels
driver/          FileChecker and public editor/checking APIs
```

Only `core`, `kernel`, and the soundness-critical portion of `inductive` belong
to the trusted computing base. The dependency direction is one-way: the kernel
must not import parser, tactic, model, CLI, filesystem, or diagnostic modules.

During migration, keep the current public `check_file*`, goal, explanation, CLI,
and Wasm APIs as a facade. New receipt fields may be added compatibly to JSON.

## Migration phases and gates

### Phase H0 — freeze and measure

Status: the deterministic semantic corpus oracle and initial artifact/timing
report are in place. The public legacy kernel now accepts an opaque
`KernelSignature` rather than the complete `Env`; shrinking its internal view
and extracting modules remain H1 work. CI rejects new parser, tactic, UI,
filesystem, driver, or countermodel dependencies in the kernel module.

- Tag the current FOL baseline and keep `main` releasable.
- Record golden JSON for the standard library, examples, book, and CS250 corpus.
- Add adversarial tests for draft holes, datatype no-confusion, axiom receipts,
  classical receipts, import aliases, and FOL countermodel eligibility.
- Capture baseline build time, test time, Wasm size, and checker latency.

Exit gate: the old checker can be run as a reproducible oracle on all 74 corpus
files, including expected negative declarations and quoted documentation.

### Phase H1 — extract the current kernel boundary

- Split modules along the target dependency direction without changing the old
  `Type`, `Term`, `Formula`, or proof semantics.
- Replace broad `&Env` access in kernel code with a minimal read-only
  `KernelSignature` trait or value.
- Move normalization used by definitional equality into the trusted core;
  educational simplification remains outside it.

Exit gate: the full corpus and golden JSON are unchanged, the kernel dependency
graph has no parser/tactic/model/driver edge, and formatting plus strict linting
can run per module.

### Phase H2 — parallel HOL core

Status: `hol::types` now defines resolved simple types, stable constructor and
parameter IDs, constructor-arity validation, and conservative first-order
domain classification. `hol::terms` adds resolved constants, de Bruijn binders,
typed lambdas/application, capture-avoiding beta substitution, and checked
normalization. Rank-1 constant schemes now require explicit core type
applications, validate scheme binders, substitute through nested types, and
enforce first-order parameter constraints. Primitive proposition terms and a
hole-free constructive proof checker cover connectives, quantifiers over
arbitrary simple types, typed equality, and equality elimination through
explicit predicate motives. The
new `hol::fragments` layer beta-normalizes and classifies checked statements,
then derives deterministic transitive receipts and enforces constructive
Prop/FOL/FOL+induction/HOL policies. Its adversarial tests reject higher-order
dependency laundering and propagate classical, axiom, and incomplete taint.
The checker is still hand-constructed: theorem declarations and surface
elaboration have not begun.

- Add `CoreType` and typed `CoreTerm` without deleting the old AST.
- Implement capture-avoiding substitution, alpha-equivalence, beta reduction,
  type checking, and a fuel-independent normalization strategy for the accepted
  terminating fragment.
- Add the narrow HOL kernel proof checker and property/adversarial tests.

Exit gate: hand-constructed proofs cover constructive propositional logic,
many-sorted FOL, typed equality, and higher-order universal instantiation; holes,
ill-typed terms, capture bugs, and disallowed classical steps are rejected.

### Phase H3 — inductive and polymorphic spike

Decision: **H3.5 is complete and a bounded H4a compatibility substrate is
authorized; cutover is not.** See
[`hol/H35_EXIT_DECISION.md`](hol/H35_EXIT_DECISION.md) for the exit decision and
linked measurements, and
[`hol/H3_DECISION_REPORT.md`](hol/H3_DECISION_REPORT.md) for the original H3
checkpoint.

Status: the checked declaration substrate now supports transactional,
parameterized inductive types and explicit polymorphic constructor schemes.
It derives first-order preservation from constructor fields, records direct
recursive fields, rejects negative occurrences, and deliberately rejects
nested recursion pending a later design. Structurally recursive definitions now
receive only constructor fields and precomputed results for declared recursive
subdata; constructor reduction is definitional, works for `Prop` results, and
cannot name the function being defined. Type-constructor parameter classes are
also enforced at every core type occurrence. The proof checker now has an
explicit structural-induction rule whose exhaustive cases receive constructor
fields and induction hypotheses only for recorded recursive fields; a
hand-built constructive `List` induction principle passes. The small surface
spike elaborator now resolves names immediately to stable core IDs, maintains
fragment metadata, kernel-checks proofs, and derives induction features from
checked evidence before constructing receipts. Typed constructor disjointness
and injectivity are also explicit kernel rules backed by the inductive
signature. Two of the three full curriculum examples are now executable: the
list example checks generic
`All`, `Member`, `Nodup`, `append`, and `length`, while the graph example proves
constructively that concatenating endpoint-valid paths preserves validity.
Both produce trust-free `fol+induction` receipts and exercise deliberate type,
termination, and positivity rejections. The finite example now adds two checked
finite datatypes, exhaustive duplicate-free enumerations, structural
encode/decode maps, inverse proofs, and a shared cardinality witness, again with
no trust. H3.5 now adds a reusable, stored cardinality-transport theorem and
checked `map` lemmas for length, membership, duplicate-freedom, and coverage.
The concrete theorem is checked both directly and by reusing this generic
result: the direct proof remains `fol+induction`, while the reused proof is
honestly `hol` because its transitive dependency quantifies over functions.
H3.5 also adds stable
checked theorem IDs, explicit type-instantiated theorem references, schematic
type-scope validation, and transitive theorem/structural-definition receipts
derived from statements and hole-free evidence. The three examples have been
migrated off caller-authored dependencies. A compact release smoke now keeps
the engine reachable in native and Wasm artifacts. The mechanical map in
[`hol/FOL_TO_HOL_LOWERING.md`](hol/FOL_TO_HOL_LOWERING.md) covers every legacy
form and identifies the eight compatibility prerequisites for H4a.

Implement only enough surface elaboration and inductive infrastructure for
these three end-to-end examples:

1. `List A`, `All`, `Member`, and `Nodup`, including an induction theorem.
2. A generic graph edge relation, `ValidPath`, and path concatenation.
3. Finite enumeration evidence, `HasCard`, and cardinality preservation under a
   bijection.

Each example must have at least one positive proof, one deliberate type error,
one termination/positivity rejection, and an accurate fragment receipt.

**Stop/go decision:** do not authorize wholesale migration unless the spike:

- needs no new untracked axiom;
- makes the examples materially clearer than their FOL encodings;
- keeps the trusted core small enough to audit;
- certifies ordinary examples as FOL or FOL+induction where appropriate;
- rejects higher-order dependency laundering under an FOL policy;
- has an acceptable Wasm size and interactive latency;
- offers a credible mechanical lowering path for the existing corpus.

If this gate fails, retain the FOL kernel and port only the successful library or
fragment-receipt ideas.

### Phase H4 — compatibility elaborator

Status: **H4 shadow exit gate passed; default cutover is not yet authorized.**
The production command/import driver now has an opt-in, non-authoritative HOL
sidecar. It receives the same canonical declarations that the legacy checker
has accepted, preserves aliases and declaration order, and reports any lowering
or receipt disagreement separately. `python3 scripts/hol_shadow.py check`
currently matches all 74 corpus files and all 588 root theorem/axiom receipts,
while the frozen legacy oracle still rejects all 38 intended-negative theorems.
The legacy checker remains the default authority until the H5 policy/UI work
and an explicit cutover decision. The first substrate checkpoint supports checked rank-one
term/proposition/predicate-symbol theorem templates, simultaneous
capture-avoiding reference instantiation, and FOL classification of saturated
symbol parameters. Missing and ill-typed arguments are rejected
transactionally; legacy surface parameter inference is connected at the shared
canonical-AST seam.
H4a also now stores typed trusted axiom templates and propagates their IDs
through checked theorem receipts. Explicit excluded-middle,
double-negation-elimination, and contradiction evidence is kernel-checked and
adds a transitive `Classical` feature; constructive policies reject it unless
explicitly allowed. Typed incomplete theorem drafts are now checked and retained
outside the kernel, can depend on other incomplete drafts, and produce
transitive incomplete receipts. The checked theorem-reference path rejects
incomplete declarations, preventing dependency laundering. Surface
axiom/classical/incomplete lowering is connected. H4a also has checked, closed,
rank-one transparent definitions: the body is validated before its constant is
installed, declaration order rules out delta cycles, and normalization unfolds
definitions through beta and existing structural computation. Their receipts
retain dependencies while concrete instances determine the statement fragment.
Surface `def`, `unfold`, `simp`, and conversion evidence is connected.
Typed product introduction and both projections are now core terms as well;
projection reduction is definitional, capture-safe under binders, and
first-order whenever the component types are first-order. Legacy `Pair`/`Fst`/
`Snd` lowering is connected.
Structural definitions now carry a checked recursive-argument index. The
declared function type, reduction scrutinee, and every generated recursive call
use that position consistently; invalid indices leave signatures unchanged.
This removes the former reversed-argument workaround from the graph `append`
spike and matches legacy `defrec`, whose recursive parameter is first.
The H4a core now also has a distinguished first-order `Set A` wrapper rather
than the tempting higher-order encoding `A -> Prop`. All current membership and
subset computations—including powersets, Cartesian products, and capture-safe
comprehensions—are definitional. Set extensionality remains an explicit trusted
axiom and taints every transitive user; the linked smoke checks that its theorem
still has an FOL statement receipt alongside that separate trust evidence.
Theorem dependency receipts are now instance-aware. Proof checking records the
fully instantiated referenced statement together with its local de Bruijn term
context; receipt derivation recomputes only that statement fragment and keeps
all trust, incompleteness, feature, and transitive-dependency evidence. This
removes false HOL taint from concrete first-order uses without opening a
dependency-laundering path. Specialization recurses through generic theorem
wrappers and reconstructs nested binder contexts rather than trusting the
generic declaration's conservative fragment.

The checked compatibility prelude installs inductive `Nat`, first-order `Set`,
structurally recursive arithmetic, and nested-structural `le` transactionally.
The legacy evaluator's overlapping other-argument arithmetic shortcuts remain
intentionally outside kernel conversion because they are not
substitution-stable. Seven internal induction theorems prove the secondary
`add`, `mul`, and `sub` orientations. Legacy `Convert` nodes normalize with
those theorems and elaborate every step to explicit equality elimination;
no-op rewrites retain their theorem dependency through a constant motive.

A parser-independent lowerer covers every legacy type, term, formula,
declaration, and proof-object form, including capture-safe rewrite motives,
quantifiers, theorem substitutions, classical rules, Nat/data induction,
polymorphic transparent definitions, monomorphic direct-recursive datatypes,
and legacy `defrec` with its exact branch binder layout. The shadow driver now
connects that layer to parsed commands, recursive imports, and aliases without
changing ordinary checking behavior.

- Done: lower theorem/axiom declarations and every legacy proof expression,
  along with `sort`, `const`, `func`, `pred`, `def`, `data`, `defrec`, formulas,
  and predicate lambdas.
- Done: preserve existing name resolution and import behavior through the
  legacy driver's qualified canonical declarations and stable HOL identities.
- Done: elaborate old monomorphic direct-recursive datatypes as zero-parameter
  inductive types.
- Preserve the current tactic language by changing its generated evidence, not
  rewriting course scripts.

Exit gate: all existing positive files check in both engines with matching
statuses, modes, axiom/incomplete dependencies, and theorem statements. Every
negative theorem remains rejected individually. **Passed in shadow mode:**
74/74 files, 588/588 root receipts, 9,389/9,389 accepted declaration
occurrences, and zero mismatches. Required-fragment distribution is 108 `prop`,
234 `fol`, and 246 `fol+induction`; status distribution is 483 checked, 81
incomplete, and 24 trusted axioms. Surface statement identity is shared at the
canonical AST seam rather than compared through a lossy text round-trip; the
HOL kernel independently checks the lowered statement and evidence. The native
CLI release is 3,346,328 bytes. Because the browser API does not expose shadow
checking, `cetacea_wasm` disables the `hol-shadow` Cargo feature and remains
1,351,837 bytes, below the 1.5 MB review line.

### Phase H5 — fragment enforcement and assignment manifests

Status: **native CLI policy, assignment manifests, and certified native editor
hints implemented.** The shadow report now
retains kernel-created declaration receipts and stable names. An opt-in
`--hol-profile prop|fol|fol+induction|hol` checks root declarations with their
transitive used dependencies; profiles remain constructive, trust-free, and
complete unless `--allow-classical`, `--allow-axioms`, or
`--allow-incomplete` is supplied. Text and JSON results name violations, and
adversarial tests separate fragment level from classical reasoning, trust,
incompleteness, and unused imports. A versioned, fail-closed
`--assignment` manifest now fixes those dimensions, every transitively resolved
filesystem import, individually permitted imported axioms, and exact root
theorem signatures including their canonical parameter telescopes. A local
student axiom cannot impersonate an allowed imported axiom. Ordinary checking
remains unchanged. Failed theorems in native shadow mode are now classified
before a receipt exists; truth-table, bounded first-order, and bounded Nat model
search are selected only by that certified least fragment, while HOL or failed
classification produces no weaker-fragment countermodel claim. The pre-receipt
classifications, including rejected theorem names, full
signatures, fragments, locations, and import provenance, are exposed in shadow
JSON for audit. The exact corpus gate now checks 600/600 elaborated root theorem
statements, including 36 proof-level intended rejections; two deliberately
ill-typed negative signatures are rejected before classification. Native TUI
and line-mode goal and explanation requests can now opt in with `--hol-shadow`:
the full theorem signature is classified before tactic stepping, the certified
fragment is shown in the interface, and countermodel hints are gated by that
fragment. Legacy editor entry points remain unchanged. H5 still owns
Wasm/browser result and policy surfaces, interactive assignment-policy
enforcement, and structural signature fingerprints after the syntax
stabilizes.
The first policy checkpoint's native CLI release was 3,396,656 bytes; the
feature-isolated Wasm module was unchanged at 1,351,837 bytes. The
manifest checkpoint is 3,482,976 bytes natively and 1,351,852 bytes in Wasm;
the browser artifact grew by only 15 bytes and remains below the 1.5 MB review
line. At the auditable pre-receipt/countermodel checkpoint they are 3,495,424
and 1,351,920 bytes respectively; the no-shadow browser path grows by 68 bytes
and remains below the review line.
At the certified native-editor checkpoint they are 3,500,184 and 1,351,199
bytes respectively; feature isolation still keeps the HOL sidecar out of the
browser artifact, which remains below the review line.

- Implement least-fragment classification and transitive feature receipts.
- Native CLI text/JSON and versioned manifests are implemented; extend Wasm
  JSON, browser results, and interactive assignment-policy enforcement after
  the policy format settles.
- Native allowed-import, named imported-axiom, and frozen full-signature
  policies are implemented.
- Native shadow file diagnostics and opt-in native editor goal hints consume
  the certified fragment. Browser goal hints retain legacy routing until the
  browser surface adopts HOL state.

Exit gate: adversarial tests demonstrate that a syntactically FOL theorem proved
through HOL, choice, extensionality, classical reasoning, or an unallowed import
is rejected by the corresponding course policy. The native manifest portion now
has executable tests for fragment boundaries, independent classical/trust/draft
permissions, transitive used axioms, exact resolved imports, named imported
axioms, missing or changed full signatures, local-axiom impersonation, and
certified Prop/FOL/inductive/HOL countermodel dispatch. The pre-receipt gate is
600/600 for all elaborated root theorem statements. Native editor tests also
show that legacy entry points remain uncertified while opt-in goal, tactic-step,
and explanation entry points preserve certified Prop/FOL/inductive dispatch.

### Phase H6 — library and curriculum migration

Status: **in progress; reusable HOL list, graph, and cardinality substrates
extracted.** A transactional `ListLibrary` now installs parameterized `List A`,
its constructors, `All`, `Member`, `Nodup`, and `append`, with an optional
checked Nat `length`
extension. The list, graph-path, and finite-cardinality examples all consume
the same typed handles instead of redeclaring variants. Cardinality transport
is now a public, namespaced, transactional package exposing `map`, all five
supporting theorem handles, and the final theorem. Its receipt test fixes the
complete direct dependency set and verifies that every theorem is trust-free
and classified `hol`. It is registered as `std/hol/cardinality@1`, with all
seven declarations, stable receipt names, and an explicit dependency on
`std/hol/list@1`. The complete dependency closure installs atomically and
reinstallation validates cross-package receipt bindings. Tests demonstrate the
central mode claim directly: the
same unrestricted library has a `fol+induction` Nat
or graph instance and a `hol` `Prop` instance, while the existing graph and
finite proof receipts retain their prior least fragments. This package is
now installable on demand through the compatibility elaborator's versioned
registry as `std/hol/list@1`. Its reserved core namespace, declaration catalog,
definition-receipt names, builtin provenance, core binding, and Nat binding are
checked atomically. The registry deliberately does not add legacy surface
aliases: a current monomorphic `List` can coexist unchanged. It is not yet a
`.ctea` import. A reusable `GraphLibrary` now specializes `ValidPath` to a
checked edge-symbol family and constructs checked path-concatenation theorems
over the shared list package. That specialization boundary is deliberate:
concrete `Vertex` paths remain `fol+induction`, while passing the edge predicate
as a value—or instantiating paths at `Prop`—is certified `hol`. The graph spike
uses the extracted package without changing its receipt. See
[`hol/H6_LIBRARY_MIGRATION.md`](hol/H6_LIBRARY_MIGRATION.md) for the remaining
surface, compatibility-alias, and curriculum slices. A reusable
`FiniteEnumerationLibrary` now defines `HasCard` and generates checked
no-duplicate, length, and coverage evidence for any parameterless nullary
datatype. The three-constructor test and refactored Color/Bit spike remain
trust-free and fragment-precise. The finite-enumeration checkpoint artifacts
are 3,510,136 bytes natively and 1,349,499 bytes in Wasm, below the 1.5 MB
review line.

- Introduce parameterized `List A`, finite enumeration, generic relation and
  graph libraries. The checked list substrate and versioned production-facing
  registry, a symbol-specialized graph/path substrate, and the checked
  cardinality-transport package and registry record plus finite-enumeration
  evidence generation are implemented; finite-package registration and surface
  imports remain.
- Keep compatibility aliases for current monomorphic course names during one
  release cycle.
- Add course chapters only after representative theorem targets pass: path
  concatenation, pigeonhole, finite union cardinality, handshake, and a finite
  tree edge/vertex theorem.
- Retain explicit path witnesses in FOL exercises even though HOL libraries can
  express closures more abstractly.

Exit gate: a pilot discrete-math sequence can enforce its logical profile per
assignment, and students can complete it without encountering internal HOL
machinery in FOL units.

### Phase H7 — cutover or coexistence

After a pilot, choose one:

- replace the old kernel once semantic and performance parity is demonstrated;
- keep the FOL checker as a small independent engine if it remains materially
  easier to audit or produces better countermodels;
- abandon the HOL migration if the stronger core increases complexity without
  improving the curriculum examples.

Deletion of the old engine is a final phase, never a prerequisite for the spike.

## Verification strategy

### Kernel tests

- typing preservation for substitution and beta reduction;
- alpha-renaming and capture avoidance under nested binders;
- rejection of malformed applications and equality across types;
- constructive/classical separation;
- no `DraftProof` conversion with holes;
- constructor disjointness, injectivity, exhaustiveness, and induction;
- strict positivity and recursive-call structural decrease;
- explicit tests that extensionality and choice are unavailable unless supplied.

Where practical, use small generators to test substitution composition,
renaming, and normalization idempotence. Generated tests supplement, rather than
replace, readable adversarial examples.

### Fragment tests

- equivalent surface spellings receive the same least fragment;
- lambdas eliminated during elaboration do not spuriously taint FOL statements;
- lambda or predicate values retained in checked evidence do taint proofs;
- transitive imports cannot hide HOL, classical, choice, or axiom use;
- theorem signature freezing compares canonical core statements, not source
  formatting.

### Compatibility tests

- dual-run every current `.ctea` file;
- compare declaration status and receipts, not only process exit codes;
- retain the executable book-output contract;
- compare goal snapshots for representative tactics;
- run native and Wasm builds at every migration gate.

## Risks and controls

| Risk | Control |
|---|---|
| A “HOL mode” silently becomes classical | Constructive kernel; explicit classical receipt |
| FOL exercises use imported HOL facts | Transitive proof receipts and import allowlists |
| Definitional equality becomes unbounded computation | Structural recursion only; separate kernel normalization from `simp` |
| Polymorphism makes inference opaque | Rank-1 only; explicit type arguments in diagnostics and fallback syntax |
| Rewrite breaks the existing book | Parallel engine, facade APIs, dual-run corpus gate |
| Trusted core grows with UI features | Enforced module dependency direction |
| Countermodels become misleading | Run only from certified Prop/FOL fragments |
| Function extensionality leaks into computation | Track it as an explicit principle, never definitional equality |
| The project stalls in permanent dual-engine state | Time-box the H3 spike and make H7 an explicit decision |

## Initial implementation sequence

The first work items on this branch should be small reviewable commits:

1. Add golden machine-readable corpus receipts and baseline measurements.
2. Write a module dependency test or CI check for the intended kernel boundary.
3. Extract existing kernel-facing signature access behind a narrow interface.
4. Introduce `CoreType` with first-order and arrow-type classification tests.
5. Introduce typed `CoreTerm`, substitution, and alpha-equivalence tests.
6. Implement the minimal constructive HOL proof checker for hand-built terms.
7. Implement feature receipts and the dependency-union operation independently
   of the parser.
8. Build the three-example H3 spike through a deliberately small elaborator.
9. Produce a short decision report with measured results before beginning H4.

Do not begin by teaching the existing parser every HOL construct. The kernel,
receipt model, and spike must demonstrate the architecture before surface-area
migration starts.

## Definition of success

The re-architecture succeeds when Cetacea can use one auditable logical core to
support generic discrete-mathematics libraries while an instructor can reliably
say, and mechanically enforce, “this exercise uses only constructive FOL plus
induction.” The stronger implementation must reduce incidental encoding burden
without making the stronger logic invisible or unavoidable.
