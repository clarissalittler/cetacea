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

Decision: **conditional go for a bounded H3.5 bridge; H4 is not yet
authorized.** See [`hol/H3_DECISION_REPORT.md`](hol/H3_DECISION_REPORT.md) for
the executable examples, measurements, gate assessment, and current H3.5
progress.

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
no trust. It is intentionally a concrete transport instance; turning it into a
reusable theorem over arbitrary stored bijections remains an H3.5 deliverable.
H3.5 now adds stable
checked theorem IDs, explicit type-instantiated theorem references, schematic
type-scope validation, and transitive theorem/structural-definition receipts
derived from statements and hole-free evidence. The three examples have been
migrated off caller-authored dependencies. The generic cardinality theorem,
linked Wasm measurement, and mechanical compatibility lowering map remain.

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

- Lower existing `sort`, `const`, `func`, `pred`, `def`, theorem parameters,
  formulas, predicate lambdas, and proof expressions into the new core.
- Preserve existing name resolution and import behavior through stable
  declaration identities.
- Elaborate old monomorphic datatypes as zero-parameter inductive types.
- Preserve the current tactic language by changing its generated evidence, not
  rewriting course scripts.

Exit gate: all existing positive files check in both engines with matching
statuses, modes, axiom/incomplete dependencies, and theorem statements. Every
negative theorem remains rejected individually.

### Phase H5 — fragment enforcement and assignment manifests

Status: the parser-independent foundation now exists: least-statement
classification, direct/transitive dependency sets, feature union, required
fragment calculation, trust/incompleteness propagation, and profile policy
checks. H5 still owns integration with theorem elaboration, import provenance,
manifests, result formats, UI, and countermodel eligibility.

- Implement least-fragment classification and transitive feature receipts.
- Extend text, JSON, Wasm JSON, TUI, and browser results.
- Add allowed-import and frozen-signature policies.
- Ensure model search consumes the certified fragment, not an ad hoc syntax
  guess.

Exit gate: adversarial tests demonstrate that a syntactically FOL theorem proved
through HOL, choice, extensionality, classical reasoning, or an unallowed import
is rejected by the corresponding course policy.

### Phase H6 — library and curriculum migration

- Introduce parameterized `List A`, finite enumeration, generic relation and
  graph libraries.
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
