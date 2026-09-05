# Project stocktake — 2026-09-04

Scope: local `hol` branch at `bfc169e`. This is an assessment, not an implementation change. Existing untracked `AGENTS.md` was preserved. Remote CI, deployed Pages, actual browser interaction, and classroom use were not verified. This is not an independent soundness audit.

## Implementation follow-up

The first implementation slice now fixes package type/symbol identity across
independent aliases. The checked `hol/examples/package_aliases.ctea` companion
covers seven proofs combining List, finite, cardinality, and counting; native
and Wasm-interface tests exercise it. A second slice documents and checks
prelude/counting coexistence under an explicit alias and makes failed imports
atomic, with one root diagnostic instead of a dependent cascade. Earlier root
declarations and successful imports survive rollback. Standard-library sources
now ship with the checker and support external homework and explicit bundled
manifest identities. Multiline definitions and projected-proof application
are fixed, and parser resource limits replace the known oversized-input hangs
with JSON diagnostics. See [STUDENT_READINESS.md](STUDENT_READINESS.md) for the
remaining completion checklist. The assessment below records pre-change findings.

## Assessment

Cetacea is a substantial teaching prover with an unusually strong executable textbook and regression discipline. It has a credible logic/proof course and the beginnings of a broader discrete-mathematics course. Its main problem is now the distance between features working in curated examples and those features composing predictably in new student work.

The intended destination, inferred from the book, discrete-math audit, and HOL plan, has three parts:

1. Teach students mathematical reasoning without making implementation details dominate the lesson.
2. Certify proofs with a small, reviewable kernel and enforce explicit logic/trust boundaries.
3. Support a substantial discrete-mathematics sequence, including finite mathematics, number theory, and graphs, through usable student and instructor workflows.

The first is substantially implemented but still needs classroom evidence. The second has made a major architectural transition but retains migration debt. The third remains incomplete. These should have separate completion criteria.

## Current evidence

- `cargo test`: 482 passing tests (25 CLI, 451 core, 6 Wasm-interface tests).
- `cargo fmt --all --check`: passes.
- `cargo clippy --workspace --all-targets -- -D warnings`: passes.
- `cargo check -p cetacea_core --no-default-features`: passes.
- Wasm release build: passes; artifact is 1,370,268 bytes.
- `scripts/check_all.sh`: 93 source files pass their expected positive, incomplete, negative, and assignment-policy checks.
- `scripts/hol_baseline.py check`: 74 files, 589 root declarations, 38 negative theorems verified.
- `scripts/hol_shadow.py check`: 74/74 files match, 589/589 root receipts, zero mismatches; 601/601 statement classifications accounted for, including two rejected before classification.
- Kernel dependency-boundary check: eight modules pass. Generated browser examples: all eleven synchronized.

The six Wasm-interface tests run natively under Cargo; they are not browser end-to-end tests. Build and regression success do not establish logical soundness or student usability.

The book has sixteen drafted chapters and executable companions. The first twelve provide the logic/induction spine; the last four address finite enumeration, bijections, pigeonhole, and finite unions. Versioned List/finite/cardinality packages, checked counting/pigeonhole source libraries, assignment manifests, and recursion over imported package datatypes are real implemented capabilities.

## Current failures and their consequences

### 1. Package aliases affect type identity

Reproduced against the current CLI:

```text
import std/hol/list@1 as C
import std/hol/list@1 as F

theorem same_list (xs : C.List Nat) : F.length(xs) = F.length(xs) := by
  refl
```

The statement is rejected because `xs` has type `C.List Nat`, whereas `F.length` expects `F.List A`. Two names for the same package datatype do not compose at the surface.

This is the highest-value mathematical usability fix: separate canonical declaration identity from display aliases throughout surface type checking and elaboration. Grading signatures already canonicalize package references, but that does not repair ordinary type matching. Require direct aliases and transitive imports through counting/finite/cardinality modules to compose; preserve rejection of genuinely different datatypes. Deduplicate theorem search by identity.

### 2. Standard-library imports are fragile

Reproduced:

```text
import std/prelude.ctea
import std/hol/counting.ctea
```

This produces thirteen diagnostics, starting with a `List` alias collision and continuing with unknown predicates inside `counting.ctea`. The prelude's monomorphic List and the package List require an intentional coexistence policy; fixing alias identity alone will not make genuinely different declarations identical.

Define and document the supported import surface, make import failure transactional or suppress dependent cascades, and establish predictable standard-library resolution independent of working directory. Acceptance should include checking the same homework from the repo root, its own directory, and an external assignment directory.

### 3. Grading results are not a complete declaration record

A file with a proved `good : True` and a failed `bad : False` returns only `good` in JSON `theorems[]`. The name and reason for `bad` are embedded in diagnostic prose. This is reproduced, not merely an old audit entry.

Add structured declaration outcomes, with names, spans, statuses, and linked diagnostics. A grader needs to distinguish a failed proof from a missing theorem and a renamed declaration without parsing English. Parser recovery limits should be explicit rather than pretending every malformed declaration can be recovered.

The native manifest interface also lacks per-theorem capability grants: sanctioning a HOL lemma currently raises the assignment's whole profile to HOL. Designing a restricted grant must retain transitive receipt accounting. The grant should authorize a dependency explicitly, never relabel that dependency as first-order.

### 4. Resource limits and browser isolation are incomplete

A theorem statement containing 50,000 nested parentheses did not finish within a five-second external timeout. The process was terminated with exit 124 and no JSON output. This confirms lack of a prompt bounded response; it does not establish that the parser would never terminate.

H7 records fixes for earlier stack crashes and normalization budgets. Those fixes should not be confused with a whole-pipeline resource contract. Bound parser depth/work, return structured limit errors, and test pathological inputs in isolated processes. Native batch grading also needs external time/memory limits.

`web/app.js` directly executes Wasm checks on the main browser thread, including a live check after 500 ms of inactivity. From code inspection, a slow check can block the UI; this was not reproduced in a browser. Move checking to a terminable worker, ignore obsolete responses, and preserve the source on worker restart. Acceptance: an excessive input cannot prevent editing, cancellation, or recovery.

### 5. HOL is authoritative, but the migration is unfinished

The H7 decision is implemented: normal acceptance requires teaching-checker success and HOL certification. This protects against acceptance that HOL cannot replay. It also means a valid HOL proof can still be blocked by limitations in the old elaborator/checker.

`lib.rs` is 28,742 lines including tests. H7 documents mirrored APIs, the legacy kernel dependency, and remaining signature/context hygiene. The boundary script is a useful textual check, not a Rust crate boundary.

Finish this incrementally: clarify and rename the production HOL bundle, enforce ownership/signature consistency, isolate the kernel behind a crate API, migrate callers, and remove the legacy verdict only after goal construction no longer depends on it. Keep substitution, recursion, and instantiation adversarial tests throughout. Do not expand both kernels as new mathematics arrives.

No new proof-soundness failure was found in this stocktake; no comprehensive soundness claim is made.

### 6. Mathematical foundations have not all become usable course libraries

The old claim that package List cannot support user recursion is obsolete: the latest implementation supports it. A graph/path implementation also exists internally in `hol/graph_library.rs`. Neither fact means that the full graph course is available through the student surface.

Remaining curricular deliverables include constructive overlap handling for finite sets, useful finite sums, graph degree/counting, public paths and reachability, number theory, sequences/recurrences, and eventually probability. User-declared polymorphic datatypes remain narrower than the kernel's package capabilities.

The source-to-versioned-package publication path is another bottleneck: checked teaching proofs should graduate into reusable packages without being manually rewritten as Rust proof constructors.

### 7. Release and classroom workflow lag the mathematics

Manifests remain native CLI only. The browser is a single-buffer editor with localStorage, rather than a multi-file assignment workspace. There are no local Git tags and no license file in this checkout. These observations do not establish the state of remote releases.

Pages deploys on pushes to `main`, while this assessment is of `hol`. Its workflow builds and deploys independently of the CI test job. Consequently a local green branch is not evidence that students receive this version, or that deployment waits for the full gate.

Before a classroom pilot, provide a versioned distribution, explicit licensing, an identifiable browser build, file import/export, assignment-policy parity where grading happens, and deployment tied to successful checks. Validate keyboard navigation, recovery, and accessibility in the actual browser.

### 8. Planning documents mix historical and current states

README and the HOL plan still describe an architectural experiment although H7 chose HOL. `OUTLINE.md` opens with fourteen chapters but lists sixteen. The discrete-math audit still lists completed induction/generalization or polymorphic-list work as gaps, and old friction entries retain superseded crash descriptions.

One particularly concrete mismatch: friction item 41 claims a sum-over-append induction theorem is demonstrated by `list_fold_sum.ctea`; that fixture and its test currently contain `sum_two`, `sum_cons`, and `sum_nil_right`. The stronger claim needs its own checked fixture or corrected wording.

Keep the old audits as history, but give the project one current status page with links to executable acceptance examples. Count a feature as complete at its usable course surface, not merely when its kernel representation exists.

## Recommended sequence and exit criteria

| Stage | Work | Evidence required to finish |
|---|---|---|
| 1. Stabilize composition | Canonical package identity, import coexistence/resolution, concise import errors | Mix chapters 13–16 under independent aliases and import routes; new proofs check without namespace workarounds |
| 2. Make a dependable pilot | Structured outcomes, parser limits, worker isolation, shared assignment policy, pinned distribution | A student opens, edits, saves, submits, and recovers work; instructor receives complete and policy-correct results |
| 3. Finish the trust transition | Narrow kernel API/crate, signature ownership, retire legacy verdict dependencies | Existing corpus retains statuses, adversarial probes pass, and one authoritative certification API serves every frontend |
| 4. Prove the next mathematical unit | Checked finite sums, decidable membership/equality, overlapping union construction, public graph surface | Source-level proofs of sum-over-append, union enumeration, path concatenation, and handshake using public libraries |
| 5. Extend to the full sequence | Graph tree theorem, arithmetic, number theory, recurrences, counting, optional probability | Each unit has a representative theorem, explanation, starter, solution, negative examples, and assignment policy |

Stages 1 and 2 can support an early logic-course pilot; that pilot need not wait for all graph theory or number theory. Kernel work should proceed in bounded steps alongside the next curriculum slice, not become an indefinite rewrite.

Distinguish an easy structural-tree counting exercise from the finite-graph theorem that a connected acyclic graph has one fewer edge than vertices. The latter is the meaningful graph-library integration target. Similarly, an internal Rust proof of path concatenation is not the same milestone as a student writing it through the public language.

The next development target should be: **an instructor can combine the existing finite-math libraries into a fresh, graded assignment without alias workarounds, opaque failures, or an unresponsive editor.** That directly strengthens the current project and prepares the next mathematical units.
