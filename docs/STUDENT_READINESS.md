# Student-readiness work plan

User objective: continue until Cetacea is more usable for a discrete-math
student, addressing the friction points identified in the stocktake and book
ledger. This is the active completion checklist, not a claim of readiness.
Previously resolved ledger entries remain protected by the regression suite.

## Composition and feedback

- [x] Package aliases share type/symbol identity (friction 42); native and
  Wasm-interface tests plus `hol/examples/package_aliases.ctea`.
- [x] Explicit prelude/counting coexistence and atomic import failure (43);
  `hol/examples/prelude_counting.ctea`, rollback and editor regressions.
- [x] Standard-library imports work outside the repository, including grading;
  subprocess tests exercise shipped libraries and explicit manifest identities.
- [x] Deduplicate theorem search while retaining usable alias lookup (42).
  Package exports now reach the browser library from checked receipts; alias
  groups retain searchable spellings without merging distinct declarations.
  Both terminal interfaces now use the same separate, receipt-aware catalog;
  tests cover alias lookup, distinct equal statements, source replacement,
  and failed-import cleanup. The line interface was exercised directly.
- [x] Complete the classroom namespace transition and update course examples (18).
  Migrated 51 teaching sources and their companion chapters; 398 root receipts
  preserve their statements under qualification/renaming and retain status,
  logic mode, fragment, and proof features. See CLASSROOM_NAMESPACE_MIGRATION.md.
- [x] Make computation-induced goal changes understandable in the UI (15).
  Applications preserve written premises; structured computation previews
  appear in browser/terminal goals and browser proof explanations. Tests
  distinguish True, False, unchanged goals, and actual proof completion.
- [x] Report every parsed theorem's result structurally, including failures (44).
  CLI/Wasm theorem_outcomes preserve occurrence locations and distinguish
  failure, incompleteness, skipped work, and import rollback; browser results
  also show failed root declarations. Editor completion and explanations enforce
  final logical-mode checks, so a mode-rejected proof is not shown as complete.
- [x] Support narrowly authorized library-theorem grants in assignments (44).
  ReceiptPolicy now retains dependency provenance and can grant a checked,
  trust-free dependency without erasing receipt facts or waiving root proof
  requirements. Adversarial tests cover unrelated/shared dependencies and
  strong principles. Native manifests now accept exact public logical-package
  and source-library theorem identities, with subprocess checks for alias
  independence, file identity, invalid exports, and root-fragment enforcement.
  The supplied-library pigeonhole client and manifest pass at fol+induction
  with the grant and fail without it; receipts retain the full HOL dependency.
  Browser enforcement is tracked separately below.

## Mathematical proof ergonomics

- [x] Short, checked concrete finite-enumeration derivations, without added
  trust or a higher logical fragment (24).
  `finite` builds bounded proofs from checked library laws and datatype cases.
  The named three-colour example retains a constructive, trust-free
  `fol+induction` receipt; negative enumerations are rejected.
- [x] Goal/occurrence-driven package theorem instantiation in apply/rewrite (25).
  Rewrite occurrences, projected apply, partial explicit arguments, empty-tail
  typing, and named function parameters are checked in `inferred_rewrite.ctea`.
  Chapter 13 examples and solutions now use the shorter proof forms.
  Explicit concrete predicates and typed lambdas now infer theorem type
  parameters before definition normalization. The road example needs only
  `E := Road`; positive mixed-type and conflicting-type regressions protect
  that inference without overriding explicit type arguments.
  Rewrite matching now carries inferred element types into empty-constructor
  patterns: `rewrite -> L.append_nil_right` works without redundant type
  arguments in the Chapter 17 example. Goal, hypothesis, simplification and
  mismatched-type/content regressions cover the shared matcher.
- [x] Term abbreviations work with unfold, simp, and rewriting (26).
  Explicit named tactics, automatic rewrite matching, both directions, all
  occurrences, and named hypotheses have dual-kernel examples. Tests also cover
  imported names, binder capture, saved evidence, and visible proof states.
- [x] Revert term variables with the necessary dependent context (31).
  Dependent hypotheses move into the universal goal; independent facts remain.
  Tests cover rewritten evidence, reuse of names without capture, and the
  counting inclusion proof with its container generalized before induction.
- [x] Rewrite equalities in named hypotheses (31).
  Both directions and rewrite-all retain checked evidence; tests cover package
  computation, saved hypotheses, invalid targets, and binder capture.
- [x] Multiline definitions and projected-proof application work naturally (35);
  physical error locations and adverse proof arguments are regression-tested.
- [x] Positive pigeonhole collision witness API with explicit constructive
  data or explicitly tracked classical reasoning (32).
  The separate classical source library exports `pigeonhole_collision`; the
  constructive base is unchanged. Examples, mode-rejection tests, and a native
  assignment policy verify that classical use remains explicit and enforced.
- [x] Replay arithmetic simplification beneath unused existential binders.
  The zero-modulus proof in Chapter 20 exposed a teaching/HOL mismatch.
  Arithmetic replay now collects binder-independent subterms in the surrounding
  context. Outward shifts reject escaping references and capture beneath nested
  binders. Positive certification and false-conclusion tests cover the source
  proof; scope tests cover the shifting boundary.
- [ ] Checked source-library publication without hand-translating proofs to
  Rust (34).

## Reliability and classroom workflow

- [x] Bounded parsing returns JSON diagnostics for oversized input.
- [ ] Complete end-to-end checking budgets and compact large Nat literals.
  Successor-chain normalization is iterative in the teaching checker; kernel
  application/lambda normalization uses guarded heap continuations. This fixes
  the checked 99-valued contribution example and its invalid-proof diagnostic,
  without claiming compact numeral storage or whole-check budgets.
  Application continuations now release the replaced redex's depth guard before
  its next reduction and handle opaque constructor chains iteratively. Existing
  runaway/depth checks remain active. Native and browser regressions cover
  `27*27 = 729` and rejection of 728. Structural recursion now directly
  substitutes checked arm arguments, avoiding repeated normalization of
  administrative lambdas. The formerly failing modular-square proof certifies
  within unchanged limits, with valid/invalid native and browser grading cases.
  Its browser stack regression is addressed by iterative term cloning and
  constant-spine traversals for normalization, shifting, substitution and type
  inference. Domain checks and binder-scope checks remain enforced.
  Unary representation and whole-check budgets remain open.
  Native corpus, assignment, semantic baseline and HOL shadow gates now run each checker in a process group
  with wall-time, address-space and combined-output limits. Six runner tests
  cover timeouts, pipe flooding, descendants and allocation denial. In-process
  budgets now include a shared 250,000,000-operation allowance for declaration
  dispatch, tactics, proof-node inference, HOL term traversal and normalization.
  Nested checks/imports cannot refresh it, failed imports cannot refund it, and
  exhaustion leaves later declarations unchecked. Six regressions cover these
  boundaries and a fresh allowance after return/unwind.
  Countermodel collection, candidate search and formula/term evaluation now
  share that allowance too. Four further regressions verify that interrupted
  searches return unknown, never invent a falsifying assignment, and retain the
  original proof error. Interrupted quantifiers restore their temporary variable
  assignments, including shadowed values. Legacy name resolution, validation,
  unfolding and environment-aware normalization now charge the same budget;
  two more regressions cover stopping/recovery and iterative numeral visits.
  Source/expression bytes and parser recursion also consume the allowance,
  with buffer entry points retaining it through checking. Three parsing
  regressions cover diagnostic failures and recovery; the path-aware resource
  error is preserved in the diagnostic notes under its contextual message.
  Remaining unmetered walks (including context-free simplification,
  substitution and alpha-equivalence),
  parsing/allocation and compact literals remain open; see CHECKING_LIMITS.md.
- [x] Browser worker isolation, cancellation, recovery, and stale-result handling.
  Four lifecycle unit tests and the real-editor browser harness cover busy-worker
  cancellation, ten-second timeout, worker exceptions, retry, source preservation,
  stale certification, replacement edits, and current explanations. Verified in
  Chrome using `web/tests/browser-recovery.html` on 2026-09-04.
- [x] Browser assignment enforcement agrees with native enforcement.
  The parser and teaching-policy construction are now shared in
  cetacea_core::assignment and used by the CLI. Manifest byte limits and
  independent permission controls have core regressions. The CLI also uses shared
  grant validation, imported-axiom checks, required root signatures and receipt
  restrictions. VirtualAssignment now owns pinned trusted libraries, rejects
  student collisions, resolves imports/grants and combines kernel and policy
  acceptance. Seven existing classroom cases match native grading outcomes and
  violation categories. Assignment-aware worker/Wasm transport now covers all
  five analysis operations, with separate certification and assignment outcomes.
  Browser regressions cover signatures, pinned-library substitutions and recovery.
  Separate task import and editor feedback controls are implemented. Assignment
  selections now persist with work and checkpoints and are rechecked on reload.
  Thirty-one cases compare fresh native grading with the actual browser worker,
  including classroom manifests, rejected grants/signatures/imports, independent
  permissions and transitive dependencies. Student substitutions are rejected
  by the editor harness. Reserved extensionality/choice flags have no source
  producer; shared receipt tests verify their permissions and profile limits.
  See BROWSER_ASSIGNMENTS.md for the scope and future-feature regression gate.
- [x] Student file/project import, export, and persistence with recovery.
  Single-file UTF-8 open/download, named autosave, and ten recovery checkpoints
  are implemented. Replacements preserve the previous source; quota failures
  remain visible and damaged saved data is not overwritten. Unit/browser
  coverage includes restore, file round-trip, invalid input, and storage failure.
  Multi-file archive import/export, active-file selection, creation/rename,
  project autosave and full-project checkpoints are now connected through the
  shared VirtualProject core and worker/Wasm transport. Browser checks exercise
  dependency edits, invalid archives, restoration and reload. Damaged saves now
  expose intact checkpoints, export original data and resume autosave with an
  atomic write preserving that original. Shared browser locks serialize saves;
  stale tabs pause autosave while retaining their drafts. Verified with 36
  JavaScript unit tests and 25 browser checks, including concurrent editors
  using isolated real localStorage and actual Web Locks. See BROWSER_PROJECTS.md.
- [ ] Actual browser keyboard/accessibility and assignment-flow verification.
  Initial Chrome keyboard checks verify source/proof-state skip links and Tab
  escape from the editor; search labeling and focus styles are corrected.
  Long-name selector overflow is fixed and exercised at narrow/tablet/desktop
  widths. A failing-proof-to-correction workflow now passes with actual keyboard
  navigation at 320 pixels, as do theorem search and insertion. Assignment
  clearing and checkpoint recovery now pass with actual keyboard navigation
  at 320 pixels; focus loss on the disabled clear control and embedded
  skip-link navigation are fixed. Keyboard file selection was blocked by
  Chrome extension file access; complete import and screen-reader
  checks remain open. See
  BROWSER_ACCESSIBILITY.md.
- [ ] Identifiable, versioned distribution; deployment gated on passing checks.
  A reproducible self-contained web bundle now includes a visible content ID,
  build-specific asset directories and a hash manifest; its packaged worker/Wasm was verified
  in Chrome. CI builds it after existing checks; Pages now requires the same
  reusable CI workflow. Local bundles can now retain verified previous assets;
  both retained and current checkers passed all 57 grading cases in Chrome
  from one combined bundle. A repeatable cache-disabled local update test also
  passed all 57 cases before switching bundles, through the still-loaded old
  client with a fresh worker afterward, and through the new client (171 checks);
  server records verified post-update worker/Wasm fetches for both builds.
  The packaged editor also preserved an unsaved single-file draft through a
  local update with injected storage failure, exported its exact contents,
  recovered saving, and restored/certified it in the new editor. Storage was
  isolated in memory; real disk persistence and hosted behavior were not tested.
  Automatic Pages retention, remote execution and
  a hosted open-tab update remain unverified; see WEB_DISTRIBUTION.md.
- [ ] Published licensing decision (requires the owner's choice of license).
- [x] Reconciled current status and limitations rather than contradictory roadmaps.
  ROADMAP.md and the original gap/HOL plans now distinguish historical proposals
  and counts from this active checklist. The implementation guide describes
  default HOL checking, compatibility API limits, virtual assignments/projects,
  worker execution and current recursion/reversion support. CS250 limitations
  distinguish its monomorphic tutorial library from polymorphic logical packages.
  The July audit dispositions now record completed grants, declaration outcomes
  and alias search. Local links in all six reviewed guides were verified.

## Architecture and curricular integration from the stocktake

- [ ] Narrow, authoritative HOL API and signature ownership; retire legacy
  verdict dependencies as their callers migrate, preserving adversarial tests.
- [x] Finite sums and constructive overlapping-union enumeration.
  The bundled `std/hol/sums.ctea` now provides natural-list sums and checked
  empty, cons and concatenation laws, with independent-alias consumer examples.
  Two core regressions check virtual imports, constructive restricted receipts
  and rejected false totals; a Wasm-interface regression checks the bundled
  import path. The release Wasm build passes with the new library.
  See FINITE_SUMS.md. The bundled `finite_union.ctea` now constructs an
  existential duplicate-free union witness from explicit membership decisions
  and derives its set-relative size bound. Core and Wasm regressions cover
  concrete overlap, restricted constructive receipts and rejected bad proofs.
  This is checked witness construction, not an executable list-valued union
  function or a general equality decision procedure; see CONSTRUCTIVE_UNIONS.md.
  `member_decidable` now derives decisions for arbitrary lists from explicit
  decidable equality. List-union and set-size wrappers reuse that premise;
  the colour example proves it once and handles arbitrary colour lists.
  The bundled `nat_decidable.ctea` supplies that premise for natural numbers,
  with checked numeric list/set clients and rejected misuse of either branch.
- [x] Public path concatenation and handshake-lemma unit.
  `std/hol/reachability.ctea` provides a checked closed-set reachability API,
  composition and invariant/exclusion laws, with a directed-road consumer.
  Virtual-project and Wasm-interface tests cover imports and adverse uses.
  `std/hol/graph@1` now exposes explicit paths and checked endpoint equations.
  The bundled `paths.ctea` proves concatenation by list induction through that
  public interface; a directed-road client joins paths across package aliases.
  Core and Wasm tests cover the client and core tests reject reversed paths,
  wrong finishes and mismatched composition. Generic concatenation requires
  the `hol` profile. Chapter 18 now supplies exercises, solutions, deliberate mistakes and a
  matching native/browser assignment. Chapter 19 now supplies the handshake teaching unit;
  see REACHABILITY.md for the precise boundary. Explicit empty-list arguments
  now use types supplied by later relation/type arguments.
  A checked three-vertex multigraph example now computes incidences and degrees
  and proves the handshake identity for arbitrary edge lists, including loops
  and parallel edges. Weighted sums now require contribution facts only on listed elements, and
  finite-set wrappers consume checked `HasSize` evidence. These support the
  next generalization. Checked weighted removal and enumeration-independence
  proofs now show that reordering a duplicate-free finite-set enumeration
  preserves its total. Generic endpoint-support laws now prove that an edge
  contributes two over any duplicate-free vertex list containing both endpoints,
  including loops. The `std/hol/matrix@1` package now exposes checked row/column sums and
  eight computation laws. The bundled `double_counting.ctea` proves equality
  of both totals for arbitrary index types and lists by constructive induction.
  A workshop example checks rectangular tables and shared List aliases;
  adverse tests reject false totals, swapped types, and lost multiplicities.
  The bundled `handshake.ctea` now connects arbitrary binary incidences and
  named degrees: per-edge contribution 2 and checked column degrees imply the
  degree sum is twice the edge-list length. Its row bridge connects endpoint
  proofs to the incidence interface. A loop/parallel-edge client and rejected
  incorrect degrees are covered in core, Wasm, and browser grading. Chapter 19 supplies the teaching
  chapter, four exercises and solutions, three rejected mistakes, exact-signature
  assignment policy, portable browser task, and example-selector entry;
  see DEGREE_COUNTING.md for the exact scope.
- [ ] Distinguish structural-tree exercises from the finite-graph tree theorem;
  provide the latter through the public graph library.
- [ ] Arithmetic/number-theory, recurrence, and further counting units with
  checked end-of-unit proofs, exercises, solutions, negatives, and policies.
  Chapter 17 now supplies the finite-sum unit: examples, four exercises and
  solutions, three intended negatives, a restricted assignment policy and a
  browser task archive. Native/browser parity covers accepted solutions and
  the rejected unfinished starter; task contents are checked against the
  native policy. The 100-file corpus gate passes, and solutions plus policy
  also pass from a temporary directory outside the repository. All 33 grading
  parity cases passed in Chrome; browser unit tests and generated-example
  verification pass. Chapter 20 now supplies divisibility and modular arithmetic:
  witness proofs, common-divisor linear combinations, congruence of polynomial
  values, and the zero-modulus case. Four exercises and solutions, three
  deliberate mistakes, a restricted assignment and browser task accompany it.
  The bundled `recurrences.ctea` now proves uniqueness for arbitrary state
  types and the constant-step closed form. Token-counting and two-state-machine
  clients are checked, with rejected wrong initial values/update rules and
  incompatible function arguments. Named monomorphic `def` functions now work
  as theorem function arguments alongside `func` and `defrec` declarations.
  Chapter 21 now supplies recurrence exercises, solutions, deliberate mistakes,
  and a restricted native/browser assignment. Chapter 22 now supplies finite
  uniform probability through checked natural-number event counts and
  expectation numerators. The bundled `probability_counts.ctea` proves the
  complement identity, numerator linearity, constant totals and nonzero length
  for nonempty lists. Coin/ticket examples distinguish duplicate occurrences;
  regressions reject false totals, lost tickets, missing complement evidence
  and an empty denominator. Four exercises, solutions, deliberate mistakes,
  an exact-signature policy and portable browser task accompany the chapter.
  Rational arithmetic, nonuniform measures, conditional probability and further
  counting units remain open; see RECURRENCES.md and
  [Chapter 22](book/22-finite-probability.md).
  Chapter 22 validation: all 131 teaching files passed the corpus gate;
  572 core and 27 Wasm tests passed, as did workspace Clippy and formatting.
  All 61 native/browser grading cases passed in Chrome using release Wasm,
  including accepted Chapter 22 solutions, rejected unfinished exercises and
  a rejected lost-ticket count. Its assignment passed outside the repository;
  all four starter holes, task/policy identity, chapter links and 21 generated
  browser examples were checked. The earlier immutable classroom candidate
  predates this chapter and has not been replaced or deployed.
- [ ] Evaluate student usability with a concrete class/pilot workflow; code
  tests alone do not establish classroom outcomes.

Each implementation step must preserve prior work, add meaningful positive and
adversarial checks where semantics change, and update the relevant ledger.
Before completion, audit this checklist against current artifacts and actual
execution. Missing evidence remains incomplete. Licensing and classroom
outcomes must not be invented or inferred from green tests.

## Latest local release validation (2026-09-04)

The full local CI command sequence passed after Chapters 19–21 and the
normalization/function-argument changes. This pass found and fixed missing
`hol-shadow` feature guards on the graph and matrix import handlers.

- Formatting, workspace Clippy with warnings denied, and seven JavaScript test files.
- 629 Rust tests: 25 CLI, 8 CLI integration, 570 core, and 26 Wasm.
- Core build without default features and release Wasm build.
- 126 teaching-corpus files, including every chapter assignment policy.
- Unchanged frozen semantic baseline: 74 files, 589 root declarations, and
  38 negative theorems. The HOL comparison checked all 13,350 declaration
  occurrences with no mismatches.
- Kernel-boundary check across eight Rust modules.
- Fresh native comparison for 57 browser assignment fixtures; 20 bundled
  browser examples verified against their sources.
- Six process-runner tests and two reproducible-packaging tests.
- Identified candidate at `target/web-classroom-candidate`, build
  `0f71d1318fb7096efa4b0a98aa0cd94b78eb01dd15fafeafbbfaeb680afb9a5f`; all 13 packaged asset hashes verified.

The frozen baseline is separate from the growing teaching corpus; its counts
do not describe all current teaching files. The packaged-browser verification
is recorded in CLASSROOM_CANDIDATE.md. Earlier browser accessibility/recovery
checks retain the scope described above; they were not rerun by these Rust and
corpus gates. No remote CI run or deployment was triggered. Unchecked readiness
items remain open, including licensing, actual classroom outcomes, complete
resource budgets, and hosted update behavior.
