# Local classroom candidate

This is a locally checked candidate, not a deployment or a claim that the
student-readiness checklist is complete. All source changes remain uncommitted.

- Directory: `target/web-classroom-candidate`
- Build ID: `0f71d1318fb7096efa4b0a98aa0cd94b78eb01dd15fafeafbbfaeb680afb9a5f`
- Manifest: `target/web-classroom-candidate/build.json`
- Toolchain used: Rust 1.95.0
- Checked on: 2026-09-04

The bundle contains its own worker and Wasm, twenty selectable examples, and
build-specific asset URLs. Its thirteen asset hashes match the manifest.
Do not modify the identified bundle in place; create a new output directory
for a later build.

## Launch locally

From the repository root:

```sh
python3 -m http.server --bind 127.0.0.1 --directory target/web-classroom-candidate 8000
```

Open `http://localhost:8000/`. The page displays build `0f71d1318fb7`.
The generated directory is a local build artifact, not a checked-in source
file. Rebuild with `scripts/build_web.py` if it is absent, using a new output
directory and recording the resulting ID; changed inputs can produce a
different candidate.

For Chapter 21, open `docs/book/hol-code/ch21-exercises.ctea` and load
`docs/book/hol-code/ch21.ctea-task` as the assignment. The starter is expected
to fail grading until its four proofs are complete. Chapters 17–20 also have
portable task files in that directory. See each chapter for its proof methods
and exact grading command.

## Verification evidence

The [readiness ledger](STUDENT_READINESS.md) records the full local CI pass:
629 Rust tests, 126 teaching files and their policies, the unchanged frozen
semantic baseline and HOL comparison, feature-disabled core compilation,
workspace linting, JavaScript tests, process-limit tests, packaging tests,
and generated-fixture/example checks.

A separate browser harness imported this candidate's versioned
`checker-client.mjs`, which created the candidate's own worker and loaded its
packaged Wasm. All 57 native/browser grading cases passed in Chrome. These
include the newer chapter assignments, rejected unfinished starters, incorrect
arithmetic/graph/recurrence claims, and the assignment permission/grant cases.
The harness did not read or write student storage. The packaged editor was
also opened directly: it displayed the matching build ID, all twenty example
options, and a certified saved implication proof with goals, explanation,
theorem search, and no diagnostics. The source was not edited during that
inspection. Its local reproduction is
`target/classroom-candidate-parity.html`, served from the repository root; it
compares against `web/tests/assignment-parity.json`.

The full release pass caught and fixed missing `hol-shadow` feature guards
on the graph and matrix source-import handlers. The required core build with
`--no-default-features` now passes.

## Remaining readiness work

The [active checklist](STUDENT_READINESS.md) remains authoritative. Outstanding
work includes complete resource budgets and compact numerals, finite-graph
trees and further counting/probability material, source-package publication
and the HOL API transition, full accessibility/file-selection verification,
hosted update/asset-retention behavior, the owner's licensing decision, and
an actual classroom pilot. Green tests do not establish those outcomes.

No remote CI run, commit, deployment, or distribution to students was performed.

## Buildable checkpoint — 2026-09-05

The later local bundle `target/web-checkpoint-2026-09-05` has build ID
`d64b53958a66184d3054c10bc5ad76271c6abe33ff1c855963e8d7b7f2a82543`.
It includes Chapter 22 and the shared checking budget, including parsing,
legacy validation and countermodel search. The native workspace and release
Wasm build, all 647 workspace tests, seven browser unit-test files, six process
runner tests, five packaging tests, Clippy, formatting and the core build
without default features passed. The 131-file teaching corpus, semantic
baseline and HOL shadow gate passed (13,350 checked declaration occurrences,
589 root theorem receipts, no mismatches). This records a buildable development checkpoint; the earlier
candidate's browser verification does not automatically apply to this bundle.
No deployment or distribution to students accompanies this checkpoint.
