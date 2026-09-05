# Browser assignment enforcement

Browser assignment grading uses the same enforcement as the native CLI. The native CLI now uses the shared parser
and `TeachingPolicy` in `cetacea_core::assignment`; syntax and basic receipt
permissions must not be reimplemented in JavaScript. Manifests are bounded to
64 KiB, and parser errors expose their line and message separately.

The CLI also delegates grant validation, allowed imported axioms, required root
signatures, and root receipt restrictions to `check_receipt_requirements` in
that module. `ReceiptRequirements` carries resolved grant identities and the
required declarations; `AssignmentViolation` preserves the native diagnostic
categories and messages. Import authorization remains a separate check.
An empty receipt-violation list alone never establishes acceptance: kernel
certification and authorized imports must also succeed.

`VirtualAssignment` now owns an immutable manifest and pinned library sources.
It resolves the manifest's imports and grants relative to its project path,
checks pinned sources without student files in scope, and rejects student paths
that collide with pinned sources. Its `check` method combines the sources,
checks all reachable imports against the manifest, and applies the shared
receipt requirements. `AssignmentResult::accepted` requires error-free checking,
successful HOL replay, and no assignment violations. Worker/Wasm requests now
use this API. The editor can load a separate instructor task archive, clear
its selection, and display assignment outcomes alongside proof certification.

Native-versus-virtual regression coverage compares acceptance and violation
categories for the pigeonhole client and Chapter 13–16 solution policies,
including both restrictive HOL policies. Relative paths into the reserved
`std/` tree resolve to bundled sources in virtual projects; editable files
cannot occupy those paths. Pinned custom libraries retain project-relative
identities, independently of the student's import alias.

## Required trust boundary

A native manifest is trusted instructor input, and authorized source libraries
are loaded from instructor-controlled paths. Browser project files are editable
student input. A browser port must not grant a source theorem merely because an
editable file has the expected path and export name.

Keep the instructor manifest and its pinned source-library contents in a
separate assignment context. Resolve its imports relative to the assignment,
validate the complete trusted dependency set, and reject collisions with student
project paths. Source theorem grants must refer to those pinned, checked
libraries. Bundled standard-library and registered-package identities retain
their existing protected resolution. The project editor must neither modify
these pinned files nor replace them through project import.

Choosing an assignment in the browser provides local feedback against that
assignment. It does not authenticate which assignment an instructor intended;
final grading must use the instructor's original manifest and library contents,
just as the native CLI requires today.

## Verified enforcement boundary

Native/browser comparisons cover current classroom manifests and adversarial
signatures, imports, local axioms, dependency grants and permission switches.
The editor recovery harness separately rejects student substitutions for pinned
libraries across all five analysis operations. Project archives reject policy
and certificate fields; only the separate task import selects an assignment.

Extensionality and choice are reserved features with no current teaching-language
producer. Shared receipt-policy tests verify their independent permissions and
profile restrictions; browser fixtures verify that these flags do not authorize
classical reasoning, new axioms or incomplete proofs. When either principle
becomes available in source programs, add corresponding positive and negative
browser fixtures before publishing that feature.

## Implemented worker transport

The existing `project` worker operation accepts `options.assignment` with
`{path, source, files}`: the manifest path, manifest text, and separately supplied
pinned sources. All five operations (check, outline, goals, tactic, explain)
construct the same validated `VirtualAssignment`. Each request contains its
entire context, so cancellation or worker replacement cannot retain a previous
assignment. Requests use the existing queue and deadline handling.

Assignment checks retain the proof-report fields and add
`assignment: {path, accepted, violations}`. A certified proof with the wrong
required signature returns `hol_certified: true` and `assignment.accepted: false`;
consumers must display both outcomes. Other operations provide proof assistance
in the pinned context; their completion fields do not establish assignment
acceptance.

The CTP2 packet uses magic `0x32505443` and the CTP1 prefix documented in
BROWSER_PROJECTS.md. After student files it appends length-prefixed manifest path
and text, then a pinned-file count and path/source pairs. Manifest text is bounded
to 64 KiB; student and pinned sources together remain bounded to 64 files and
8 MiB. The existing 9 MiB packet limit applies. CTP1 requests remain supported.
Truncation, excessive counts, trailing fields and student/pinned path collisions
are rejected. The release-Wasm browser harness checks all five operations,
required-signature rejection, substitution rejection, and recovery afterward.

## Opening an assignment in the editor

Expand **Assignment**, choose **Open assignment**, and select the instructor's
`.ctea-task` file. Task files are JSON objects with exactly these fields:

```json
{
  "format": "cetacea-assignment",
  "version": 1,
  "path": "lesson/task.ctea-assignment",
  "source": "version = 1\nprofile = 'prop'\nrequired_theorem.answer = 'True'\n",
  "files": []
}
```

`files` contains pinned `{path, source}` library files, using the same relative
paths as the manifest. Bundled libraries do not need copies. The native manifest
text goes in `source` without translating its permissions. The editor validates
it with Rust before replacing the selected assignment. Invalid archives preserve
the current source and selection; changes during loading discard the pending
selection. The archive never replaces student source files.

The selected assignment applies to the active file, including when switching
project files. Assignment satisfaction is displayed separately from HOL
certification, with each policy violation listed. Editing or selecting another
assignment invalidates previous feedback. **Clear assignment** removes its pinned
libraries and rechecks the current work. Project archives cannot install an
assignment or change its pinned sources.

Assignment selection is saved atomically with student work and included in
checkpoints. Reload and checkpoint restoration recheck the saved manifest and
pinned sources. The original task filename appears with its manifest path;
this records the local selection, not authenticated instructor identity.
Replacing or clearing a task checkpoints the previous selection. Invalid saved
contexts pause autosave and preserve the original saved data for recovery.
Project archives continue to contain only student files; importing one retains
the separately selected task. Keep the original instructor task file for use
on another browser or computer. For a runnable bundled-library example, open
`docs/hol/pilot/pigeonhole_client.ctea` and select the adjacent
`pigeonhole_client.ctea-task`.

## Browser/native parity regression

Run `python3 scripts/browser_assignment_parity.py --check` to rebuild the native
CLI and verify that `web/tests/assignment-parity.json` agrees with fresh grading.
Without `--check`, the script regenerates the fixture after asserting each case's
intended acceptance. CI checks freshness. Fixtures contain source and manifest
inputs plus native acceptance, certification and declaration/violation-category
pairs; no absolute checkout or temporary paths are retained.

With the release Wasm and local server available, open
`web/tests/assignment-parity.html`. It sends every fixture through the production
worker and compares all three outcomes. The 31 cases cover the pigeonhole client,
Chapter 13–16 solution policies (including restrictive Chapter 14/15 policies),
wrong signatures, missing declarations, incomplete proofs, new axioms, classical
reasoning, required/forbidden imports and pinned grants whose sources are checked,
axiomatic or incomplete. Additional cases cover failed proofs, local axiom
whitelisting, independently permitted features and transitive imports. All 31
cases passed through Chrome and the release Wasm on 2026-09-04. This page never
accesses student storage.
