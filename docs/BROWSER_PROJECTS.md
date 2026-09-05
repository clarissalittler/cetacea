# Browser projects: implementation status

The editor supports single files and multi-file projects. Open **Project files**
to import or download a `.ctea-project` archive, select the active source, or add
and rename files. Autosave and checkpoints retain the complete project. File
switches and changes to dependencies trigger fresh analysis; only the active
source and its reachable imports are certified.

Archives are UTF-8 JSON with `format: "cetacea-project"`, `version: 1`, `root`,
and `files: [{path, source}]`. Unknown fields are rejected, including purported
proof certificates or assignment policies. Archive validation completes before
replacing current work. Downloads preserve all project source files and nested
paths; **Download .ctea** still downloads only the active file. Renaming changes
the path without rewriting import statements.

Project archive files are limited to 50 MiB to accommodate JSON escaping of the
source limits below. Over-limit edits are retained in autosave for recovery,
but checking and project-archive export reject them until repaired. The active
source can still be downloaded separately.

## Shared checker boundary

`cetacea_core::VirtualProject` accepts an active project-relative source path
and a list of `VirtualFile` values. Its `check`, `goals_at`, `run_tactic`, and
`explain` methods use the same project context and HOL checking path. Each call
checks the current supplied sources; it does not reuse a prior certification.
Only the active source and its reachable imports are checked. Unrelated project
files are not thereby certified.

Imports resolve relative to the importing file, including the active source's
directory. For example, `lessons/main.ctea` can import `sibling.ctea` from
`lessons/` and `../lib/helper.ctea` from `lib/`. A different `sibling.ctea` at the
project root does not shadow the local sibling. Bundled `std/...` imports and
registered logical packages remain available. Project resolution never reads
host filesystem files.

Project source paths must be unique, relative, slash-separated `.ctea` paths,
without empty, dot, or parent components. `std/` and names containing colons are
reserved. Import statements may use parent components within the project, but
cannot escape its root. Projects are limited to 64 source files, 512 bytes per
path, 1 MiB per source, and 8 MiB of source text in total. These are input limits;
they do not establish an end-to-end checking budget.

Native regression tests exercise nested/sibling imports across all four editor
surfaces, bundled libraries, separation of root and imported theorems, source
changes invalidating a dependency, missing files, cycles, root escapes,
duplicate paths, and oversized sources. Existing native file entry points retain
their filesystem behavior.

## Remaining integration

- Carry assignment manifests into the same project context and compare browser
  enforcement with the native grading path.
  The core now exposes the same bounded manifest parser and teaching-policy
  builder used by the CLI; importing a manifest does not yet grade a project.
- Complete keyboard, accessibility, and classroom workflow verification.

The browser harness exercises nested projects, supporting-file edits that
invalidate the active proof, repair, checkpoint restoration, complete downloads,
invalid archives, autosave reload, file creation, and rename collisions. It uses
isolated storage and rechecks restored files with the real worker and Wasm.

Damaged saved work pauses autosave and exposes any individually valid active
source or checkpoints. **Download saved data** exports the original storage
string in a `cetacea-saved-data` JSON wrapper; its `raw` field preserves even
unpaired UTF-16 code units through JSON escaping. This is a recovery backup,
not a project archive. **Resume autosave with recovered work** writes the current
work and the original data in one storage update. If quota is exhausted, the
original slot is unchanged. The original-data download remains available after
resuming and reloading. Unknown save versions are preserved without guessing
how to interpret their contents. An entirely unreadable storage service cannot
provide a backup until it becomes readable again.

## Worker and WebAssembly transport

The worker accepts method `project` with arguments `[project, operation, options]`.
`project` contains `root` and `files: [{path, source}]`; operations are `check`,
`outline`, `goals`, `tactic`, and `explain`. Options provide `line`/`column`, or
`theorem`/`tacticIndex`, as appropriate. The result uses the same JSON shape as
the corresponding single-source operation. All requests go through the existing
queued worker client, including cancellation, deadlines, and worker recovery.

`web/project-request.mjs` encodes the snapshot for `cetacea_project`. The CTP1
packet contains little-endian u32 values: magic `0x31505443`, operation number
(0 through 4 in the order above), first coordinate/index, second coordinate,
then length-prefixed UTF-8 root and theorem names, a file count, and pairs of
length-prefixed paths and sources. The Rust reader rejects truncated packets,
invalid UTF-8, unknown versions/operations, excessive fields, and trailing data
before analysis. The total wire limit is 9 MiB; project source limits remain
those above. No project state is retained inside the Wasm module between calls.

The browser regression harness exercises all five project operations through
the actual worker and release Wasm build, changes a dependency to invalidate a
proof, and verifies recovery after a duplicate-path request is rejected. The editor workflow checks described above cover the controls separately.

## Concurrent editor saves

The browser serializes autosave and recovery writes with the shared Web Lock
`cetacea.web.autosave`. Inside the lock, it compares the current storage string
with the last version this editor read or wrote. A mismatch pauses this tab's
autosave and preserves its in-memory source, project, and checkpoints. Storage
change notifications also surface conflicts without waiting for another edit.
The other tab's saved work is not replaced. Download the paused tab's file or
project before reloading it; checking and editing remain available.

Rapid edits coalesce while waiting for the lock. The save status distinguishes
pending writes from completed ones, and closing with pending or failed storage
prompts the browser's unsaved-work warning. If browser locking is unavailable,
autosave reports a failure rather than performing an uncoordinated write;
download remains available. This protocol coordinates current Cetacea editors;
older builds or unrelated scripts do not participate in its lock.

The regression harness runs concurrent editor frames with actual Web Locks and
real localStorage under unique temporary keys, forwards their storage events,
and removes those keys afterward. Normal student storage is not modified.
