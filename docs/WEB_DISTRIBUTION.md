# Identified web distribution

Build a self-contained directory with:

```sh
python3 scripts/build_web.py --output target/web-distribution
```

The command builds the release Wasm, copies the editor assets and their modules,
and writes `build.json`. It refuses an existing output directory; choose a new
one for each build. It prepares a staging directory before exposing the completed
output. Nothing is deployed or published by this command.

The build ID hashes the builder, all input frontend assets and the Wasm bytes.
Assets live under `assets/<full-build-id>/`; the root page references that
directory. Module imports, the worker and the Wasm remain within it. Every
local asset reference also receives the build ID as its cache version. The editor displays its first twelve digits;
`build.json` contains the full ID and SHA-256 hashes of every output asset.
Identical inputs and retained bundles produce identical output files. The bundled worker uses only
its packaged Wasm, with no fallback into `target/` or another installation.

Serve the output directory over HTTP on localhost for local use:

```sh
python3 -m http.server --bind 127.0.0.1 --directory target/web-distribution 8000
```

Then open `http://localhost:8000/`. The Web Locks used by autosave require a
secure context, which localhost provides. Hosted classroom copies need HTTPS.
Keep published build directories immutable and use a new directory/URL for a
new build, so existing pages can still fetch their matching assets. Do not
replace the files beneath an already published build directory. If a host
removes old asset directories, an old page can encounter a missing-file error
but cannot load a newer worker under its old URL. Retain previous asset
directories to support already-open pages through updates. The current Pages
workflow does not yet implement that retention.

For a local update, carry assets forward explicitly:

```sh
python3 scripts/build_web.py --output target/web-next \
  --retain-from target/web-classroom-candidate
```

`--retain-from` is repeatable. It copies only manifest-listed assets, verifies
their SHA-256 hashes, and rejects unsafe paths, symlinks, missing files and
conflicting bytes. It verifies the old root page but does not copy it: the new
root page always references the current build. The output manifest covers both
current and retained assets. Passing that output to the next update carries
its retained assets forward too. Retention does not change the current build
ID; the manifest records the additional files. Hashes check integrity against
the supplied manifest, not authenticity; use trusted local bundles.

Nothing is pruned automatically, so retained bundles grow over time. Choose
which earlier bundles to include according to the period you intend to support
open tabs. Keeping asset directories at the same hosted paths is necessary;
this command alone does not implement retrieval or deployment on Pages.

CI runs packaging tests and builds this directory only after its existing Rust,
JavaScript, corpus, kernel-boundary and generated-fixture checks pass. Local
packaging alone does not assert that those tests were run; run the CI checks
before distributing a local build. The Pages workflow now calls the same CI workflow and requires its success
before packaging and uploading the site. These workflow changes have not been
executed on GitHub in this session. Keeping old build directories available
during site updates remains a deployment concern. The manifest identifies contents, not a signed
release or a licensing decision.

On 2026-09-04 a generated bundle was served from `target/web-preview` and opened
in Chrome. Its visible build ID matched its manifest, and its own worker/Wasm
certified the saved source and displayed goals, explanations and theorem search.
Packaging tests cover deterministic output, changed-input IDs, versioned module
and worker URLs, removal of the development Wasm fallback, and preservation of
existing output directories. Build-specific asset paths are also tested: an old
build path does not exist in a newer bundle unless explicitly retained. The addressed bundle was opened
and certified source in Chrome as build `7546098f9867`.


If checker files cannot be loaded, the editor tells students to download their
source or project before reloading. Unexpected worker failures also include this
fallback after retry. Source editing and downloads remain available. The browser
recovery harness loads the real worker with Wasm fetches returning 404, verifies
the guidance and preserved controls, then restores normal loading and certifies
the retained source. This checks recovery behavior; it does not replace hosted
retention of previous builds or verification of the remote Pages workflow.

The latest locally verified classroom bundle and its exact build ID are recorded
in [CLASSROOM_CANDIDATE.md](CLASSROOM_CANDIDATE.md). That candidate passed all
57 grading cases using its own packaged worker and Wasm in Chrome, after the
full local release gates passed. This supersedes the older bundle IDs above as
the latest full release-gate verification; it does not claim a hosted deployment.

A later retention check built `target/web-retention-preview` as
`bebb869f0442657250673468ae1ec17d91b199ed38977592367946a60ba9f15e`, retaining
the classroom candidate's assets. All 25 manifest hashes matched, and all old
assets were byte-identical to the candidate. Chrome ran all 57 grading cases
successfully through each of the old and new packaged clients, workers and
Wasm files served from this combined directory. The five packaging tests also
cover retention across two updates, duplicate retention, ignored unlisted
files, and atomic failure for corrupt, missing, unsafe or conflicting assets.
This verifies local availability of both builds; an actual open-tab transition
on the hosted site and remote CI remain unverified.

## Repeatable open-page update check

With two distinct bundles, where the second retains the first, run:

```sh
python3 scripts/serve_bundle_update_test.py \
  --old target/web-classroom-candidate \
  --new target/web-retention-preview
```

Open `http://localhost:8766/__bundle-test__/` in a browser. The server binds only
to loopback, verifies the bundles before serving, disables caching, and switches
its served directory in memory when the test requests an update. It does not
change either bundle or publish anything. Restart the server to repeat the test;
`--port` selects a different local port.

The harness keeps the original packaged client loaded in an open page. It runs
all grading fixtures, terminates that client's worker, switches the server to
the new bundle, checks that the root page now references the new build, and runs
the fixtures again through a fresh worker created by the original client. It
then checks the new packaged client too. Server request records must show fresh
post-update worker and Wasm requests under both build IDs. The test never reads
or writes student storage and does not replace production client or worker code.

On 2026-09-04 Chrome passed all three sets of 57 cases (171 checks) and both
network-request assertions with the bundles above. This establishes a local
open-page checker transition with uncached asset loads. It does not test a
remote host's cache policy or the Pages workflow's retrieval of previous
bundles. Those remain separate checks before claiming hosted update support.

For the editor lifecycle test, restart the same server and open
`http://localhost:8766/__bundle-test__/editor` instead. This harness loads the
real packaged editor in an iframe and substitutes isolated in-memory storage;
production source editing, saving, rendering, downloads and checking code run
unchanged. It deliberately fails storage writes, verifies an unsaved draft,
switches bundles without reloading the editor, and edits again to force a fresh
worker. The download Blob must match the draft exactly (the harness suppresses
the actual browser download). It then restores storage writes, saves a
checkpoint, loads the new editor and verifies that the draft is restored and
HOL-certified. Server records must show post-update worker and Wasm requests
under both build IDs.

On 2026-09-04 this editor test passed in Chrome with the same two bundles above.
It covers a single-file draft and storage failure/recovery across a local
update; it does not establish real disk persistence, file-picker behavior,
multi-tab conflict behavior during an update, or a hosted deployment.
