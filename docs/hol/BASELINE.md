# Pre-HOL Baseline

This report fixes the observable starting point for the `hol` branch. The
machine-readable oracle is [`fol-baseline.json`](fol-baseline.json); it is
generated and verified by [`scripts/hol_baseline.py`](../../scripts/hol_baseline.py).

## Semantic corpus

Baseline commit: `52736d878942ff7aceeb42be8a739919f6ad5efd`

| Measurement | Value |
|---|---:|
| `.ctea` files | 74 |
| Expected-positive files | 61 |
| Expected-negative files | 13 |
| Root declarations retained by the checker | 588 |
| Accepted theorems | 483 |
| Incomplete declarations | 81 |
| Trusted axioms | 24 |
| Individually rejected negative theorems | 38 |
| Recorded diagnostics | 41 |

For every corpus file, the golden receipt records:

- a SHA-256 hash of the source;
- expected process success or failure;
- canonical root theorem statements;
- constructive/classical mode;
- accepted/incomplete/trusted status;
- direct or transitive `sorry` status;
- axiom dependencies;
- diagnostic severity, location, message, and notes;
- every theorem name in an intended-negative fixture.

Imported declaration copies are intentionally omitted. Their effects remain
observable through root receipts and diagnostics, while omitting them keeps the
golden file small enough to review.

Capture an intentional new baseline with:

```sh
python3 scripts/hol_baseline.py capture
```

Verify that the current checker and corpus still match it with:

```sh
python3 scripts/hol_baseline.py check
```

CI runs the verification command. A baseline change must therefore be reviewed
as a semantic change, not accepted as an incidental regenerated artifact.

## HOL shadow gate

The frozen oracle above protects legacy behavior. A separate, opt-in gate
replays every declaration that legacy checking accepted through the HOL
compatibility elaborator and compares theorem status, constructive/classical
use, axiom closure, incompleteness, and fragment receipts. It never changes the
legacy result.

Inspect the current migration frontier without failing on HOL mismatches:

```sh
python3 scripts/hol_shadow.py report
```

Require exact agreement:

```sh
python3 scripts/hol_shadow.py check
```

The current checkpoint reports:

| Shadow measurement | Value |
|---|---:|
| Matching corpus files | 74 / 74 |
| Matching root theorem/axiom receipts | 588 / 588 |
| Matching accepted declaration occurrences, including imports | 9,389 / 9,389 |
| Unique mismatches | 0 |
| `prop` required fragment | 108 |
| `fol` required fragment | 234 |
| `fol+induction` required fragment | 246 |
| Checked / incomplete / trusted root receipts | 483 / 81 / 24 |

`cetacea --hol-shadow [--json] file.ctea` exposes the same per-file report. A
shadow mismatch makes that opt-in CLI invocation fail for use in migration CI;
ordinary CLI and editor checking remain legacy-authoritative. The browser crate
does not expose this migration tool and disables the `hol-shadow` Cargo feature,
so command integration does not pull the sidecar into the Wasm artifact.

## Implementation and artifacts

| Measurement | Value |
|---|---:|
| `cetacea_core/src/lib.rs` | 20,710 lines |
| Rust unit tests | 252 (7 CLI + 245 core) |
| Native release CLI | 2,162,328 bytes |
| Wasm release module | 979,741 bytes |

Artifact sizes are raw filesystem sizes before transport compression or Wasm
optimization. They are comparison signals, not release limits.

## Timing observation

Observed on 2026-07-10 with Linux 6.17 x86-64, an Intel i9-14900HX, 32 logical
CPUs, `rustc 1.95.0`, and `cargo 1.95.0`:

| Warm/incremental operation | Wall time |
|---|---:|
| Workspace tests | 0.73 s |
| Full semantic baseline verification | 3.26 s |
| No-op native release build | 0.03 s |
| Incremental Wasm release build | 6.84 s |

These timings are deliberately not CI assertions: runner load, cache state, and
toolchain changes make exact thresholds misleading. Repeat the same commands on
the same machine when comparing a prototype:

```sh
/usr/bin/time -f '%e' cargo test --workspace
/usr/bin/time -f '%e' python3 scripts/hol_baseline.py check
/usr/bin/time -f '%e' cargo build --workspace --release
/usr/bin/time -f '%e' \
  cargo build -p cetacea_wasm --target wasm32-unknown-unknown --release
stat -c '%n %s bytes' \
  target/release/cetacea_cli \
  target/wasm32-unknown-unknown/release/cetacea_wasm.wasm
```

Cold-build comparisons should use a separate target directory rather than
deleting the developer's normal build cache.
