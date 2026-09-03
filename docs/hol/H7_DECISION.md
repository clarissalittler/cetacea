# H7 Decision — the HOL core is the kernel

Date: 2026-09-03. Branch: `hol`.

## Decision

The HOL core (`crates/cetacea_core/src/hol/`) is Cetacea's kernel. The legacy
checker in `crates/cetacea_core/src/lib.rs` is the elaborator: it parses,
runs tactics, produces goals, diagnostics and countermodels, and is not
trusted. A declaration is accepted only when the legacy checker accepts it
*and* the HOL replay certifies it. That is what the browser build already
did; as of this decision the native CLI and its editor modes do the same by
default.

Of the three options the plan listed for H7 (replace, coexist, abandon), this
is "replace" — but framed so that the founding invariant, *tactics are
untrusted and the kernel is trusted*, is realized by the engine that is
already small and boundary-linted rather than by extracting a kernel from the
27k-line legacy file. Phase H1 (legacy kernel extraction) is therefore closed
as unnecessary rather than deferred.

## What changed

- `HolShadowReport::certified()` (core) returns the legacy result with every
  declaration the kernel did not replay reported as an error
  (`failed kernel certification: …`) and removed from the accepted list.
- The CLI runs the HOL replay on every check and reports the certified
  result; the exit status is non-zero when certification fails. `--hol-shadow`
  is accepted and is now the default. `--legacy-only` runs the teaching
  checker alone for debugging, prints `Not certified`, is refused together
  with `--hol-profile` or `--assignment`, and still hands files with an exact
  logical package import to the kernel.
- The TUI and line editors use kernel-certified analysis by default.
- The Wasm boundary was already fail-closed (`ok` and `hol_certified` are
  the same value); it is unchanged.

## Evidence the decision rested on

- The H4 shadow gate: 74/74 corpus files and 589/589 root receipts replay
  with zero mismatches (`python3 scripts/hol_shadow.py check`), and the
  frozen oracle still rejects all 38 intended-negative theorems.
- Dual-certified latency is 0.2–0.7 s on package-importing files
  (`AUDIT_2026-07.md` §E); the Wasm artifact is under the 1.5 MB review line.
- The legacy kernel could not be made auditable in place: `kernel.rs` is a
  41-line facade over `check_kernel_proof_node` inside `lib.rs`, and the
  boundary linter deliberately never inspects that file. The HOL trusted
  modules are ~5.5k pre-test lines across seven boundary-linted files.

## The audit that preceded it

Two independent soundness reviews of the trusted modules were run before the
flip (2026-09-03). Findings and dispositions:

| Finding | Severity | Disposition |
|---|---|---|
| Structural-recursion arm bodies not validated against the definition's type scheme; a free type parameter in an arm unified with any theorem's parameter of the same id. Reproduced: `False` derived as a checked, axiom-free theorem. | Soundness | Fixed; regression test in `recursion.rs`. |
| Zero-constructor inductives accepted by the HOL core, and the surface language accepted `data T \| mk(T)` (no base constructor); with `const c : T` both engines proved `False`. The legacy production checker was affected. | Soundness | Fixed in both engines: every data type needs a constructor whose arguments do not mention the type. Regression tests in `inductive.rs` and `lib.rs`. |
| Unbounded normalization: a well-typed term of a few dozen nodes (Church numeral squaring) overflowed the stack; 20k-deep terms overflowed `infer_type`. Under `panic = "abort"` this traps the Wasm instance. | Robustness | Fixed: per-thread depth guard (2048) and reduction-step budget (4M) in `terms.rs`; CLI runs on a 256 MiB checker thread; Wasm links with a 16 MiB stack. Side effect: the legacy parser no longer dies at ~1,000 nested parentheses. |
| The four kernel signatures are independent values with positional ids; a proof checked against one set and instantiated against another is accepted. | Boundary | `SpikeElaborator` is the only bundle (private fields, no `&mut` escape, single production instance); it is now boundary-linted. A rename to something like `HolCore` and moving the kernel into its own crate so `pub(crate)` means what the comments claim are recommended follow-ups. |
| `usize` overflow in parameter instantiation on 32-bit targets. | Robustness | Fixed (`checked_add`). |
| `HolProofAudit` never emits `FunctionExtensionality`/`PropositionalExtensionality`/`Choice`; an axiom stating them appears only as an anonymous axiom dependency. | Hygiene | Open. Not unsound (axiom use is visible); receipts cannot distinguish "classical via axiom" from "classical via rule". |
| `HolProofContext` is not bound to the `TermContext` its hypotheses were checked under. | Hygiene | Open; every consuming rule re-infers, no accepted-wrong-conclusion path found. |
| Reviewer judgment: the load-bearing logic is ~700 lines in `terms.rs` and ~900 in `proofs.rs`, reviewable in one sitting; the rest is per-constructor boilerplate. | — | Recorded here as the re-audit the H3 "trusted core remains auditable" criterion asked for. |

The first two findings are the reason the audit came before the flip. Both
were reachable only through shapes the surface language did not emit (the
first) or that no corpus file used (the second), but the second was
reachable by a student typing it.

## What remains

1. **Stop adding semantics to the legacy kernel.** New features are
   implemented as elaboration into HOL draft proofs; the legacy kernel check
   becomes advisory (it still runs, because the elaborator's goal state
   depends on it) and is not extended.
2. **Delete `check_kernel_proof_node`** and the `_with_hol_shadow` twins once
   nothing depends on the legacy kernel's verdict, collapsing the 13 mirrored
   entry points and 118 `cfg(feature = "hol-shadow")` sites. At that point
   the `hol-shadow` feature flag goes away.
3. **Rename** `SpikeElaborator` to reflect its role, and consider moving
   `hol/{types,terms,proofs,inductive,recursion,theorems}.rs` plus the bundle
   into a separate crate so the crate boundary enforces what the linter only
   checks textually.
4. **Emit extensionality/choice features** for trusted axioms whose
   statements are those principles, or document that receipts report them as
   axiom dependencies only.
5. **Parser complexity:** 50,000 nested parentheses still hang (audit A4);
   the stack fix only removed the crash.

## What would reopen the decision

If the follow-up review of the trusted modules finds them not reviewable by
one person in a sitting, or if the shadow classifier's two
"rejected before classification" statements or 81 incomplete receipts turn
out to hide a gap the parity numbers do not show, the "keep the FOL engine
as a small independent kernel" option should be reconsidered — but that
option requires actually extracting that kernel, which is the work this
decision avoids.
