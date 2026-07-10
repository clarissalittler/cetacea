# H3 HOL Spike Decision Report

Date: 2026-07-10  
Measured commit: `7a2573adc60566430b47c0d1261817e18c229007`

## Decision

**Conditional go for a bounded H3.5 bridge; no wholesale compatibility
migration yet.**

H3.5 is now complete. Its exit decision authorizes a bounded H4a compatibility
substrate while retaining the legacy checker; see
[`H35_EXIT_DECISION.md`](H35_EXIT_DECISION.md). The text and measurements below
retain the original H3 checkpoint, followed by the work that closed its gates.

The spike is strong evidence that a small constructive HOL core can support the
generic libraries needed by a discrete-mathematics course while certifying
ordinary exercises as `fol+induction`. It is not yet evidence that Cetacea
should replace the current checker or teach the existing parser the full HOL
surface language.

Before Phase H4 begins, one more bounded bridge must demonstrate:

1. checked theorem storage and theorem-reference evidence;
2. dependency receipts discovered from evidence rather than supplied by the
   spike driver;
3. a reusable cardinality-transport theorem over a stored bijection;
4. schematic theorem type-parameter scope checking;
5. a linked Wasm measurement in which the HOL engine is reachable rather than
   removed as dead code; and
6. a written mechanical lowering map for the current FOL declaration and proof
   forms.

If those items remain small and preserve the measurements below, proceed to the
compatibility elaborator. If theorem reuse or dependency discovery forces a
large proof-language or kernel expansion, retain the FOL engine and port only
the successful receipt and generic-library ideas.

## H3.5 progress after the measured checkpoint

The first three bridge items are now implemented:

- checked theorems have stable IDs and can be referenced only through explicit,
  kernel-checked type instantiations;
- theorem and structural-definition dependencies are collected from stored
  statements and hole-free proof evidence, then closed transitively when the
  receipt is built; and
- schematic statements and every type annotation embedded in proof evidence
  are checked against the theorem's declared rank-one type parameters.

The old spike method that accepted a caller-supplied dependency list has been
removed. The list, graph, and finite examples now use checked theorem storage
and automatically derived receipts end to end. Focused adversarial tests cover
a first-order-looking theorem facade over induction, a recursive definition
mentioned only in discarded proof evidence, unknown theorem IDs, duplicate
theorem names, and undeclared schematic type parameters.

The reusable bijection/cardinality theorem is now also checked. It proves that
mapping a duplicate-free exhaustive list along a function with a two-sided
inverse preserves duplicate-freedom, length, and exhaustiveness. Its stored
proof reuses separate checked lemmas for `map` length, forward and reflected
membership, injective `Nodup`, and surjective coverage.

The concrete Color/Bit statement is checked twice. Its direct proof retains a
`fol+induction` receipt. A second proof reuses the generic theorem and therefore
has the same first-order statement but an honest `hol` required fragment. This
is intentional: restricted FOL mode must reject a genuinely higher-order lemma
even when its concrete conclusion happens to be first-order.

The linked measurement and mechanical lowering map are now complete. See the
exit decision for the measured `101ec15` artifacts and
[`FOL_TO_HOL_LOWERING.md`](FOL_TO_HOL_LOWERING.md) for the form-by-form map and
eight H4a prerequisites.

## What the spike now checks

### List library

The executable list example declares parameterized `List A` and checked
structural definitions for:

- `All`;
- `Member`;
- `Nodup`;
- `append`; and
- `length`.

It kernel-checks a computed `Nodup` theorem and a structural-induction theorem.
The resulting receipts are trust-free `fol+induction`; the `Nodup` theorem is
transitively marked `StructuralRecursion`, and the induction theorem derives
`Induction` from checked proof evidence.

### Graph paths

The graph example defines a typed edge relation and an endpoint-aware
`ValidPath`. It proves constructively:

```text
ValidPath xs a b ->
ValidPath ys b c ->
ValidPath (append xs ys) a c
```

The proof is by structural induction on `xs`. Its statement and required
receipt are both `fol+induction`, with the exact transitive feature set
`{Induction, StructuralRecursion}` and no trusted or incomplete dependency.

### Finite enumeration and cardinality

The finite example declares two two-element datatypes, explicit duplicate-free
exhaustive enumerations, structural `encode`/`decode` functions, and generic
list `map`. It proves both inverse laws and constructs a common natural-number
witness for `HasCard` on the two types. The direct theorem is constructive,
trust-free, and classified as `fol+induction`.

H3.5 additionally stores and reuses a schematic transport theorem over two
types, functions in both directions, and their inverse laws. Its supporting
list lemmas and the final transport theorem are all hole-free and axiom-free.
The reused concrete proof is correctly classified as `hol` through its
transitive dependency, demonstrating rather than bypassing fragment isolation.

### Rejection cases

Every example includes deliberate failures for:

- an ill-typed application;
- a direct self-call that bypasses the supplied recursive-result binders; and
- a datatype occurrence to the left of a function arrow.

Declarations are transactional: failed positivity, typing, name, or recursion
checks leave no partially registered type, constructor, or definition.

## Soundness-relevant findings

The spike found three issues before any compatibility migration:

1. **Type-constructor parameter classes were not retained.** A constructor
   declared with a first-order parameter could have been formed at an arrow
   type through raw `CoreType` construction. Constructor applications now
   enforce parameter classes at every occurrence.
2. **Structural reduction initially substituted terms but not schematic type
   annotations.** Reducing `ValidPath[Vertex]` could emit an equality still
   annotated at abstract `A`. Reduction now substitutes explicit rank-1 type
   arguments through branch bodies and binder metadata; a focused regression
   test and the graph example cover it.
3. **Zero-argument type application had two core spellings.** Empty type
   application is now canonicalized to the monomorphic constant form, avoiding
   false failures of definitional equality.

Finding these at the isolated spike stage supports continuing the parallel-core
strategy and argues against an immediate parser-first rewrite.

## Measurements

The pre-HOL values come from [`BASELINE.md`](BASELINE.md). Current timings are
warm observations on the same machine and toolchain; they are signals rather
than CI thresholds.

| Measurement | Pre-HOL | H3 spike | Change |
|---|---:|---:|---:|
| Rust unit tests | 252 | 335 (7 CLI + 328 core) | +83 |
| Warm workspace tests | 0.73 s | 0.55 s | noise-level improvement |
| Semantic baseline verification | 3.26 s | 3.21 s | -0.05 s |
| No-op native release build | 0.03 s | 0.04 s | +0.01 s |
| Incremental Wasm release rebuild | 6.84 s | 7.41 s | +0.57 s |
| Native release CLI | 2,162,328 bytes | 2,180,888 bytes | +18,560 (+0.86%) |
| Wasm release module | 979,741 bytes | 977,475 bytes | -2,266 (-0.23%) |

The three H3 example tests themselves report 0.01 seconds of test execution
(0.03 seconds including the warm Cargo process).

The experimental `hol/` tree is 7,781 lines including tests and the executable
examples. The five soundness-critical prototype modules contain about 3,030
lines before their `#[cfg(test)]` sections:

- resolved types;
- typed terms and normalization;
- proof checking;
- inductive declarations; and
- structural recursion.

At this measured H3 commit, the Wasm result was **not yet a linked-engine
comparison**. H3.5 closed that gap; the exit report records the reachable
1,227,302-byte Wasm artifact and smoke latency.

## Gate assessment

| H3 gate | Result | Evidence or remaining concern |
|---|---|---|
| No new untracked axiom | Pass | All three theorem receipts have empty axiom and incomplete sets. |
| Examples clearer than FOL encodings | Conditional pass | Generic definitions and the path theorem are natural; hand-built de Bruijn proof evidence is intentionally not a student surface. |
| Trusted core remains auditable | Conditional pass | H3.5 has about 3,713 pre-test lines in six guarded HOL modules, including theorem storage. |
| Ordinary examples certify as FOL/FOL+induction | Pass | The direct list, graph, and finite proofs require `fol+induction`; generic HOL reuse is separately and honestly labeled `hol`. |
| HOL dependency laundering is rejected | Pass | Theorem and definition dependencies are now discovered from statements and hole-free evidence, including adversarial facades. |
| Type, positivity, and termination errors are rejected | Pass | Each executable example exercises all three classes. |
| Native latency is acceptable | Pass | No measurable regression in warm tests or corpus verification. |
| Wasm size and latency are acceptable | Conditional pass | Linked Wasm is 1,227,302 bytes (+25.6% from H3); mean smoke time is 0.0441 ms. Re-measure throughout H4a. |
| Credible mechanical lowering of existing corpus | Pass for H4a planning | Every legacy form is mapped; eight required compatibility mechanisms are explicit in the lowering document. |
| Generic cardinality preservation under bijection | Pass | Checked `map` lemmas and a stored schematic transport theorem are reused at Color/Bit; the dependency honestly raises that proof to HOL. |

## H3.5 scope and exit gate

H3.5 should remain smaller than a compatibility parser. Its only authorized
work is:

1. introduce stable theorem IDs, checked theorem storage, and a `TheoremRef`
   proof node;
2. derive theorem dependencies and their receipts by traversing checked
   evidence;
3. validate all free type parameters in schematic theorem statements and
   proofs;
4. prove and reuse the list lemmas needed for generic bijection/cardinality
   transport;
5. link a temporary H3 smoke entry point into native and Wasm builds and repeat
   artifact/latency measurements; and
6. map each current FOL core form to its intended HOL lowering, identifying any
   declaration that cannot be translated mechanically.

The exit gate is a second short decision note. Phase H4 is authorized only if:

- dependency discovery cannot be omitted or forged by the elaborator;
- the generic cardinality theorem checks without a new axiom;
- the linked Wasm cost remains acceptable;
- the kernel boundary check still passes; and
- the legacy 74-file semantic oracle remains exact.

## Recommendation

Proceed with the bounded H4a substrate in the exit decision. Do not delete,
freeze, or weaken the existing FOL checker, and do not expand the production
parser yet. The architecture has earned compatibility work, not a cutover.
