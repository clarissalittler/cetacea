# H3.5 Exit Decision

Date: 2026-07-10  
Measured commit: `101ec15eebd863e32b0b26a75abfaa63586e38e0`

## Decision

**Go for a bounded H4a compatibility substrate. Do not cut over, remove the
legacy checker, or add a new student-facing HOL parser yet.**

H3.5 closed all six gates from the H3 decision report:

1. checked theorem storage has stable IDs and explicit type-instantiated
   theorem references;
2. theorem and structural-definition dependencies are derived from checked
   statements and hole-free evidence, not supplied by callers;
3. a schematic, axiom-free cardinality-transport theorem is proved and reused;
4. schematic type scope is checked throughout statements and proof evidence;
5. native and Wasm artifacts contain a reachable HOL engine and have measured
   size and latency; and
6. every legacy type, term, formula, declaration, and proof form has a written
   lowering in [`FOL_TO_HOL_LOWERING.md`](FOL_TO_HOL_LOWERING.md).

This is enough evidence to build the compatibility substrate. It is not enough
evidence to switch the course over. The lowering audit found eight required
compatibility mechanisms, and the linked size cost is material. H4a is
therefore infrastructure-first and retains the 74-file legacy oracle as the
authority until exact dual checking succeeds.

## Logical result

The reusable finite-cardinality result is now factored into checked lemmas for:

- length of `map`;
- forward membership through `map`;
- reflected membership under a left inverse;
- preservation of `Nodup` by an injective map; and
- exhaustive coverage under a surjective map.

The final theorem says that mapping a duplicate-free exhaustive enumeration
along a function with a two-sided inverse preserves duplicate-freedom, length,
and exhaustiveness. It is rank-one polymorphic over both element types and uses
no axiom or incomplete declaration.

The Color/Bit statement is checked in two ways:

| Proof | Statement fragment | Required fragment | Why |
|---|---|---|---|
| Direct datatype proof | `fol+induction` | `fol+induction` | Uses structural definitions and induction only. |
| Reuse of generic transport | `fol+induction` | `hol` | Transitively depends on a theorem quantifying over functions. |

That difference is a success condition, not a regression. It demonstrates that
an FOL-looking conclusion cannot launder a genuinely HOL proof dependency.

## Dependency and trust result

The stored-theorem path has no dependency-list argument. Direct dependencies
are collected from:

- `TheoremRef` nodes;
- constants in stored statements;
- constants in motives, witnesses, targets, and other proof annotations; and
- constants in checked structural-definition arms.

Receipts close those dependencies transitively. Adversarial tests cover an
induction theorem hidden behind a `True` facade and a recursive predicate used
only in discarded proof evidence. Unknown theorem IDs, duplicate declarations,
free schematic type parameters, holes, ill-typed applications, negative
datatype occurrences, and direct self-calls are rejected transactionally.

No new axiom was introduced. The trusted HOL modules contain approximately
3,713 lines before their test sections:

| Module | Pre-test lines |
|---|---:|
| Types | 360 |
| Terms and normalization | 884 |
| Proof checking and evidence audit | 1,550 |
| Inductive declarations | 449 |
| Structural recursion | 296 |
| Checked theorem storage | 174 |

The 782-line generic cardinality proof constructor is elaborator-side evidence,
not trusted kernel code. Its verbosity is evidence that a surface proof
language is necessary; it is not a reason to add a trusted shortcut.

## Linked measurements

The H3 artifacts did not call the HOL engine, so linker dead-code elimination
made their size comparison provisional. Commit `101ec15` adds the same small
smoke to the release CLI (`--hol-smoke`) and Wasm
(`cetacea_hol_spike_smoke`). It executes checked inductive declaration,
structural recursion, induction, theorem storage/reference, explicit
polymorphic instantiation, receipt closure, and trust reporting.

| Measurement | Pre-HOL | H3, engine unreachable | H3.5, engine linked |
|---|---:|---:|---:|
| Rust tests | 252 | 335 | 340 |
| Warm workspace tests | 0.73 s | 0.55 s | 0.59 s |
| Semantic oracle | 3.26 s | 3.21 s | 3.28 s |
| No-op native release build | 0.03 s | 0.04 s | 0.01 s |
| Incremental Wasm release rebuild | 6.84 s | 7.41 s | 7.49 s |
| Native release CLI | 2,162,328 B | 2,180,888 B | 2,543,648 B |
| Wasm release module | 979,741 B | 977,475 B | 1,227,302 B |

Relative to the H3 dead-code-eliminated artifact, linking the engine adds
362,760 bytes (+16.6%) to the native CLI and 249,827 bytes (+25.6%) to Wasm.
Relative to the pre-HOL baseline, the increases are 381,320 bytes (+17.6%) and
247,561 bytes (+25.3%). These raw files have not been transport-compressed or
postprocessed by a Wasm size optimizer.

The smoke itself is not a latency concern:

- 1,000 calls in one Node-instantiated Wasm module averaged 0.0441 ms each; and
- 100 separate native CLI processes took 0.21 s total, about 2.1 ms per process
  including process startup.

For diagnostic comparison, exporting the entire hand-authored finite fixture
rather than the compact engine smoke produced a 1,293,257-byte Wasm module.
That number includes example-specific proof construction and is not used as the
engine-size gate.

### Measurement judgment

Latency and rebuild time pass. Raw linked size receives a **conditional pass**:
1.23 MB is acceptable for the bounded experiment, but a 25.6% increase is not
noise. Re-measure after every H4a milestone. A raw Wasm artifact around 1.5 MB
is a review trigger before adding more compatibility machinery, not permission
to weaken the kernel or fragment receipts.

## What the lowering audit changed

The lowering is credible, but it is not a simple AST rename. H4a must first add:

1. rank-one term, proposition-symbol, and predicate-symbol theorem parameters;
2. checked transparent nonrecursive definitions and delta reduction;
3. a first-order legacy `Set A` wrapper with audited membership computation;
4. typed pair/projection computation;
5. a checked structural-recursion argument position;
6. trusted and incomplete declaration/reference storage;
7. explicit classical evidence and transitive `Classical` receipts; and
8. instance-aware schematic receipts.

Two choices are particularly important:

- Legacy `(P : Prop)` and `(R : A -> Prop)` are rank-one schema symbols, not
  object-level quantifiers. Turning them into `forall P : Prop` or
  `forall R : A -> Prop` would falsely classify `std/prop.ctea` and much of the
  FOL library as HOL.
- Legacy `Set A` remains a first-order wrapper. Lowering it directly to
  `A -> Prop` would move the sets sequence out of the promised FOL mode.
  `set_ext` remains an explicit trusted axiom.

The positive corpus's datatypes use only direct recursion, so the checked H3
inductive subset is sufficient. The missing items above are compatibility
features already exercised by the corpus, not speculative new language design.

## Authorized H4a scope

H4a may implement only the substrate required by the lowering map, in this
order:

1. theorem-template term/symbol parameters plus trusted, incomplete, and
   classical declaration evidence;
2. transparent definitions, product computation, and a recursive-argument
   position;
3. the Nat and first-order legacy-set compatibility prelude; and
4. lowering from the existing parsed AST into the new core, beginning with
   constructive propositional files and expanding fragment by fragment.

After each item:

- run the full workspace tests;
- verify the exact 74-file, 588-declaration, 38-negative oracle;
- run the kernel-boundary check;
- measure linked native/Wasm size; and
- add adversarial tests for laundering, capture, trust, and transactionality.

H4a does **not** authorize deleting the FOL engine, changing existing syntax,
routing normal course checks to HOL by default, or weakening a receipt to make
the compatibility numbers look better.

## H4 exit gate

The compatibility phase succeeds only when both engines agree on every corpus
file:

- every positive declaration has the same canonical surface statement,
  accepted/incomplete/trusted status, constructive/classical use, and
  axiom/incomplete closure;
- every intended-negative theorem remains rejected individually;
- imports and aliases resolve to the same declaration identities;
- the new receipt additionally supplies an accurate Prop/FOL/FOL+induction/HOL
  classification; and
- linked artifact size remains acceptable after review.

Until then, the legacy checker remains the production and curriculum authority.
