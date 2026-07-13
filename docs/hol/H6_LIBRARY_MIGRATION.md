# H6 Library and Curriculum Migration

## Current checkpoint

H6 has begun with a reusable, elaborator-side parameterized list package. It
atomically installs:

- `List A`, `nil`, and `cons`;
- `All`, `Member`, `Nodup`, and `append`; and
- an optional `length` extension over a supplied checked Nat interface.

The package exposes checked typed handles and term builders rather than asking
each client to pass unrelated declaration IDs. The list, graph-path, and finite
cardinality examples now install and use this one package.

`List` deliberately has an unrestricted HOL element parameter. Fragment
classification happens at each use: an open `Member` goal over `List Nat` is
`fol+induction`, while an `All` instance over `List Prop` is `hol`. The generic
implementation therefore does not force ordinary graph and finite exercises
out of their restricted teaching profile. The existing path-concatenation
theorem remains constructive, trust-free `fol+induction`; the direct finite
cardinality proof does too. Reusing the genuinely higher-order cardinality
transport theorem still raises only that proof's required fragment to `hol`,
as intended.

The package now also has a production-facing, on-demand registry seam. The
compatibility elaborator owns a `HolLibraryRegistry` and can atomically install
the package as logical module `std/hol/list@1` under reserved core namespace
`@library.list.v1`. Registry records retain module, version, source, all eight
declarations, and stable audit names for the five structural-definition
receipts (for example `std/hol/list@1::Member`). Repeated installation is
idempotent, but a registry cannot be paired with another core or rebound to a
different Nat interface. Late name collisions roll back both declarations and
metadata.

The graph-path substrate is now reusable as well. `GraphLibrary` installs an
endpoint-aware `ValidPath` structural predicate over the shared list handles
and can check/store path concatenation for any concrete element type. Its edge
relation is supplied as a checked polymorphic symbol family when the package is
installed. This choice is semantically important: passing a predicate as an
ordinary argument is genuinely higher-order, even when the application is
saturated. Executable tests show that a predicate-valued path over an otherwise
first-order `Vertex` domain is `hol`, while the symbol-specialized `Vertex`
path and concatenation theorem remain constructive, trust-free
`fol+induction`. Instantiating the same package at `Prop` is also correctly
`hol`. The graph spike now consumes this package instead of owning a second
copy of the definition and proof builder.

Cardinality transport is now a reusable public elaborator-side package too.
`CardinalityTransportNames` permits canonical or namespaced installation, and
`CardinalityTransportLibrary` exposes `map`, all five checked supporting
lemmas, and the final transport theorem. Installation is transactional: a late
collision cannot leave a partial definition or lemma chain behind. Receipt
tests pin the final theorem's exact direct dependencies on `Member`, `Nodup`,
`length`, `map`, `nodup_map_injective`, `map_length`, and
`map_coverage_surjective`; every theorem is trust-free and honestly classified
as `hol`. The finite spike now consumes this public package rather than a
private H3.5 builder.

It is also registered as logical module `std/hol/cardinality@1` under reserved
namespace `@library.cardinality.v1`. The record catalogs `map`, all six theorem
receipts, checked explicit-parameter wrappers for all six source aliases, and an
explicit dependency on `std/hol/list@1`. Installing cardinality
installs that dependency when necessary, but stages the complete closure as one
transaction: a late theorem collision rolls back both packages. Reinstallation
validates the core binding, Nat binding, declaration catalog, individual
receipts, and the final theorem's cross-package receipt dependencies before it
is accepted as idempotent. Stable names such as
`std/hol/cardinality@1::cardinality_transport` are therefore available to the
future import-policy layer.

Finite enumeration now has a checked substrate rather than a Color/Bit-only
proof script. `FiniteEnumerationLibrary` defines polymorphic
`HasCard A xs n` from `Nodup`, `length`, and exhaustive `Member`; its definition
receipt pins those three dependencies. For a parameterless datatype whose
constructors are all nullary, `declare_nullary_inductive` derives the complete
constructor list, its Nat numeral, a no-duplicates proof from constructor
disjointness, and an exhaustive-coverage proof by induction. The generated
theorem is trust-free and remains `fol+induction` at an ordinary finite type,
while a `List Prop` use is correctly `hol`. The generator is tested with three
constructors, rejects constructors with fields without changing the core, and
the Color/Bit spike now reuses its two stored enumeration receipts.

The generic predicate is registered as `std/hol/finite@1` under
`@library.finite.v1`, with the `HasCard` definition and checked
`has_card_intro` theorem as its owned declarations and `std/hol/list@1` as an
explicit dependency. Its validator pins the definition to registered
`Member`, `Nodup`, and `length` receipts and the introduction theorem to that
complete dependency set. Generated facts such as `traffic_has_card`
deliberately remain client theorem receipts, not declarations owned by the
generic package. Installing finite enumeration can stage List automatically,
and a collision rolls the entire closure back.

The shared surface AST now represents rank-one constructor application and the
parser accepts prefix forms such as `List Nat` and `List (List Nat)`. Formatting
round-trips nested and multi-argument applications; theorem-schema substitution
and inference recurse through them; and compatibility lowering resolves the
checked constructor and validates arity. Rank-one type parameters cannot be
misused as higher-kinded constructors. A monomorphic legacy `sort List` still
rejects `List Nat` with an explicit diagnostic until a logical package import
binds the generic constructor.

That parser-independent binding now exists for `std/hol/list@1`.
`CompatibilityElaborator::import_builtin_list_v1` atomically binds either the
unqualified package leaves or a namespace such as `L.List`, `L.nil`, and
`L.Member` to the registered core handles and their checked rank-one schemes.
Type inference can determine `nil` from its context inside `cons`; qualified and
unqualified `Member` applications lower identically. Repeated bindings are
idempotent, while any early or late alias collision rolls back both registry and
surface state. A qualified generic package can coexist with the current
monomorphic `List`.

The first source-driver seam is now live under HOL-shadow authority.
`import std/hol/list@1 as L` permits a theorem parameter such as
`xs : L.List Nat`, and the transitional proof UI can type-resolve `cons`,
`Member`, `Nodup`, `append`, and `length` by rank-one unification. Reflexivity
and propositional proofs over those terms are independently checked by both
engines and certified `fol+induction`. This is still a signature-only bridge:
expected types flow inward through package applications, so polymorphic `nil`
can be inferred inside `cons`, on either side of `append`, and beneath an outer
`Member`. A standalone `nil = nil` remains correctly ambiguous. `All` still
has a predicate-valued source argument rather than pretending its first
argument is a first-order term. Named predicates and expected-type-directed
lambdas now cross both checkers; variable-list uses remain policy-visible as
`hol`, while closed nil uses can normalize to their least `fol+induction`
dependency. No List computation, simplification, or induction has been copied
into the legacy engine. The first computation-facing surface is instead the
checked theorem `append_nil_left`: its package receipt depends on the checked
`append` definition, its alias descriptor is compared against the stored core
statement, and source `exact`/`simp` proofs retain that dependency. At this
List-only checkpoint, default legacy checking rejected logical HOL imports and
finite/cardinality imports rejected explicitly. Reports and JSON carried the
exact package ID, and assignment manifests allowlisted that ID without
filesystem canonicalization.

The same alias mechanism now exposes `list_induction`. Its core theorem is
checked with explicit `Induction` evidence; its source schema takes `A`, a
predicate over `List A`, and the scrutinee. A concrete source application stays
`fol+induction` rather than inheriting a generic `hol` classification, while
the package receipt and induction feature remain transitive and visible. The
checkpoint artifacts are 3,764,424 bytes for the native CLI and 1,368,943
bytes for Wasm.

The package now checks and receipts the constructor equations `append_cons`,
`length_nil`, and `length_cons` as well. Source aliases for `append_cons` and
`length_cons` cross both engines through `exact` and `simp`; their concrete
constructor arguments determine the List instance. `length_nil` now uses the
checked source ascription `(L.nil : L.List A)` to select the instance that its
Nat result cannot determine. The annotation is substituted, validated, and
erased by both elaborators; it adds no kernel term form. This checkpoint
measures 3,794,240 bytes natively and 1,369,623 bytes in Wasm.

The source package also exports the first-order predicate constructor laws
`member_nil`, `member_cons`, `nodup_nil`, and `nodup_cons`. The cons laws are
constructive bi-implications encoded as conjunctions, avoiding proposition
equality and retaining `fol+induction` for concrete instances. Their conversion
proofs depend on the registered `Member` or `Nodup` definition, and source uses
retain the individual stable theorem receipt. This checkpoint measures
3,828,728 bytes natively and 1,373,157 bytes in Wasm.

`all_nil` and `all_cons` complete the structural predicate constructor laws.
Both are checked conversion theorems, but their concrete classifications differ
after normalization: nil eliminates the predicate and remains
`fol+induction`, while cons retains `P(h)` and is `hol`. Stable receipts remain
visible in both cases. The package validator now pins 19 exact declarations and
16 receipts. This checkpoint measures 3,851,304 bytes natively and 1,373,491
bytes in Wasm.

The package now owns derived theorem `append_nil_right`. Its checked induction
proof carries the `Induction` feature and an `append` dependency; exact source
reuse remains `fol+induction`. A representative source proof also derives it
solely from `list_induction`, `append_nil_left`, and `append_cons`, and the root
receipt records exactly that public theorem set plus the transparent `append`
definition used by conversion. Ascriptions remain present long enough to guide
generic proof replay but are transparent to conversion and rewriting. The
validator now pins 20 declarations and 17 receipts. This
checkpoint measures 3,870,472 bytes natively and 1,374,035 bytes in Wasm.

Derived theorem `append_assoc` is now installed and exposed as well. Its
three-list statement is proved by direct checked induction in the package, and
a separate source proof reconstructs it from `list_induction`,
`append_nil_left`, and `append_cons`. Both receipts carry `Induction` and remain
constructive `fol+induction`; the source receipt's package dependencies are
exactly those three theorems and the transparent `append` definition. The
validator now pins 21 declarations and 18 receipts. This checkpoint measures
3,885,320 bytes natively and 1,374,139 bytes in Wasm.

Derived theorem `length_append` is now installed and exposed. The package's Nat
interface explicitly includes checked addition, and the theorem is proved by
List induction with kernel-visible `append`, `length`, and `add` dependencies.
An independent source proof uses only `list_induction`, `append_nil_left`,
`append_cons`, `length_nil`, and `length_cons`; its receipt also records the
transparent List definitions used during conversion. Both proofs are
constructive `fol+induction`. The validator now pins 22 declarations and 19
receipts. This checkpoint measures 3,907,064 bytes natively and 1,379,905 bytes
in Wasm.

The browser now exercises the installed package rather than rejecting logical
imports. Its full-file Wasm result is fail-closed dual checking: legacy UI
acceptance is necessary, and every declaration must also replay through HOL
without a mismatch. JSON includes the exact package ID, receipt IDs, fragments,
features, and dependency status. Goal, step, and explanation requests share the
HOL-enabled virtual-import path, including certification of completed stepped
proofs. Size-optimized LTO yields a 1,651,664-byte native CLI and a
1,167,950-byte raw Wasm module.

The native CLI now makes the same fail-closed choice automatically for a root
or transitive logical package import. Core `CheckResult` carries an explicit
capability flag, so check, TUI, and line modes can reroute without recognizing
diagnostic prose; package-free sources retain the legacy path unless
`--hol-shadow` is requested. Native check JSON exposes the complete package and
receipt report without that flag. This checkpoint measures 1,656,344 bytes
natively and 1,167,984 bytes in raw Wasm.

Finite enumeration now has an end-to-end source import as well.
`import std/hol/finite@1 as F` transactionally exposes the package's checked
List dependency under `F`, followed by `F.HasCard` and the receipt-backed
`F.has_card_intro`. Registry and result metadata still report the two owning
packages separately. The generic theorem receipt is conservatively `hol`, but
concrete applications are reclassified; this lets an ordinary finite type stay
`fol+induction` without weakening the boundary for higher-order instances. A
public source proof derives `one_has_card` for a
one-constructor datatype using List constructor laws and structural induction;
its receipt is constructive, trust-free `fol+induction`, carries `Induction`,
and names the finite introduction theorem directly. The same example runs in
the browser. This checkpoint measures 1,675,000 bytes natively and 1,182,740
bytes in raw Wasm.

Rank-one function-symbol parameters now cover the arrow-valued source seam
needed by cardinality transport. `(f : A -> B)` records a saturated
domain/result schema in the transitional checker and a real curried arrow in
HOL. The schema can be instantiated only by a named function and cannot be used
bare or partially applied. Dual-checked generic and concrete Nat reflexivity
examples retain `fol+induction`, while bad arities reject. This checkpoint
measures 1,700,384 bytes natively and 1,197,428 bytes in raw Wasm.

The first cardinality source import now exposes `map` and `map_length` together
with the complete checked List dependency. The source theorem alias targets a
new kernel-checked template that specializes the package's original quantified
`map_length`; no proof is trusted or replayed by the legacy engine. Mixed
rank-one inference checks the named function's domain and codomain before
inferring the List instances, and the complete import is transactional and
idempotent. A saturated concrete use remains honestly `hol`: `map` takes a
function as data, unlike a theorem schema that merely substitutes a function
symbol into first-order application positions. The browser example and
assignment tests therefore require the HOL profile and both exact package IDs.
This checkpoint measures 1,741,224 bytes natively and 1,234,290 bytes in raw
Wasm.

`cardinality_transport` is now source-bound as well. A checked wrapper removes
only the outer function and List quantifiers; its inverse, Nodup, and coverage
premises and its three-part conclusion are unchanged. Generic source reuse with
function-symbol parameters crosses both engines and retains
`std/hol/cardinality@1::cardinality_transport_schema`. The browser example now
checks both the concrete map-length instance and the generic final transport.
This checkpoint measures 1,753,232 bytes natively and 1,244,116 bytes in raw
Wasm.

All four supporting theorems now have checked source templates as well:
forward membership, inverse-reflected membership, injective map preservation of
Nodup, and surjective preservation of coverage. Their source aliases retain
separate stable receipts. The browser example reconstructs the final
three-component result from `nodup_map_injective`, `map_length`, and
`map_coverage_surjective`; native coverage also applies both membership lemmas
directly. This complete-catalog checkpoint measures 1,775,272 bytes natively
and 1,262,322 bytes in raw Wasm.

## Remaining migration slices

1. Extend the implemented function-symbol theorem schemas to the remaining
   generic declaration forms and source surfaces, then decide when low-level
   legacy core APIs should select the sidecar automatically. Native CLI and
   browser acceptance are already fail-closed and automatic. Retain aliases
   for the current monomorphic list vocabulary for one release cycle. The
   import seam is
   specified in [`H6_SURFACE_IMPORTS.md`](H6_SURFACE_IMPORTS.md).
2. Extend the implemented package-ID JSON/manifest policy and stable definition
   receipt names to imported theorem aliases and browser assignment-policy
   enforcement.
3. Register and expose graph instances once surface imports can bind a checked
   edge-symbol family. Keep path witnesses explicit in restricted FOL
   exercises; predicate-valued relations and more abstract closure theorems
   remain HOL and must stay policy-visible when reused.
4. Extend the implemented finite surface to representative multi-constructor
   exercises, then prove pigeonhole,
   finite-union-cardinality, and handshake targets through checked library
   theorems. Extend enumeration generation beyond nullary datatypes only when a
   course theorem requires it.
5. Add the finite tree edge/vertex theorem and a pilot chapter sequence. Freeze
   each assignment's profile, imports, trusted principles, and theorem
   signatures with manifests.

## Gates for each slice

- Package installation is transactional, typed, and receipt-producing.
- Concrete first-order clients retain the least `fol` or `fol+induction`
  fragment even when the package is polymorphic.
- Higher-order instances and transitive HOL theorem reuse cannot be laundered
  through a first-order-looking conclusion.
- The 74-file exact baseline, 600-statement shadow classifier, kernel boundary,
  feature-disabled core build, and native/Wasm release builds remain green.
- Student exercises need no explicit type lambdas, de Bruijn indices, kernel
  IDs, or other internal HOL machinery in restricted units.

Release artifacts are measured at each completed source slice; raw Wasm remains
below the 1.5 MB review line at the induction checkpoint.
