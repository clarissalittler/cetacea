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
receipts, and an explicit dependency on `std/hol/list@1`. Installing cardinality
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
`@library.finite.v1`, with `HasCard` as its sole owned declaration and
`std/hol/list@1` as an explicit dependency. Its validator pins the `HasCard`
receipt to the registered `Member`, `Nodup`, and `length` receipts. Generated
facts such as `traffic_has_card` deliberately remain client theorem receipts,
not declarations owned by the generic package. Installing finite enumeration
can stage List automatically, and a collision rolls the entire closure back.

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

The first source-driver seam is now live but deliberately type-only. Under
HOL-shadow authority, `import std/hol/list@1 as L` permits a theorem parameter
such as `xs : L.List Nat`; a reflexivity theorem over that type is independently
checked by both engines and certified `fol+induction`. Default legacy checking
rejects logical HOL imports. List operation names are reserved but remain
unavailable to legacy tactics, and finite/cardinality imports reject explicitly,
until their end-to-end surfaces are implemented. Reports and JSON carry the
exact package ID, and assignment manifests allowlist that ID without filesystem
canonicalization.

## Remaining migration slices

1. Extend the implemented type-only logical List import through operation
   resolution, computation, induction, and tactics; add generic declaration
   syntax, then publish it for ordinary checking. Retain aliases for the current
   monomorphic list vocabulary for one release cycle. The import seam is
   specified in [`H6_SURFACE_IMPORTS.md`](H6_SURFACE_IMPORTS.md).
2. Extend the implemented package-ID JSON/manifest policy and stable definition
   receipt names to imported theorem aliases and browser/editor results.
3. Register and expose graph instances once surface imports can bind a checked
   edge-symbol family. Keep path witnesses explicit in restricted FOL
   exercises; predicate-valued relations and more abstract closure theorems
   remain HOL and must stay policy-visible when reused.
4. Expose registered finite enumeration and cardinality transport through
   surface imports, then prove the representative pigeonhole,
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

At the type-only logical-import checkpoint the release CLI is 3,632,264 bytes
and the raw Wasm module is 1,349,516 bytes, still below the 1.5 MB review line.
