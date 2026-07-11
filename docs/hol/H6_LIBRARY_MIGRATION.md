# H6 Library and Curriculum Migration

## Current checkpoint

H6 has begun with a reusable, elaborator-side parameterized list package. It
atomically installs:

- `List A`, `nil`, and `cons`;
- `All`, `Member`, `Nodup`, and `append`; and
- an optional `length` extension over a supplied checked Nat interface.

The package exposes checked typed handles and term builders rather than asking
each client to pass unrelated declaration IDs. The list, graph-path, and finite
cardinality examples now install and use this one package. The multi-lemma
cardinality-transport package consumes the same handles and is transactional as
well: a failure after earlier declarations have been staged leaves the caller's
elaborator unchanged.

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

This is not yet a student-visible library. `ListLibrary` currently targets the
checked core, and `CompatibilityElaborator` exposes the package registry, but
the `.ctea` parser, standard-library import resolver, browser, and assignment
manifests do not yet expose generic list declarations. Reserved package names
are not added to the legacy surface: a current monomorphic `List`/`nil`/`cons`
declaration can coexist and keeps its original meaning.

## Remaining migration slices

1. Add student-facing rank-one type application and generic declaration syntax,
   then publish the list package through the standard library. Retain aliases
   for the current monomorphic list vocabulary for one release cycle.
2. Route package provenance and receipt names into shadow/JSON results and
   assignment import allowlists when surface imports can request a package.
3. Register and expose graph instances once surface imports can bind a checked
   edge-symbol family. Keep path witnesses explicit in restricted FOL
   exercises; predicate-valued relations and more abstract closure theorems
   remain HOL and must stay policy-visible when reused.
4. Turn finite enumeration and cardinality transport into importable packages,
   then prove the representative pigeonhole, finite-union-cardinality, and
   handshake targets through checked library theorems.
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

At the graph-library checkpoint the release CLI is 3,522,040 bytes and the raw
Wasm module is 1,359,017 bytes, still below the 1.5 MB review line.
