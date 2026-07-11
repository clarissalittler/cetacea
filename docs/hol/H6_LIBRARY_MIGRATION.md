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

This is not yet a student-visible library. `ListLibrary` currently targets the
experimental `SpikeElaborator`; the compatibility elaborator, `.ctea` parser,
standard-library imports, browser, and assignment manifests do not yet expose
generic list declarations.

## Remaining migration slices

1. Move package installation behind a production HOL library registry shared
   by the compatibility driver and future native HOL syntax. Give installed
   packages stable qualified names and provenance suitable for receipts and
   assignment allowlists.
2. Add student-facing rank-one type application and generic declaration syntax,
   then publish the list package through the standard library. Retain aliases
   for the current monomorphic list vocabulary for one release cycle.
3. Extract a generic relation/graph package over the same list handles. Keep
   path witnesses explicit in restricted FOL exercises; more abstract closure
   theorems may live in HOL and must remain policy-visible when reused.
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

At this checkpoint the release CLI is 3,501,856 bytes and the raw Wasm module
is 1,361,312 bytes, still below the 1.5 MB review line.
