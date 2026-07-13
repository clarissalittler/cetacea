# H6 HOL Surface Imports

## Decision

Versioned HOL packages will be explicit logical imports, beginning with:

```text
import std/hol/list@1
import std/hol/finite@1
import std/hol/cardinality@1
```

An optional existing import alias qualifies the exposed names:

```text
import std/hol/list@1 as L
const xs : L.List Nat
```

The version suffix is required. Paths ending in `.ctea` remain file imports;
an exact registered package ID is a logical import. This avoids guessing based
on filesystem state and gives assignment manifests a stable capability name.

Package-enabled files must ultimately be accepted by the HOL checker. We will
not simulate support by generating legacy axioms, unchecked monomorphic copies,
or a second implementation of generic List computation in the legacy kernel.
Ordinary files with no logical package import retain the existing legacy
authority and behavior until the explicit cutover decision.

## Rank-one type surface

The first surface checkpoint is implemented in the shared AST and parser:

```text
List Nat
Either Nat (Set Nat)
List (List Nat)
```

Type application is prefix notation, as specified by the HOL plan. Parentheses
are required only to group a nested application. `Type::App` participates in
formatting, schema substitution, schema inference, and compatibility lowering.
The HOL lowerer resolves a checked type constructor and validates its arity;
applying a rank-one type parameter as though it were higher-kinded is rejected.
A current legacy `sort List` still rejects `List Nat` explicitly, rather than
silently changing the meaning of a monomorphic course declaration.

`Prop` and arrow types are not added to this legacy-shaped `Type` node in this
checkpoint. They need an explicitly HOL surface context, not a relaxation of
every existing first-order declaration grammar.

## Atomic alias binding

The parser-independent List alias catalog is now implemented in
`CompatibilityElaborator`. `import_builtin_list_v1` already performs the five
steps that a successful source package import must use:

1. resolve the exact `LibraryPackageId`;
2. install its complete registry dependency closure;
3. preflight every requested type, constant, definition, and theorem alias;
4. bind surface names to checked core handles and rank-one schemes; and
5. commit registry state and aliases together.

An unaliased import requests the package's logical leaf names (`List`, `nil`,
`Member`, and so on). `as L` requests `L.List`, `L.nil`, `L.Member`, etc. Any
collision rejects the whole import. Reserved names such as
`@library.list.v1.List` remain internal and never appear in student source or
receipts. Stable audit names remain package-qualified, for example
`std/hol/finite@1::HasCard`, regardless of the chosen source alias.

Executable catalog tests cover `List Nat`, contextual inference of polymorphic
`nil`, `Member(0, cons(0, nil))`, the corresponding `L.*` spellings, repeated
imports, coexistence with a monomorphic List, and collisions at both the first
and a later alias.

`Command::Import` now recognizes the exact `std/hol/list@1` ID in HOL-shadow
mode. The transitional legacy environment records the constructor arity and
rank-one source signatures for `cons`, `Member`, `Nodup`, `append`, and
`length`; it does not copy definitions or imitate generic List computation.
Consequently both type-only statements and propositionally used operations can
cross the dual-checking boundary, for example:

```text
import std/hol/list@1 as L
theorem list_refl (xs : L.List Nat) : xs = xs := by
  refl

theorem member_id (x : Nat) (xs : L.List Nat) :
  L.Member(x, L.cons(x, xs)) -> L.Member(x, L.cons(x, xs)) := by
  intro h
  exact h
```

These are checked by the legacy proof UI and independently lowered, checked,
and classified `fol+induction` by HOL. Rank-one unification rejects mixed
instances such as a `Nat` member paired with a `List Color`. Expected types now
flow through nested package applications, so `cons(x, nil)`, `append(nil, xs)`,
and even `Member(x, append(nil, nil))` infer one consistent element type in
both engines. A bare `nil = nil` remains ambiguous and fails explicitly; no
arbitrary element type is guessed. `All` now has an explicit predicate-valued
argument descriptor, so both named predicate parameters and expected-type-
directed lambdas are accepted. A variable-list `All(P, xs)` remains visibly
`hol`; a closed nil instance may normalize away the predicate body and retain
only its `fol+induction` List dependency. No imported List definition is
copied into the transitional engine. Instead, the package now publishes the
checked theorem `append_nil_left`; `exact L.append_nil_left {...}` and
`simp [L.append_nil_left]` cross both engines and retain the stable package
receipt as a proof dependency. The checked theorem `list_induction` likewise
accepts explicit `A`, predicate-lambda `P`, and scrutinee `xs` parameters.
Applying it to a first-order property keeps the root theorem
`fol+induction`, records the `Induction` feature, and retains the stable package
receipt. Direct legacy unfolding and generic-List induction synthesis remain
unavailable. Low-level legacy-only core entry points reject the logical import;
the native CLI and browser automatically select fail-closed dual checking when
an exact package import is present. Repeated imports are idempotent. At this
List-only checkpoint, finite and cardinality package IDs were recognized but
rejected with
an explicit surface-not-implemented diagnostic. The induction checkpoint
artifacts are 3,764,424 bytes for the native CLI and 1,368,943 bytes for Wasm.

`append_cons` and `length_cons` are now source-bound through the same validated
alias mechanism. Constructor arguments determine their rank-one instance, and
a combined explicit `simp` invocation retains both stable theorem receipts.
The checked `length_nil` theorem is source-bound as well. Because `length(nil)`
returns Nat for every element type, its descriptor and uses write
`(L.nil : L.List A)`. Both engines validate and erase the annotation; a wrong
type is rejected rather than cast. This ascription checkpoint produces a
3,794,240-byte native CLI and a 1,369,623-byte raw Wasm module.

The source alias catalog now includes `member_nil`, `member_cons`, `nodup_nil`,
and `nodup_cons`. The cons theorems use constructive bi-implications rather
than proposition equality, so concrete theorem applications stay
`fol+induction`. End-to-end `exact` clients retain each stable theorem receipt;
the transitional engine receives no predicate reduction rule. This predicate
checkpoint produces a 3,828,728-byte native CLI and a 1,373,157-byte raw Wasm
module.

`all_nil` and `all_cons` complete the predicate constructor aliases and verify
the policy boundary directly. Normalization removes the predicate from the nil
instance, yielding `fol+induction`; the cons instance retains its predicate
value and is reported as `hol`. Both source proofs retain stable package
receipts, so neither result is a frontend guess. This checkpoint produces a
3,851,304-byte native CLI and a 1,373,491-byte raw Wasm module.

`append_nil_right` is now the first derived package theorem on this surface. Its
checked proof is inductive, and direct reuse retains the stable theorem receipt
and `Induction` feature. The same theorem is also proved in source from only
`list_induction`, `append_nil_left`, and `append_cons`; that root receipt names
exactly those theorem dependencies plus the transparent `append` definition
used by conversion, and remains `fol+induction`. Ascriptions persist through
the transitional proof replay only as checked typing evidence and are ignored
by rewrite matching. This checkpoint produces a 3,870,472-byte native CLI and
a 1,374,035-byte raw Wasm module.

`append_assoc` now exercises the same surface with three generic List values.
Direct alias reuse and a proof written from `list_induction`,
`append_nil_left`, and `append_cons` both check as constructive
`fol+induction`. The latter receipt pins exactly those three public theorems
plus the transparent `append` definition used by conversion. This checkpoint
produces a 3,885,320-byte native CLI and a 1,374,139-byte raw Wasm module.

`length_append` now connects the List surface to checked Nat arithmetic.
Addition is an explicit package-installation dependency, while students can
prove the result with `list_induction`, the two append equations, and the two
length equations. Direct reuse and reconstruction both remain constructive
`fol+induction`; the latter receipt pins those five public theorems plus the
transparent `append` and `length` definitions. The induction base now carries
its `List A` annotation through open arithmetic normalization, without making
annotations proof-relevant. This checkpoint produces a 3,907,064-byte native
CLI and a 1,379,905-byte raw Wasm module.

The browser path now enables the same HOL sidecar. `cetacea_check` reports
success only when the legacy teaching UI accepts the file and every accepted
declaration has a mismatch-free HOL replay; the response includes
`hol_certified`, exact imported package IDs, receipt IDs, least fragments, and
proof features. Virtual-import goal, step, and explanation endpoints load the
same List aliases, reject prefix mismatches, and certify completed stepped
proofs. The web example menu includes the public-surface `length_append` proof.
Size-optimized LTO produces a 1,651,664-byte native CLI and a 1,167,950-byte raw
Wasm module.

Native check mode now makes the same selection automatically. A logical package
import in the root or any transitive file import reroutes the check through the
HOL sidecar, fails on any replay mismatch, and reports the exact package and
receipt data without requiring `--hol-shadow`. TUI and line modes use the same
detection for package-aware goals; the flag remains useful to force certified
analysis on package-free files. Low-level legacy-only core APIs are unchanged.
This checkpoint is 1,656,344 bytes natively and 1,167,984 bytes in Wasm.

The finite package now crosses that same source boundary. Importing
`std/hol/finite@1 as F` atomically binds the checked List dependency as
`F.List`, `F.nil`, and the rest of its public catalog, followed by
`F.HasCard` and the kernel-checked `F.has_card_intro`. The shared namespace is a
source convenience only: reports list both package IDs, and stable receipts
remain `std/hol/list@1::*` or `std/hol/finite@1::*` according to ownership.
Collisions in either dependency or finite-owned names roll back the complete
import. The stored introduction theorem is conservatively `hol` because its
type parameter is unrestricted; each application is classified again, so the
concrete `One` instance remains `fol+induction` while a genuinely higher-order
instance cannot be laundered. The bundled `finite_one.ctea` proof constructs
`HasCard` for a one-constructor datatype from public Nodup, length, membership,
and induction rules. Its root receipt is constructive, trust-free
`fol+induction`, carries the induction feature, and directly depends on
`has_card_intro`. This checkpoint is 1,675,000 bytes natively and 1,182,740
bytes in raw Wasm.

The next cardinality prerequisite is implemented without making arrow types
ordinary first-order data. A theorem parameter `(f : A -> B)` is a rank-one
function-symbol schema: it must be saturated in source and instantiated by a
named function, while HOL lowering binds the actual curried arrow type. The
parser continues to treat arrows ending in `Prop` as predicate schemas. A
dual-checked generic reflexivity theorem and its concrete Nat instance retain
`fol+induction`; bare function values, partial application, lambdas, and arity
mismatches fail explicitly. This checkpoint is 1,700,384 bytes natively and
1,197,428 bytes in raw Wasm.

`std/hol/cardinality@1` now has its first source-facing slice. Importing it as
`C` transactionally binds the checked List dependency under `C`, the polymorphic
`C.map`, and `C.map_length`. The registry retains the original universally
quantified theorem and adds a checked explicit-parameter wrapper solely for
source theorem application; the public receipt is
`std/hol/cardinality@1::map_length_schema`. The transitional descriptor accepts
only a named function with the inferred `A -> B` signature. A complete browser
example proves length preservation for `inc` without copying `map` or its proof
into the legacy engine, and collisions roll back both cardinality and List.

This slice also makes the policy boundary concrete: a proposition containing
`map(inc, xs)` is `hol`, even though `inc` is a first-order symbol, because
`map` itself consumes a function argument. Function-symbol schemas do preserve
FOL for theorems whose function is used only as an application head, but they
do not launder higher-order library operators. Consequently cardinality-map
assignments must opt into the `hol` profile; ordinary finite-cardinality
exercises can continue to use `HasCard` under `fol+induction`. This checkpoint
is 1,741,224 bytes natively and 1,234,290 bytes in raw Wasm.

The final `C.cardinality_transport` theorem now crosses the same boundary. Its
checked source template takes explicit forward and inverse function symbols and
an enumeration List, leaving the left-inverse, right-inverse, Nodup, and source
coverage facts as ordinary premises. The conclusion packages mapped Nodup,
length preservation, and target coverage exactly as the original theorem does.
Its stable adapter receipt is
`std/hol/cardinality@1::cardinality_transport_schema`; that receipt directly
pins the original transport theorem and the Map/List definitions visible in
the specialized statement. This checkpoint is 1,753,232 bytes natively and
1,244,116 bytes in raw Wasm.

The four supporting lemmas complete the source catalog:
`C.member_map_forward`, `C.member_map_reverse`,
`C.nodup_map_injective`, and `C.map_coverage_surjective`. Each has a checked
explicit-parameter adapter with its own stable `*_schema` receipt. Native tests
reuse both membership directions directly. The browser example proves the same
transport conclusion a second time from public Nodup, length, and coverage
lemmas, so the final theorem is convenient rather than opaque or indispensable.
The complete catalog checkpoint is 1,775,272 bytes natively and 1,262,322 bytes
in raw Wasm.

`std/hol/finite@1` now exposes the elimination side of its witness interface as
well: `has_card_nodup`, `has_card_length`, and `has_card_coverage` are distinct
checked aliases with stable package receipts. Importing finite and cardinality
under the same namespace composes their shared List aliases idempotently. The
vertical pilot uses that surface to derive `HasCard(map(f, xs), n)` from one
source `HasCard(xs, n)` hypothesis. A separate three-constructor source proof
forced compatibility replay to make legacy datatype no-confusion explicit
below disjunctions; it now constructs kernel-checked disjointness, reflexivity,
and connective evidence rather than treating legacy conversion as HOL
definitional equality. Native and browser tests pin the datatype exercise to
`fol+induction` and the genuine `map` exercise to `hol`. The checkpoint is
1,793,096 bytes natively and 1,281,435 bytes in raw Wasm.

Generated finite facts are not package aliases: `color_has_card` is owned by
the importing file even though its statement uses builtin `HasCard`; the new
`one_has_card` example follows that ownership rule. Likewise, graph packages
remain instance-scoped until an import can bind a particular checked
edge-symbol family.

## Driver and policy gates

Recognizing a logical import is not enough to authorize package source. The
end-to-end slice is complete only when:

- parser, editor, native CLI, and browser entry points select the same package
  identity and alias set;
- tactics resolve package symbols and submit their evidence to the HOL kernel;
- receipts retain builtin provenance and transitive fragment/trust metadata;
- assignment manifests allow the exact versioned package ID, not an ambient
  stronger library;
- unimported or colliding package names fail transactionally; and
- the exact legacy corpus remains unchanged for files without logical imports.

The alias catalog, parser-independent lowering, signature-only shadow-driver
import, stable package reporting, JSON, and exact assignment-manifest
allowlisting are complete. Contextual `nil` inference is also complete for
package applications; intentionally ambiguous standalone uses remain rejected.
Predicate-valued `All` arguments, explicit term ascriptions, all structural
predicate constructor laws, right identity, associativity, and length over
append and browser/editor verification are complete as well. The next source
slices continue with general generic declarations, cardinality aliases, richer
finite enumeration exercises, browser assignment-policy enforcement, and an
explicit decision about the low-level core-API cutover. The generic induction
principle itself is exposed through a receipt-backed theorem alias.
