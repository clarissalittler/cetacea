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
unavailable. Default checking rejects the logical import. Repeated imports are
idempotent. Finite and cardinality package IDs are recognized but reject with
an explicit surface-not-implemented diagnostic. The induction checkpoint
artifacts are 3,764,424 bytes for the native CLI and 1,368,943 bytes for Wasm.

Generated finite facts are not package aliases: `color_has_card` is owned by
the importing file even though its statement uses builtin `HasCard`. Likewise,
graph packages remain instance-scoped until an import can bind a particular
checked edge-symbol family.

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
Predicate-valued `All` arguments are complete as well. The next source slices
expand the checked equation catalog, followed by finite and cardinality aliases,
browser/editor verification, and an explicit decision about ordinary
(non-shadow) acceptance. The generic induction principle itself is now exposed
through a receipt-backed theorem alias.
