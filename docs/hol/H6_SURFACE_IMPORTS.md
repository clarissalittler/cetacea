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

Executable tests cover `List Nat`, contextual inference of polymorphic `nil`,
`Member(0, cons(0, nil))`, the corresponding `L.*` spellings, repeated imports,
coexistence with a monomorphic List, and collisions at both the first and a
later alias. The catalog is not yet invoked by `Command::Import`; therefore this
checkpoint does not expand the capabilities of any source file. Finite and
cardinality aliases will follow the same catalog after the List driver path is
end-to-end.

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

The alias catalog and parser-independent lowering step is complete. The
remaining sequence is logical import resolution in the shadow driver,
end-to-end tactic proof tests, then policy/JSON/Wasm exposure. Default
acceptance should not be enabled halfway through that sequence.
