# Namespace Design Note

Cetacea currently has one global top-level environment. Imports load every
declaration into that environment, so course files use suffixes such as
`add_comm_demo` to avoid colliding with library names. This note sketches the
design needed before implementing namespaces and qualified imports.

## Goals

- Let libraries publish stable qualified names such as `nat.add_comm` or
  `list.length_append`.
- Let teaching files reuse short names such as `add_comm` without colliding
  with imported libraries.
- Keep existing files working: plain `import path/to/file.ctea` should keep the
  current global-import behavior until the standard library and docs migrate.
- Preserve proof projections such as `h.left` and `h.right`.
- Keep local binders simple. Theorem parameters, `intro` names, `cases` names,
  lambda binders, and induction binders remain unqualified identifiers.

## Proposed Surface Syntax

Qualified references use dot-separated identifiers:

```text
exact nat.add_comm
rewrite -> eq.symm h
unfold set.Subset
simp [nat.add_zero_right]
```

Two declaration styles should be accepted:

```text
theorem nat.add_comm (n m : Nat) : add(n, m) = add(m, n) := by
  ...
```

and, as later sugar:

```text
namespace nat

theorem add_comm (n m : Nat) : add(n, m) = add(m, n) := by
  ...

end nat
```

Import aliases should be added only after qualified declaration lookup works:

```text
import std/nat.ctea as nat
```

The old unaliased `import std/nat.ctea` should continue to expose imported
names unqualified for compatibility.

## Internal Model

Introduce a top-level name representation rather than treating every name as a
plain `String`:

```rust
struct QualifiedName {
    parts: Vec<String>,
}
```

Local names should stay as `Name = String`. Only top-level declarations and
top-level references need `QualifiedName`.

`Env` can still store canonical names as strings at first (`"nat.add_comm"`),
but all lookup paths should go through resolver helpers:

- `resolve_theorem(ref, scope)`
- `resolve_sort(ref, scope)`
- `resolve_const(ref, scope)`, `resolve_func(ref, scope)`,
  `resolve_pred(ref, scope)`
- `resolve_formula_def(ref, scope)`, `resolve_term_def(ref, scope)`,
  `resolve_data_def(ref, scope)`

The resolver should receive a `Scope`:

```rust
struct Scope {
    current_namespace: Vec<String>,
    aliases: HashMap<String, Vec<String>>,
    legacy_unqualified_imports: bool,
}
```

For an unqualified reference, resolution should try local context first where
that kind has locals, then the current namespace, then legacy imported/root
names. For a qualified reference, resolution should use the canonical path and
should not be shadowed by local binders.

Ambiguous unqualified references should be errors with a targeted note:

```text
ambiguous theorem `add_comm`; use `nat.add_comm` or `my.add_comm`
```

## Parser Notes

The lexer already tokenizes `.` as its own symbol because proof projections use
the same character. Do not make dots part of identifiers globally. Instead, add
parser helpers for top-level references:

```text
qualified-name ::= ident ("." ident)*
local-name     ::= ident
```

Use `qualified-name` for declaration names and top-level references in terms,
formulas, tactics, theorem expressions, `unfold`, and `simp [...]`. Use
`local-name` for binders and hypothesis names.

Proof expressions need special care. Today `h.left` is parsed as base `h` plus a
projection. With qualified names, `eq.symm` must parse as a qualified base, not
as a projection from `eq`. A practical rule is:

- parse the longest dot-separated prefix as a possible qualified base;
- treat trailing `.left` and `.right` as projections only after resolution shows
  the base is a local proof or proof expression.

If that is too invasive for the first pass, reserve `left` and `right` as
forbidden namespace path segments in theorem names, but prefer resolver-based
disambiguation.

## Data Constructors

Data declarations introduce several top-level names: the data type and each
constructor. Namespaces should avoid forcing every constructor to repeat the
full prefix:

```text
namespace list

data List
| nil
| cons(Nat, List)

end list
```

This should canonicalize the type as `list.List` and the constructors as
`list.nil` and `list.cons`. Induction arms and `defrec` arms should accept
either the visible short constructor name or the qualified canonical name,
subject to the same ambiguity rules.

## Migration Plan

1. Done: allow dot-qualified declaration names and qualified references in the
   current single global environment, while preserving projection syntax such
   as `h.left`.
2. Done: add `namespace ...` / `end ...` blocks as declaration-prefix sugar.
3. Done: resolve sibling theorem and formula-definition names in proof/tactic
   contexts (`exact`, `apply`, `unfold`, and `simp [...]`) through the current
   namespace, while storing canonical theorem references in proof terms.
4. Add `QualifiedName` and resolver helpers while preserving existing
   unqualified behavior.
5. Add import aliases and ambiguity diagnostics.
6. Migrate standard-library declarations gradually, keeping compatibility
   aliases where needed.
7. Update book and course examples to use real qualified names instead of
   `_demo` suffixes when the imported library owns the short theorem name.

## Acceptance Tests

- A root file can import a library theorem `nat.add_comm` and also define its
  own theorem `add_comm`.
- Qualified references work in `exact`, `apply`, `rewrite`, `simp [...]`,
  `unfold`, term applications, predicate applications, and type positions.
- `h.left`, `h.right`, and `(h.left)` still parse and resolve as projections.
- Two imported files may both define `comm`; unqualified `comm` is ambiguous,
  while `nat.comm` and `set.comm` work.
- A data declaration in a namespace gives qualified constructor names and those
  names work in terms, `defrec` arms, and structural induction arms.
- Theorem search and outline display canonical qualified names while keeping
  imported/root status visible.
