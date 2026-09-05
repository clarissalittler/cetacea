# Assignment manifests

Status: experimental, native CLI only, on the `hol` migration branch.

The manifest parser and teaching-policy builder now live in
`cetacea_core::assignment`; the CLI uses that shared implementation. Manifests
are limited to 64 KiB of UTF-8 text. Syntax errors retain their physical source
line, and classical reasoning, axioms, and incomplete proofs remain independent
permissions. Grant validation, allowed imported axioms, required root signatures
and receipt restrictions now also use the shared core implementation. Browser
enforcement now has a core VirtualAssignment context for pinned libraries and
combined acceptance, with native parity tests; transport and assignment-result
presentation are still pending. Parsing a manifest or passing receipt restrictions alone does not
authorize a submission or its dependencies.

The finite-mathematics pilot contains two executable manifests:
[`finite_traffic.ctea-assignment`](pilot/finite_traffic.ctea-assignment) pins a
constructive `fol+induction` enumeration exercise, while
[`finite_bijection.ctea-assignment`](pilot/finite_bijection.ctea-assignment)
pins the genuinely higher-order generic-map exercise. The
[`pilot guide`](pilot/README.md) gives the corresponding starter and solution
commands.

The corresponding textbook sequence has solution policies alongside its code:
[`ch13-solutions.ctea-assignment`](../book/hol-code/ch13-solutions.ctea-assignment)
freezes the complete finite-enumeration exercise at `fol+induction`, while
[`ch14-solutions.ctea-assignment`](../book/hol-code/ch14-solutions.ctea-assignment)
permits the higher-order bijection/map sequence. An intentionally restrictive
[`ch14-solutions-fol.ctea-assignment`](../book/hol-code/ch14-solutions-fol.ctea-assignment)
is expected to reject only the mapped theorems; the book regression script
checks that policy failure as a teaching artifact. Chapter 15 adds
[`ch15-solutions.ctea-assignment`](../book/hol-code/ch15-solutions.ctea-assignment),
which accepts the constructive pigeonhole sequence at `hol`, and the
deliberately restrictive
[`ch15-solutions-fol.ctea-assignment`](../book/hol-code/ch15-solutions-fol.ctea-assignment).
The latter accepts member removal, list inclusion, and arithmetic but rejects
mapped-membership, injective-map preservation, and the final theorem's
transitive HOL dependency.
Chapter 16 adds
[`ch16-solutions.ctea-assignment`](../book/hol-code/ch16-solutions.ctea-assignment),
which authorizes the checked counting source module, its Nat source dependency,
and `std/hol/list@1`, while keeping all four finite-union exercises at
`fol+induction` with no classical, trust, or incomplete permission.

An assignment manifest fixes the logical fragment and the capabilities available
to a submission outside the theorem source itself. Invoke it with:

```sh
cargo run -p cetacea_cli -- \
  --assignment course/week05.ctea-assignment \
  submissions/alice.ctea
```

The manifest is trusted instructor input. A grader must keep it outside the
student-writable submission area and invoke Cetacea with the intended manifest;
the source file cannot select or relax it. Allowed library files are part of the
same trusted input and must likewise be read-only to students: version 1 pins
their canonical paths and declaration identities, not their content hashes.

## Version 1 format

The format is a deliberately small, fail-closed TOML-like subset. It accepts
scalar strings and booleans, arrays of strings, and repeatable
`required_theorem.<qualified-name>` entries:

```toml
version = 1
profile = "fol+induction"

allow_classical = false
allow_extensionality = false
allow_choice = false
allow_new_axioms = false
allow_incomplete = false

allowed_imports = [
  "../../std/prop.ctea",
  "../../std/nat.ctea",
  "std/hol/list@1",
]
required_imports = [
  "std/hol/list@1",
]
allowed_axioms = []

required_theorem.exercise_3 = '(?0 : Nat) : add(?0, 0) = ?0'
required_theorem.exercise_4 = 'forall ?0 : Nat, ?0 = ?0'
```

`version` and `profile` are required. All permission booleans default to
`false`; both arrays and the required-theorem set default to empty. Unknown
keys, duplicate keys or entries, unsupported versions, malformed values, and
unresolvable import paths are errors. Arrays may span lines and may have a
trailing comma. Comments begin with `#` outside strings.

Single-quoted strings are literal and are normally the convenient choice for
Cetacea formulas containing `/\` or `\/`. Double-quoted strings support
`\"`, `\\`, `\n`, `\r`, and `\t` escapes. This is not a general
TOML parser; accepting only the documented grammar is intentional.

## Policy dimensions

`profile` is one of `prop`, `fol`, `fol+induction` (or
`fol-induction`), and `hol`. It limits both the root statement and the
transitive proof receipt. The other permissions are independent:

- `allow_classical` permits classical proof features.
- `allow_extensionality` permits function and propositional extensionality.
- `allow_choice` permits choice.
- `allow_new_axioms` permits arbitrary trusted axioms declared by the checked
  source. This is deliberately stronger than `allowed_axioms`.
- `allow_incomplete` permits `sorry`, directly or through a dependency.

`allow_extensionality` and `allow_choice` are forward-compatibility switches:
no current elaboration or kernel path can emit the extensionality or choice
proof features, so no proof a student can write today is affected by either
key in either direction. They exist so the manifest format will not change
when those principles are introduced, and they are fail-closed until then. Do
not design a course around enabling them.

Permission does not raise the profile. For example, extensionality explicitly
allowed by a `fol` manifest is still rejected because that feature requires
HOL.

## Imports and trusted axioms

Each entry in `allowed_imports` is resolved relative to the manifest, then
canonicalized. Every filesystem import loaded transitively must appear in the
list; listing only the submission's direct imports is insufficient. Canonical
identity also prevents a different relative spelling or symlink from creating a
second capability.

Exact registered logical package IDs are retained as package identities rather
than filesystem paths. Their complete dependency closure is explicit too:
allowing `std/hol/finite@1` also requires `std/hol/list@1`, because the finite
surface exposes that checked dependency under the same source alias. The JSON
`hol_shadow.imported_packages` field supplies the exact set a manifest must
authorize.

Likewise, allowing `std/hol/cardinality@1` requires `std/hol/list@1`. The
current cardinality surface exposes `map`, which consumes a function argument;
its concrete uses are classified `hol`, so listing the package does not by
itself raise a `fol+induction` assignment's profile.

`allowed_imports` is an upper bound; it never requires that a permitted
library actually be loaded. `required_imports` is the corresponding lower
bound: every listed logical package must be imported by the submission, and
every listed file must be transitively loaded, or the check reports a
`required_import` violation. A required import is implicitly allowed, so an
entry does not have to appear in both arrays. Manifests whose required
theorems mention package declarations should require those packages; combined
with package-qualified signature comparison below, this closes the July 2026
audit bypass in which a submission rebuilt the required statement's spelling
from source-local declarations without importing the graded package at all.

`allowed_axioms` contains checked, possibly alias-qualified declaration names.
An entry must resolve to a trusted axiom from an imported file. A source-local
axiom with the same name is not accepted. The axiom is authorized only by
declaration identity, and only root proofs whose receipts actually depend on it
consume that permission. To permit arbitrary source-local axioms, an instructor
must make the much broader choice `allow_new_axioms = true`.

The checks compose:

- an allowed import cannot smuggle in HOL or classical reasoning because root
  receipts include transitive fragments and features;
- an allowed import does not automatically authorize its trusted axioms;
- an allowed axiom from a file that is not itself allowed still produces an
  import violation;
- unused imports are nevertheless rejected when they are outside the manifest,
  keeping the available checking environment fixed.

## Bundled standard-library sources

Native checkers ship the same standard-library sources as the browser. An
exact source import such as `std/nat.ctea` uses a filesystem copy when found,
and otherwise loads `builtin:std/nat.ctea`. Explicit source syntax
`import builtin:std/nat.ctea as nat` always uses the shipped copy. Its relative
dependencies also resolve within the bundle, without consulting student files.

Authorize these copies by their reserved identities:

```toml
version = 1
profile = 'fol+induction'
required_imports = ['builtin:std/nat.ctea']
required_theorem.homework = '(?0 : Nat) : add(?0, 0) = ?0'
```

Filesystem and bundled identities remain separate. Replacing a local
`std/nat.ctea` cannot satisfy a required bundled import. Unknown bundled names
are manifest errors. Every transitive bundled source and logical package must
be authorized: for example, bundled counting needs
`builtin:std/hol/counting.ctea`, `builtin:std/nat.ctea`, and
`std/hol/list@1`. Ordinary virtual files remain unauthorized by native
manifests. Bundled source contents are tied to the checker build; use the same
checker version for students and grading.

## Frozen theorem signatures

A `required_theorem.NAME` entry requires a root declaration with exactly that
name and canonical signature. The signature contains the complete canonical
parameter telescope and proposition body, not merely the body. The canonical
form is deliberately invariant under the two spelling choices a correct
submission is free to make:

- **Binders are positional.** Theorem parameters, quantifier variables,
  set-builder variables, and relation-lambda parameters print as `?0`, `?1`,
  ... in traversal order, so renaming a bound variable or parameter cannot
  fail a submission (and cannot be used to disguise a different statement).
- **Package references are package-qualified.** A reference to a logical
  package declaration prints as its stable identity, such as
  `std/hol/list@1.cons`, regardless of the import alias the source chose. A
  source-local declaration that merely imitates an alias spelling therefore
  cannot match a required signature built from package declarations.

```text
(?0 : Type) (?1 : ?0) : ?1 = ?1
(?0 : Prop) (?1 : Prop) : ?0 -> ?1 -> ?0
std/hol/finite@1.HasCard(std/hol/list@1.cons(red, std/hol/list@1.nil), 1)
True
```

Cetacea expands grouped source parameters into one canonical binder apiece.
Changing a parameter type, dropping a parameter, or weakening the proposition
fails the signature check; renaming parameters or choosing another import
alias does not. Names that resolve to declarations in the submission or its
allowed source-file imports (such as the student-declared `red` above) print
as their declared qualified names, so a manifest still pins those exact
names — source-module aliases, unlike package aliases, remain part of the
signature for now.

Do not hand-write signatures. The exact canonical values are available as
`hol_shadow.theorems[].signature`:

```sh
cargo run -p cetacea_cli -- --hol-shadow --json starter.ctea
```

Copy those machine-produced values into the manifest (a `sorry`-stubbed
starter emits them too). Signature text is versioned with this experimental
format; a future manifest version may replace it with a structural
fingerprint.

## Results and exit status

Text diagnostics identify the affected root declaration, import, or dependency.
With `--json`, the normal shadow receipt is supplemented by:

- `hol_policy`, including all independent permission dimensions;
- `hol_policy_violations`, with stable kinds such as `import`,
  `required_import`, `allowed_axiom`, `required_theorem`, and
  `theorem_signature`;
- `assignment_manifest`, recording the manifest path, version, declared
  imports (allowed and required) and axioms, and frozen signatures.

Exit status is 0 only when ordinary checking, exact HOL shadow replay, the
teaching profile, and all manifest constraints succeed. A source or policy
failure exits 1. A missing or malformed manifest exits 2.

This layer consumes the fail-closed compatibility path: ordinary checking and
complete HOL replay must both succeed. It is suitable for native grading
experiments, but assignment enforcement is not yet exposed in the browser or
TUI.


## Exact checked-theorem grants

`allowed_theorems` grants a specific public export of a versioned logical
package, independently of the student's import alias:

```toml
allowed_theorems = ["std/hol/cardinality@1::map_length"]
```

The package and its dependencies must still be authorized by `allowed_imports`.
The named export must be an imported, checked theorem without axiom or
incomplete dependencies. Unknown exports, function definitions, local
lookalikes, wildcard names, and unversioned names are rejected. Grants use the
public export name, not an internal schema or kernel name.

A grant exempts that supplied lemma's inherited fragment requirements when
checking a client proof. It does not change any receipt or reported required
fragment, exempt the client's own statement or proof features, or authorize
classical reasoning, extensionality, choice, axioms, or incomplete proofs.
Those restrictions remain independent and transitive. For example, a
first-order client can use the generic `map_length` lemma under a
`fol+induction` policy with this grant, but a root theorem whose own statement
is higher-order is still rejected.

Source-library exports use the same syntax:

```toml
allowed_theorems = [
  "helpers.ctea::lemma",
  "builtin:std/hol/pigeonhole.ctea::pigeonhole",
]
```

Filesystem paths resolve relative to the manifest and are canonicalized. Bundled
identities select the shipped source, not a same-named local file. Export names
are the names declared in that library, including any declared namespace but
excluding the caller's import alias. Grants do not authorize imports implicitly:
keep the library and its transitive imports in `allowed_imports`. Multiple
aliases of the same export receive the same permission; another file's
same-named theorem does not. A missing, rolled-back, untrusted, or incomplete
export makes the grant invalid.

The checked client and manifest in `docs/hol/pilot/pigeonhole_client.ctea` and
`pigeonhole_client.ctea-assignment` demonstrate a `fol+induction` submission
using the supplied constructive pigeonhole theorem. Run:

```sh
cargo run -p cetacea_cli -- --assignment docs/hol/pilot/pigeonhole_client.ctea-assignment docs/hol/pilot/pigeonhole_client.ctea
```

The client fails the dependency-fragment policy without its exact grant. Its
receipt still records the higher-order dependencies. The chapter-15 solutions
file itself contains higher-order helper statements, so checking that entire
file under a first-order profile is still correctly rejected. Use the client
workflow when the helper library is instructor-supplied; use the HOL profile
when students are proving those higher-order helpers themselves.

The positive witness example in
[`pigeonhole_collision.ctea`](examples/pigeonhole_collision.ctea) has a
[companion policy](examples/pigeonhole_collision.ctea-assignment) granting
`builtin:std/hol/pigeonhole_classical.ctea::pigeonhole_collision` and setting
`allow_classical = true`. The same policy with `allow_classical = false`
rejects `some_collision` for its classical proof feature, even though the
library theorem is granted. Its explicit concrete pair remains constructive.
