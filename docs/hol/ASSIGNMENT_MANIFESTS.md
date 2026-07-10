# Assignment manifests

Status: experimental, native CLI only, on the `hol` migration branch.

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
]
allowed_axioms = []

required_theorem.exercise_3 = '(n : Nat) : add(n, 0) = n'
required_theorem.exercise_4 = 'forall n : Nat, n = n'
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

Permission does not raise the profile. For example, extensionality explicitly
allowed by a `fol` manifest is still rejected because that feature requires
HOL.

## Imports and trusted axioms

Each entry in `allowed_imports` is resolved relative to the manifest, then
canonicalized. Every filesystem import loaded transitively must appear in the
list; listing only the submission's direct imports is insufficient. Canonical
identity also prevents a different relative spelling or symlink from creating a
second capability.

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

## Frozen theorem signatures

A `required_theorem.NAME` entry requires a root declaration with exactly that
name and canonical signature. The signature contains the complete canonical
parameter telescope and proposition body, not merely the body:

```text
(A : Type) (x : A) : x = x
(P : Prop) (Q : Prop) : P -> Q -> P
True
```

Cetacea expands grouped source parameters into one canonical binder apiece.
Changing a parameter type, dropping a parameter, renaming a parameter, or
weakening the proposition therefore fails the signature check. The exact
signatures are available as `hol_shadow.theorems[].signature`:

```sh
cargo run -p cetacea_cli -- --hol-shadow --json starter.ctea
```

Copy those machine-produced values into the manifest. Signature text is
versioned with this experimental format; a future manifest version may replace
it with a structural fingerprint.

## Results and exit status

Text diagnostics identify the affected root declaration, import, or dependency.
With `--json`, the normal shadow receipt is supplemented by:

- `hol_policy`, including all independent permission dimensions;
- `hol_policy_violations`, with stable kinds such as `import`,
  `allowed_axiom`, `required_theorem`, and `theorem_signature`;
- `assignment_manifest`, recording the manifest path, version, declared
  imports and axioms, and frozen signatures.

Exit status is 0 only when ordinary checking, exact HOL shadow replay, the
teaching profile, and all manifest constraints succeed. A source or policy
failure exits 1. A missing or malformed manifest exits 2.

This layer still consumes the non-authoritative HOL shadow path while the legacy
checker remains the production authority. It is suitable for migration testing
and native grading experiments, not yet the browser/TUI assignment surface.
