# Assignment manifests

Status: experimental, native CLI only, on the `hol` migration branch.

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

This layer consumes the fail-closed compatibility path: ordinary checking and
complete HOL replay must both succeed. It is suitable for native grading
experiments, but assignment enforcement is not yet exposed in the browser or
TUI.
