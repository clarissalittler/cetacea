# Cetacea 2: using the new checker

This is the short guide to the HOL-based rewrite. The language guide in
`docs/USAGE.md` still describes the surface syntax, which is unchanged
except for the items in section 9 of `docs/HOL_REWRITE_PLAN.md`.

## Tiers

A file declares its logic tier on its first line, or inherits the
default from the CLI (`--tier`) or the browser's Logic menu.

```text
logic fol        -- propositional and first-order logic, sets (default)
logic fol_nat    -- adds Nat, numerals, + * - <= <, induction, calc
logic hol        -- adds data types, functions as values, funext
```

A tier-1 file is a valid tier-3 file. Features from a higher tier are
rejected with a message naming the line to add.

## Command line

```sh
cargo run -p hol_cli -- FILE.ctea
cargo run -p hol_cli -- --tier fol_nat FILE.ctea
cargo run -p hol_cli -- --strict --json FILE.ctea
```

Flags: `--strict` (no `sorry`, no root axioms), `--deny-sorry`,
`--deny-axioms`, `--deny-classical`, `--deny-tactics simp,decide`,
`--json`, `--tier`, `--std DIR` (where `std/` imports resolve; defaults
to `lib/`).

Status lines are the familiar ones:

```text
accepted theorem and_comm (constructive)
incomplete theorem hw2 (constructive; uses sorry)
accepted theorem sub_self (constructive; axioms: modeq_zero_to_divides)
trusted axiom modeq_zero_to_divides
failed theorem converse_error
```

Every status is computed from kernel tags, so a proof cannot hide a
`sorry`, an axiom, or a classical step.

## Assignments

Write the skeleton you hand out, with `sorry` bodies, then generate a
manifest:

```sh
cargo run -p hol_cli -- --make-assignment "Homework 3" hw3_skeleton.ctea > hw3.json
```

The manifest pins each theorem's statement, the allowed imports, and a
policy (by default no `sorry` and no axioms). Edit it to add
`"deny_tactics": ["simp"]` or `"deny_classical": true`. Grade with:

```sh
cargo run -p hol_cli -- --assignment hw3.json --json submission.ctea
```

A submission that changes a statement, drops a theorem, or imports a
file outside the allowed list fails with an `assignment violation`
line, and the JSON carries an `assignment` object with each theorem's
status and `complete: true|false`.

To hand the assignment out through the browser, open the skeleton in
the web UI, and share it: the link carries the source, and if you add
the manifest as `#assignment=...` (see `scripts/`), the UI shows an
Assignment panel with each required theorem's status.

## Browser

`web2/` runs entirely in the browser. It checks as you type, shows the
goal at the cursor, marks errors inline, explains each step, searches
the library, and offers tactic suggestions that were run before being
shown. Share creates a link that reproduces the file. Save downloads
it. The Logic menu sets the default tier for files without a `logic`
line.

## Countermodel feedback

When a proof fails, the new checker can search small first-order worlds.
Try **Quantifier order: a counterexample** in the browser's example menu:

```text
sort Person
theorem quantifier_swap (R : Person -> Person -> Prop)
  : (forall y : Person, exists x : Person, R(x, y))
    -> exists x : Person, forall y : Person, R(x, y) := by
  show_goal
```

A two-element world refutes this implication: for example, with
`R = {(a, b), (b, a)}`, every `y` has a witness `x`, but no single `x`
works for every `y`. The diagnostic lists domains, constant assignments,
true predicate tuples (all others are false), and total function tables.
An open-goal counterexample instead satisfies every current hypothesis
and falsifies the goal; it is labeled as a wrong proof step, not a false
original statement. Feedback appears in CLI text, JSON, and the browser.

The search supports abstract sorts, type parameters, equality, ordinary
connectives, quantifiers over objects, and uninterpreted constants,
predicates, and functions. Different sorts can have different nonempty
domains. It tries domains of one to three elements for up to three sorts,
with limits of 12 symbols, three arguments per symbol, 16 table cells,
32,768 candidate interpretations, and 250,000 evaluation steps per search.
Compilation is also bounded (512 nodes, depth 64).

This is diagnostic search, not a proof rule or a decision procedure.
No countermodel found means **unknown**, not valid. Definitions, sets,
datatypes, arithmetic, and higher-order binders are deliberately declined
by this search; the separate arithmetic feedback remains available.
Supported declared axioms constrain candidate worlds. Any unsupported
axiom, including a polymorphic axiom, disables first-order search rather
than being ignored. In particular, the full prelude currently imports an
arithmetic axiom: use a standalone file or only the axiom-free `prop`,
`fol`, and `eq` libraries for these quantifier exercises.

## Libraries

`lib/` is the standard library: `prop`, `fol`, `eq`, `set`, `nat`,
`modular`, `fun`, `list` (polymorphic `List A`), `finite`. Import all of
them with `import ../std/prelude.ctea` from a file next to the repo, or
`import std/prelude.ctea` in the browser.

## Checking the corpus

```sh
scripts/check_hol.sh
```

Every `.ctea` file under `lib/`, `examples/`, `docs/cs250/code`, and
`docs/book/code` is checked; negative files must reject every theorem.
