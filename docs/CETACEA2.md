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
`--deny-axioms`, `--deny-classical`, `--deny-tactics simp,calc`,
`--json`, `--tier`, `--std DIR` (where `std/` imports resolve; defaults
to `lib/`), and the course flags described below. `--help` lists them
all.

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

## Course sections: allowed tactics and theorems

A course file names the sections of a class and says, for each one,
which tactics and which library theorems students may use. The checker
then reports anything outside the section's rules at the line where it
was written:

```text
error: hw2.ctea:5: the theorem `and_comm` is not available in the section `Chapter 2: Natural deduction`
  note: a theorem you prove in this file may always be used, so you can state and prove this fact yourself first
error: hw2.ctea:17: `simp` is not available in the section `Chapter 2: Natural deduction`
  note: tactics available here: intro, exact, apply, split, trivial, assumption, show, left, right, cases, contradiction, exfalso, have
```

These are course rules, not logic. The proof is still checked by the
kernel and still shows as `accepted theorem`; the file as a whole does
not pass, and the exit status is 1.

```sh
cargo run -p hol_cli -- --course courses/proofs-checked.json --section ch02 hw2.ctea
cargo run -p hol_cli -- --course courses/proofs-checked.json --list-sections
```

`courses/proofs-checked.json` has one section per book chapter and is
the place to start; copy it and edit. A section looks like this:

```json
{
  "id": "ch04",
  "title": "Chapter 4: Quantifiers",
  "description": "Shown to students next to the editor.",
  "extends": "ch03",
  "tier": "fol",
  "allow_tactics": ["exists", "obtain"],
  "allow_theorems": ["forall_*", "exists_*", "not_exists_to_forall_not"]
}
```

- `extends` builds on another section: its allow lists are added to, so
  a later section normally only lists what it unlocks. The tier is
  inherited unless the section sets one.
- `allow_tactics`, when present anywhere in the chain, makes the list
  exhaustive: any other tactic is refused. `show_goal` and `sorry` are
  always available (`sorry` is governed by `deny_sorry`).
- `deny_tactics` refuses specific tactics and wins over an allow list.
  Use it alone for "everything except `simp`".
- `allow_theorems` restricts which **imported** theorems may be cited.
  Entries are names or `*` patterns, matched against the full name and
  against the part after an import alias, so `add_*` covers
  `nat.add_comm`. An empty list means no library at all.
  `deny_theorems` refuses specific ones.
- Theorems proved in the submitted file are always usable. Closing the
  library therefore asks students to prove what they need, which is
  usually the point.
- `deny_sorry`, `deny_axioms`, `deny_classical` work as on the command
  line. `"advisory": true` turns the tactic and theorem rules into
  warnings for practice files.

A course file is validated when it is loaded: an unknown tactic name, a
missing parent, a cycle, or an unknown tier is an error, not a rule that
silently never fires.

What counts as using a theorem is what the proof actually resolved: a
hypothesis that happens to share a library theorem's name is not a
citation, and a proof that fails halfway still reports what it used up
to that point. The JSON report lists each theorem's `tactics` and cited
`theorems`.

To calibrate a section against material you already have, ask what a
set of files uses:

```sh
python3 scripts/section_usage.py docs/book/code/ch04-solutions.ctea
```

`scripts/check_course.sh` (run in CI) checks that every chapter's
examples and solutions pass under that chapter's section, so the sample
course cannot drift from the book.

The same rules are available without a course file: `--allow-tactics`,
`--deny-tactics`, `--allow-theorems` (`none` for an empty list),
`--deny-theorems`, and `--advisory`. Flags only ever restrict a section
further.

In the browser, the **Section** menu applies a section of the bundled
course (`web2/course.js`, generated from the course file by
`scripts/build_web_course.py`). A Section rules panel shows what is
available, suggested tactics never include anything the section
forbids, and the theorem library marks entries that are out of bounds.
Share links carry the section.

## What the kernel did: recorded derivations

The kernel is LCF style: only its primitive rules can build a theorem,
and no proof object is kept. It can still record what it did. While a
proof is checked, each tactic's primitive rule applications are logged,
together with the step at which `classical`, `sorry`, or an axiom first
entered the proof. The log is write-only for the kernel (no rule reads
it), so it adds nothing to what must be trusted.

```sh
cargo run -p hol_cli -- --derivation FILE.ctea
```

```text
derivation of lem:
  line  13  by_cases h : P      excluded_middle, or_elim   [introduces classical]
  line  14  left                or_left (+3 equality steps)
  line  15  exact h             3 equality steps
```

The introduction and elimination rules are listed by name, because they
are the rule table the course teaches; equational bookkeeping (`sym`,
`eq_mp`, instantiation) is counted. Rules a tactic tried on the way are
included, so this shows what the tactic did, not a minimal proof. With
`--json` the same data appears under `derivations`, and the browser's
Proof explanation panel shows it under each step of a finished proof.

The recording also makes three diagnostics point at a line instead of
at a whole theorem:

- under `--deny-classical`, the step that applied excluded middle or
  cited a classically proved theorem;
- under `--deny-sorry`, the step that left a goal open or cited a
  theorem whose own proof is unfinished;
- in a constructive file, the step where classical reasoning entered.

## Assignments

Write the skeleton you hand out, with `sorry` bodies, then generate a
manifest:

```sh
cargo run -p hol_cli -- --make-assignment "Homework 3" hw3_skeleton.ctea > hw3.json
```

The manifest pins each theorem's statement, the allowed imports, and a
policy (by default no `sorry` and no axioms). Add `--course FILE
--section ID` to write that section's tactic and theorem rules into the
manifest, so the assignment is graded under them wherever it is checked;
or edit the policy by hand (`"deny_tactics": ["simp"]`,
`"allow_theorems": ["add_*"]`, `"deny_classical": true`). Grade with:

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

The **Book** menu opens any of the book's companion files
(`web2/book.js`, generated from `docs/book/code` by
`scripts/build_web_book.py`, and checked for staleness in CI). Opening
one selects that chapter's section, and a student's work on each file
is kept separately in the browser's storage; "Start ... over" in the
same menu returns the open file to the book's version.

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
`modular`, `fun`, `list` (polymorphic `List A`), `finite`, `card`. Import
all of them with `import ../std/prelude.ctea` from a file next to the
repo, or `import std/prelude.ctea` in the browser.

### Counting

`HasCard(S, n)` says the set `S` has exactly `n` elements: some list
without repeats holds exactly the members of `S` and has length `n`.
To prove it for a concrete set, give the list. `card` proves what
counting arguments cite:

| Theorem | Says |
|---|---|
| `card_unique` | a set has one size |
| `card_subset_le` | a subset is no larger |
| `card_union_disjoint` | sizes of sets with no common element add |
| `card_le_of_injective` | an injection cannot land in a smaller set |
| `card_of_bijection` | a bijection carries the size across |
| `pigeonhole` | a function into a strictly smaller set is not injective |
| `pigeonhole_collision` | so two different inputs share an output (classical) |

Functions here are real functions `f : A -> B` with `MapsTo(f, S, T)`,
`InjectiveOn(f, S)` and `SurjectiveOn(f, S, T)`, so these need
`logic hol`. Everything except `pigeonhole_collision` is constructive.
`examples/counting.ctea` counts two small types and applies pigeonhole
to them.

### `decide`

`decide` closes a goal that has no unknowns by evaluating it. It
computes definitions and arithmetic, compares data constructors,
simplifies with `True` and `False`, and runs a quantifier over an
enumeration type (a `data` type whose constructors take no arguments)
through each of its values:

```text
theorem three_colors : HasCard(univ(Color), 3) := by
  unfold HasCard
  exists cons(red, cons(green, cons(blue, nil)))
  decide
```

Every step is a kernel rewrite, so the result is an ordinary
constructive proof, and `decide` adds nothing to what is trusted. When
the goal is false it says so and points at the false part:

```text
error: hw.ctea:4: theorem `t` failed: `decide` evaluated the goal, and it is false
  note: this part is false: `blue = red \/ blue = green`
  note: it fails when c = blue
```

When it cannot evaluate the goal it says why: a quantifier over a type
with no fixed list of values (`Nat`, `List A`), or a variable whose
value is unknown. It does not use hypotheses.

`decide` is a tactic name like any other in a course file. The sample
course's sections do not list it, so it is refused there until a section
adds it to `allow_tactics`. To do the same job by hand, `simp` takes the
`True`/`False` lemmas from `prop` as rules:
`simp [or_false_left, or_false_right, and_true_right, not_false]`.

## Checking the corpus

```sh
scripts/check_hol.sh
```

Every `.ctea` file under `lib/`, `examples/`, `docs/cs250/code`, and
`docs/book/code` is checked; negative files must reject every theorem.
