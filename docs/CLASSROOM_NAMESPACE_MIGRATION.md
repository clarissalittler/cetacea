# Classroom namespace migration

The book, CS250 course, and tutorial sources now use the qualified prelude.
Library declarations are explicit (`nat.add_comm`, `list.length`, `fun.Total`);
student declarations retain short names. Built-in operations such as `add`,
`mul`, `sub`, and `le` keep their existing names. The legacy prelude and the
compatibility examples that exercise it remain available.

## Scope and evidence

- Migrated 51 source files under `docs/book/code`, `docs/cs250/code`, and
  `docs/tutorial`, plus 20 companion chapters and introductory/status guidance.
- Captured checker results before changing the sources. Compared all 398 root
  declarations afterward: statements match under the recorded qualification and
  renaming, and acceptance status, axiom dependencies, and use of `sorry` match.
- Compared all 398 HOL root receipts separately: mode, status, statement and
  required fragments, and proof-feature sets are unchanged.
- Negative examples still reject their deliberately invalid theorems. The
  Chapter 10 declaration-collision example now explicitly redeclares
  `list.length`, since a student's own `length` is legal.
- Fixed the parser's distinction between qualified keyword prefixes and
  keywords: `fun.Total` is a qualified name; `fun x => ...` is still a lambda.
  Regression tests cover both forms and malformed inputs.
- Updated the frozen baseline's source hashes and qualified names only after
  the before/after semantic comparison. The baseline and HOL shadow gates
  continue to cover 74 files and 589 root declarations.
- Regenerated the browser example bundle from the canonical teaching sources.

The relevant checks are `cargo test --workspace`, `scripts/check_all.sh`,
`scripts/hol_baseline.py check`, `scripts/hol_shadow.py check`, and
`scripts/build_web_examples.py --check`. The browser regression harness also
loads the qualified structural-induction and function examples through the
production example menu.

Validation on 2026-09-04: all 551 Rust tests and all 94 source-file checks
passed, along with Clippy, formatting, feature-disabled compilation, the
release Wasm build, baseline/shadow checks, and browser-module tests. All 12
real-browser checks passed. Cursor positions outside a theorem show guidance
instead of incorrectly reporting a failed proof.

## Collision-driven declaration renames

Other `_demo` names remain descriptive example names; they are not required
for avoiding library collisions.

| Source | Previous name | Student declaration |
|---|---|---|
| `docs/book/code/ch01-examples.ctea` | `and_intro_demo` | `and_intro` |
| `docs/book/code/ch02-examples.ctea` | `modus_tollens_demo` | `modus_tollens` |
| `docs/book/code/ch02-examples.ctea` | `or_elim_demo` | `or_elim` |
| `docs/book/code/ch03-examples.ctea` | `dne_demo` | `dne` |
| `docs/book/code/ch03-examples.ctea` | `em_demo` | `em` |
| `docs/book/code/ch04-examples.ctea` | `exists_mono_demo` | `exists_mono` |
| `docs/book/code/ch06-examples.ctea` | `union_empty_right_demo` | `union_empty_right` |
| `docs/book/code/ch09-examples.ctea` | `add_comm_demo` | `add_comm` |
| `docs/book/code/ch09-examples.ctea` | `add_zero_left_demo` | `add_zero_left` |
| `docs/book/code/ch09-examples.ctea` | `add_zero_right_demo` | `add_zero_right` |
| `docs/book/code/ch09-examples.ctea` | `sub_self_demo` | `sub_self` |
| `docs/book/code/ch10-examples.ctea` | `append_cons_demo` | `append_cons` |
| `docs/book/code/ch10-examples.ctea` | `append_demo` | `append` |
| `docs/book/code/ch10-examples.ctea` | `length_demo` | `length` |
| `docs/book/code/ch11-examples.ctea` | `append_nil_demo` | `append_nil` |
| `docs/book/code/ch11-examples.ctea` | `length_append_demo` | `length_append` |
| `docs/cs250/code/01_propositional.ctea` | `and_intro_demo` | `and_intro` |
| `docs/cs250/code/01_propositional.ctea` | `em_demo` | `em` |
| `docs/cs250/code/01_propositional.ctea` | `modus_tollens_demo` | `modus_tollens` |
| `docs/cs250/code/01_propositional.ctea` | `or_elim_demo` | `or_elim` |
| `docs/cs250/code/05_sets.ctea` | `inter_comm_demo` | `inter_comm` |
| `docs/cs250/code/05_sets.ctea` | `powerset_mono_demo` | `powerset_mono` |
| `docs/cs250/code/05_sets.ctea` | `subset_refl_demo` | `subset_refl` |
| `docs/cs250/code/06_relations.ctea` | `eq_trans_demo` | `eq_trans` |
| `docs/cs250/code/07_structural_induction.ctea` | `length_append_demo` | `length_append` |
