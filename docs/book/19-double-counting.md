# Chapter 19 — Counting Twice

Companion files: [examples](hol-code/ch19-examples.ctea),
[exercises](hol-code/ch19-exercises.ctea),
[solutions](hol-code/ch19-solutions.ctea),
[mistakes](hol-code/ch19-mistakes.ctea),
[assignment policy](hol-code/ch19-solutions.ctea-assignment), and
[browser assignment](hol-code/ch19.ctea-task).

A table can be added by rows or by columns. That small observation proves a
useful graph theorem: the sum of the vertex degrees is twice the number of
edges. The proof has to say what an edge contributes at a vertex, including
what happens to loops and repeated edges.

This chapter uses the lists of Chapter 13, the finite sums of Chapter 17, and
list induction. Use the `hol` profile. The proofs are constructive: no new
axioms, classical cases, or unfinished proofs are needed.

## 19.1 Start with a table

Consider two bridge occurrences between `home` and `away`, and a loop at `home`.
An entry counts how many ends of that edge occur at that vertex:

| Edge occurrence | home | away | Row total |
| --- | ---: | ---: | ---: |
| First bridge | 1 | 1 | 2 |
| Second bridge | 1 | 1 | 2 |
| Loop at home | 2 | 0 | 2 |
| Column total | 4 | 2 | 6 |

Every row contributes two. Each column gives a vertex degree. The same six
incidences appear in both totals. A loop has two ends at its single vertex;
counting it once would make the first column total incorrect.

The example represents the two bridge occurrences by repeating `bridge` in an
edge list. Lists count occurrences. They do not silently remove duplicates.
A set-based interpretation needs a checked enumeration and its own evidence.
The endpoint-support theorem requires a duplicate-free vertex enumeration.

## 19.2 Express the two counting orders

```cetacea
import std/hol/matrix@1 as M
import builtin:std/hol/double_counting.ctea as D
```

For `w : A -> B -> Nat`, rows have type `A` and columns have type `B`.
The two types need not be the same.

| Expression | What it counts |
| --- | --- |
| `M.row_sum(w, a, ys)` | One row, over the listed columns. |
| `M.column_sum(w, xs, b)` | One column, over the listed rows. |
| `M.rows_total(w, xs, ys)` | All row sums. |
| `M.columns_total(w, xs, ys)` | All column sums. |

`D.double_counting` proves equality of the last two expressions for arbitrary
lists. It does not require distinct entries: a repeated row or column is
counted on both sides. Empty dimensions have total zero.

For a numerical table with different row and column types, see the
[workshop-signup example](../hol/examples/double_counting.ctea).

## 19.3 Read the recursion equations

Each operator has an empty-list law ending in `_nil` and a nonempty-list law
ending in `_cons`. For example:

```text
M.row_sum(w, a, M.nil) = 0
M.row_sum(w, a, M.cons(b, ys)) = add(w(a, b), M.row_sum(w, a, ys))
```

The second equation separates the first entry from the remaining row. The
column equation does the same along a column. For concrete calculations,
rewrite with these laws before using `refl`. Source `simp` alone does not
compute these package functions.

To prove a table identity, choose the list whose first entry you want to
separate. In Exercise 2, induct over the columns of a table with no rows.
In Exercise 3, also induct over the columns: adding one row adds one entry
to each column. The induction step rearranges four contributions using
`W.add_interchange`:

```text
add(add(a, b), add(c, d)) = add(add(a, c), add(b, d))
```

Think of the four quantities as the new entry, the old column total, the
remaining new row, and the remaining old table. Matching those quantities
to the equation explains the rearrangement.

## 19.4 From table entries to degrees

```cetacea
import builtin:std/hol/handshake.ctea as H
```

The generic theorem `H.handshake` takes `incidence : Edge -> Vertex -> Nat`,
`degree : Vertex -> Nat`, and edge and vertex lists. It asks for two facts:

1. Each listed edge has row sum 2 over the vertex list.
2. Each listed vertex's degree equals its incidence-column sum over the edge list.

It concludes:

```text
S.sum(C.map(degree, vertices)) = mul(C.length(edges), 2)
```

The names `incidence` and `degree` do not establish these facts. In the worked
example, endpoint-support proofs establish the row sums. `H.row_as_sum`
connects those unary endpoint contributions to a binary incidence row. The
proof of `degree_counts` checks the columns against the declared degrees.
Only then does `handshake_total` apply the generic theorem.

The shorter proof behind that theorem has three steps: express the degree
sum as a column total with `H.columns_as_degrees`, switch to row totals with
`D.double_counting`, and use `H.rows_constant` because each edge contributes 2.
Exercise 4 asks you to assemble those steps. The library also permits using
`H.handshake` directly; the assignment checker verifies the theorem and its
trust conditions, not which pedagogical proof method you chose.

## 19.5 Exercises and feedback

| Exercise | Task | Useful starting point |
| --- | --- | --- |
| `ex19_1` | An empty row totals zero. | Apply `M.row_sum_nil`. |
| `ex19_2` | A table with no rows has column total zero. | Induct on `ys`. |
| `ex19_3` | Adding a row adds its row sum to the column total. | Induct on `ys`; use interchange in the cons case. |
| `ex19_4` | Derive the degree-sum identity from the two incidence premises. | Introduce both premises and follow the three steps above. |

Keep the theorem names and statements and replace each `sorry`. The starter
is intentionally incomplete; it must fail the assignment until all four
proofs are complete. The assignment rejects new axioms, incomplete proofs,
and classical reasoning, and checks the exact required theorem signatures.

For native grading from the repository root:

```sh
cargo run -q -p cetacea_cli -- --assignment docs/book/hol-code/ch19-solutions.ctea-assignment docs/book/hol-code/ch19-exercises.ctea
```

In the browser, open the exercise file and load `ch19.ctea-task` as the
assignment. The example is also available in the example selector. Save or
export your work before replacing the current document with another example.

The mistakes file deliberately tries to make an empty row total one, add an
extra incidence when switching counting order, and prove the handshake
identity without its edge-contribution premise. Each proof must be rejected.
The separate regression tests also reject a loop counted once and a removed
edge occurrence with unchanged degrees.
