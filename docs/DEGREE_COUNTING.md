# Degree counting and the handshake theorem

The [checked edge-list example](hol/examples/edge_degrees.ctea) represents
undirected multigraphs on three named vertices: north, south, and west. Its six
edge constructors cover each pair of distinct vertices and a loop at each
vertex. A graph is a list of these edges. Repeated entries represent parallel
edge occurrences, so no duplicate-free premise is imposed.

`incidence(e, v)` counts the endpoints of edge `e` at vertex `v`. A non-loop
contributes one at each of its two vertices. A loop contributes two at its
single vertex. `degree(edges, v)` recursively adds those contributions over
the edge list; degrees are computed from the graph rather than supplied as
unrelated numbers.

The example proves, for every edge list in this representation,

```text
degree(edges, north) + degree(edges, south) + degree(edges, west)
  = 2 * length(edges)
```

The formal theorem writes multiplication as `mul(length(edges), 2)`. Its
induction adds one edge, separates that edge's contributions from the tail
degrees, and uses `edge_has_two_ends`. Loops and repeated edges are included.
The example also computes a loop's degree and the contribution of parallel
copies; regression tests reject counting either as one.

This is a checked three-vertex instance of the handshake theorem. The generic
incidence/degree interface and its connection to endpoint evidence are described
below. The directed path library has different assumptions and does not
automatically provide undirected-graph evidence.

## Reusable finite-sum laws

`builtin:std/hol/weighted_sums.ctea` supplies constructive laws over an
arbitrary list type. It uses the shared cardinality package's `map` operation
and the checked natural-number sum library.

| Law | Premise and conclusion |
| --- | --- |
| `sum_map_add` | If `h(x) = f(x) + g(x)` for every `x`, then the sum of `h` over a list equals the sum of `f` plus the sum of `g`. |
| `sum_map_constant` | If `f(x) = k` for every `x`, then its sum over a list equals the list length times `k`. |

The original laws remain available as wrappers around stronger list-relative
versions:

| Law | Evidence required only for `x` with `C.Member(x, xs)` |
| --- | --- |
| `sum_map_add_on` | `h(x) = add(f(x), g(x))` splits the total. |
| `sum_map_constant_on` | `f(x) = k` gives list length times `k`. |
| `sum_map_congr_on` | `f(x) = g(x)` gives equal totals. |

These laws count list occurrences, including duplicates. Their pointwise
premises are required; the checker does not assume them from function names.
Values outside the list are unrestricted. The
[selected-contributions example](hol/examples/selected_contributions.ctea)
uses a function that contributes 2 on selected items and 99 outside them.
It proves the selected total, agreement with another function that differs
outside the list, and the separate contribution of two selected copies.

`builtin:std/hol/finite_weighted_sums.ctea` connects these laws to the existing
finite-set interface. `sum_on_set_constant` takes `HasSize(V, xs, n)` and
constant contribution `k` on `V`, and proves the total is `mul(n, k)`.
`sum_on_set_congr` takes agreement on `V` and proves equal totals on `xs`.
The checked `HasSize` premise supplies list coverage and the stated size; it
also requires a duplicate-free enumeration. The example includes a singleton
set with a checked size and total. A repeated list can be counted as a list,
but cannot be presented as that set's duplicate-free enumeration.

The module also exposes the arithmetic rearrangement `add_interchange` used
by the degree proof. Passing arbitrary functions to `map` requires `hol`;
these proofs add no axioms, classical reasoning, or incomplete dependencies.

Check the library and example with:

```sh
cargo run -p cetacea_cli -- --hol-profile hol std/hol/weighted_sums.ctea
cargo run -p cetacea_cli -- --hol-profile hol docs/hol/examples/edge_degrees.ctea
```

The work also fixed a replay failure for a rewrite such as
`a = mul(n, 2)` inside `add(2, a)`. If direct rewrite reconstruction fails, the
HOL elaborator can use its checked arithmetic conversions to reconcile the
expanded multiplication. This retains the equality proof and its dependencies;
it does not allow an unchecked simplification to certify the result.

The selected-contributions example exposed stack overflows while processing
its value 99 and reporting a false proof. Successor normalization now walks
chains iteratively in the teaching checker. The kernel uses an explicit work
stack for application and lambda normalization, with depth and reduction-step
guards retained. Regressions cover the positive and rejected examples, beta
reduction under a 99-constructor chain, and recovery after a normalization
limit error. This does not complete the separate compact-Nat or whole-check
resource-budget work.

## Enumeration order

`builtin:std/hol/weighted_enumerations.ctea` now proves that a finite-set total
is independent of the order of its checked enumeration:

- `remove_weighted_member` removes a member from a duplicate-free list and
  proves that its weight plus the remainder's total equals the original total.
  It preserves the remaining membership evidence and uses no decidable
  equality assumption.
- `sum_same_members` proves equal totals for two duplicate-free lists with
  equivalent membership predicates.
- `sum_enumeration_independent` accepts two `HasSize` proofs for the same set
  and proves that either enumeration gives the same weighted sum. The caller
  need not supply an equality between the two reported sizes.

The [reordered-totals example](hol/examples/reordered_totals.ctea) enumerates a
set in opposite orders, checks both enumerations, and derives the same total
of 7. Its list names are ordinary term abbreviations. Regressions reject an
extra duplicate and an enumeration that omits a set member; mere agreement
about which distinct values occur is not enough without duplicate-freeness.

The example also fixed a rewrite-replay gap: a known proof could retain a
named-list abbreviation after the rewrite tactic expanded it. The teaching
checker now compares exposed term forms in this fallback, and HOL constructs
and checks its equality-elimination motive using definitional equality. Tests
cover both rewrite directions through opaque functions and reject a changed
numerical conclusion. Equality reconstruction has its own helper to reduce
stack use in deeply nested source proofs.

This establishes a prerequisite for treating a degree sum as a property of
the vertex set. The incidence API and handshake proof below count list
occurrences; enumeration independence is a separate result.

## One edge on an arbitrary vertex type

`builtin:std/hol/endpoint_sums.ctea` proves the endpoint-counting step for an
arbitrary type `A` and a duplicate-free vertex list:

| Law | Required evidence and conclusion |
| --- | --- |
| `sum_single_support` | A listed point has weight 1 and every other listed point has weight 0; the total is 1. |
| `sum_absent_support` | The supported point is absent and every listed point has weight 0 away from it; the total is 0. |
| `sum_endpoint_pair` | Both endpoints occur in the list, their indicator functions satisfy the preceding support conditions, and incidence is their sum on listed vertices; the total incidence is 2. |

The endpoints in `sum_endpoint_pair` need not be distinct. A loop has two
endpoint incidences at the same vertex. The supplied functions come with
explicit evidence about their values; their names alone establish nothing.
No equality decision procedure, classical reasoning, or new axiom is needed.

The [endpoint example](hol/examples/endpoint_contributions.ctea) checks an
ordinary edge, a loop, and an absent endpoint. `finite` discharges concrete
premises over its two-vertex datatype. The imported theorem itself is generic
and uses constructive removal and weighted-sum proofs, not finite search over
that particular type. Tests reject omitting an endpoint and counting a loop
only once.

These laws establish the contribution of each individual edge for any suitable
vertex enumeration. The general double-counting identity and handshake
interface below connect these endpoint laws to vertex degrees.

The example also uses `vertices := vertices`: the first name is a theorem
parameter and the second is the caller's named list. Reconstructing an imported
theorem's parameter context now permits this ordinary call-site name overlap.
Duplicate binders and declaration-time name collisions are still checked.

## Row and column sums and general double counting

`crates/cetacea_core/src/hol/matrix_library.rs` now constructs four polymorphic
operators for a contribution function `w : A -> B -> Nat`:

| Operator | Meaning |
| --- | --- |
| `row_sum(w, a, ys)` | Sum one row over the listed columns. |
| `column_sum(w, xs, b)` | Sum one column over the listed rows. |
| `rows_total(w, xs, ys)` | Add the row sums. |
| `columns_total(w, xs, ys)` | Add the column sums. |

All four use checked structural recursion and have checked empty-list and
cons equations. Lists count repeated entries separately. Tests check an
asymmetric 2-by-3 matrix, empty dimensions, repeated entries, distinct row and
column types, rejection of swapped lists and false totals, and atomic rollback
when installation fails. The laws introduce no axioms or incomplete proofs.

Import `std/hol/matrix@1 as M` for these operators and their eight computation
laws. The package shares List identity with `std/hol/list@1`, so lists from
separate aliases can be used together. Alias binding independently checks
source schemas against the kernel laws; failed imports roll back atomically.

`builtin:std/hol/double_counting.ctea` supplies the constructive theorem:

```text
theorem double_counting (A B : Type) (w : A -> B -> Nat)
  (xs : M.List A) (ys : M.List B) :
  M.rows_total(w, xs, ys) = M.columns_total(w, xs, ys)
```

The proof uses list induction, the computation laws, and addition interchange.
It needs neither duplicate-free lists nor a decidable equality operation:
occurrences are counted on both sides. It introduces no axioms or unfinished
proofs. The generic theorem requires the `hol` profile.

The [workshop signup example](hol/examples/double_counting.ctea) counts a
2-by-3 table by days and by subjects, obtaining 21 either way. It demonstrates
individual row and column sums, shared list aliases, the generic theorem, and
repeated entries. For concrete computation, rewrite with the package's `_cons`
and `_nil` equations before `refl`; these package functions are not evaluated
by source `simp` alone.

## Generic handshake identity

`builtin:std/hol/handshake.ctea` exports `handshake` for arbitrary edge and
vertex types, a binary natural-number incidence function, a unary degree
function, and finite lists of edges and vertices. Its two premises are:

- Every listed edge has row sum 2 over the listed vertices.
- Every listed vertex has degree equal to its incidence-column sum over the
  listed edges.

The conclusion is `sum(map(degree, vertices)) = mul(length(edges), 2)`.
The proof combines general double counting with a constant-row-sum argument.
It is constructive and introduces no axioms or incomplete proofs. All premises
are restricted to listed elements; unlisted values need no constraints.

`row_as_sum` connects a binary incidence row to a named unary contribution
function that agrees on listed vertices. This lets a client discharge the
first premise using `endpoint_sums.sum_endpoint_pair`. `columns_as_degrees`
connects a named degree function to column totals. `rows_constant` also works
for contributions other than 2.

The [handshake example](hol/examples/handshake.ctea) contains two bridge
occurrences and one loop at `home`. Endpoint-support proofs establish each
edge's contribution. The checked degrees are 4 at `home` and 2 at `away`,
and the generic theorem gives six incidences. Negative tests reject degree 3
at `home` and deleting a bridge occurrence while retaining the old degrees.
Core, Wasm, and browser grading tests cover the example.

The theorem counts list occurrences. A set interpretation needs separate
checked enumeration evidence; duplicate-free vertices are a premise of the
endpoint-support theorem, not a hidden assumption of the incidence identity.
An arbitrary incidence function does not become an undirected graph merely
by its name: the client must supply the stated evidence. [Chapter 19](book/19-double-counting.md) supplies the teaching unit, exercises,
solutions, deliberate mistakes, and a native/browser assignment policy.
