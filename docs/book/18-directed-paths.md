# Chapter 18 — Joining Directed Paths

Companion files: [examples](hol-code/ch18-examples.ctea),
[exercises](hol-code/ch18-exercises.ctea),
[solutions](hol-code/ch18-solutions.ctea),
[mistakes](hol-code/ch18-mistakes.ctea),
[assignment policy](hol-code/ch18-solutions.ctea-assignment), and
[browser assignment](hol-code/ch18.ctea-task).

Suppose you can travel from home to a junction, then from the junction to
campus. Joining those journeys sounds obvious. A proof has to keep track of
which roads are available, which vertices each journey visits, and where the
two journeys meet.

By the end of this chapter, you should be able to build and take apart an
explicit directed path, and prove that two paths with a common endpoint can
be joined. The induction pattern comes from Chapter 11. Chapter 13 supplies
the generic list notation.

## 18.1 What the list records

Import the checked graph package:

```cetacea
import std/hol/graph@1 as G
```

It supplies the shared list type and constructors as `G.List A`, `G.nil`, and
`G.cons`. You can also import `std/hol/list@1 as L`; both aliases refer to the
same list type.

A graph is a vertex type `A` together with a relation `E : A -> A -> Prop`.
`E(a, b)` says there is a directed edge from `a` to `b`. It does not imply an
edge from `b` to `a`.

`G.ValidPath(E, xs, a, b)` says that `xs` records a journey from `a` to `b`.
The list contains vertices visited **after** the start, including the finish.
For the journey home → junction → campus, the list is
`G.cons(junction, G.cons(campus, G.nil))`. The start, home, is a separate
argument.

Repeated vertices and edges are allowed. Graph theory usually calls such a
journey a **walk**. Despite the library name `ValidPath`, this predicate does
not require a simple path. It also makes no finiteness, symmetry, or no-loop
assumption about the graph.

## 18.2 Two equations do the work

| Law | What it tells you |
| --- | --- |
| `G.path_nil` | `G.ValidPath(E, G.nil, a, b)` iff `b = a`. |
| `G.path_cons` | `G.ValidPath(E, G.cons(h, t), a, b)` iff `E(a, h)` and `G.ValidPath(E, t, h, b)`. |

An empty path stays where it started. A nonempty path takes one edge from
`a` to its head `h`, then follows its tail from `h` to `b`. Notice how the
start changes when we move to the tail.

Cetacea represents an equivalence as its two implications. The `.left`
projection takes a path apart; `.right` builds one from the required evidence.
For example:

```cetacea
theorem stay (A : Type) (E : A -> A -> Prop) (a : A) :
  G.ValidPath(E, G.nil, a, a) := by
  apply (G.path_nil {A := A; E := E; a := a; b := a}).right
  refl
```

Read the worked road example next. Each leg uses `path_cons.right`, proves
one road exists, and finishes with an empty path at that road's destination.
The example uses `finite` only to check concrete road facts on its three
vertices. It does not search for a path.

## 18.3 Joining lists and journeys

The bundled source library provides the concatenation theorem:

```cetacea
import builtin:std/hol/paths.ctea as P
```

`P.path_append` says that a path along `xs` from `a` to `b`, followed by a path
along `ys` from `b` to `c`, gives a path along `G.append(xs, ys)` from `a` to
`c`. The first list already includes `b`. The second lists vertices after
`b`, so concatenation does not insert an extra copy of the joining vertex.

The midpoint must match. Having a path from home to a junction and a path
from a different station to campus is not enough. The checker rejects that
attempt even when the proposed conclusion names the desired destination.

You can read the complete [source proof](../../std/hol/paths.ctea). It uses
list induction on `xs`:

- **Empty list:** the first path gives `b = a`. Appending `ys` to the empty
  list leaves `ys`, and the second path has the required endpoints after
  rewriting that equality.
- **Head and tail:** take the first path apart into `E(a, h)` and a tail path
  from `h` to `b`. The induction hypothesis joins that tail to `ys`. Put the
  first edge back using `path_cons.right`.

Keep `a`, `b`, and `c` universally quantified until **after** starting
induction. The recursive step needs the induction hypothesis with start
`h`, which differs from the original start `a`. Introducing and fixing all
endpoints too early gives a weaker induction hypothesis.

## 18.4 Your turn

Replace the four `sorry` steps in the exercise file:

1. Prove that the empty path stays at its starting vertex.
2. Prepend an edge to a valid tail path.
3. Extract the tail path from a nonempty path. Identify its new start.
4. Prove path concatenation for arbitrary lists and endpoints.

For exercise 4, try writing the induction yourself before consulting the
library proof. The assignment checks the result, not which tactics you used;
using the checked library theorem is also accepted. Helper proofs are welcome.

Then inspect the mistakes file. Its three claims try to move along an empty
list, keep the original start after removing the first edge, and reverse a
directed journey without reverse-edge evidence. Explain why each is false
before reading the diagnostic. A failure of `refl` is not a request to keep
trying tactics when the claimed equality itself is unjustified.

## 18.5 Check the assignment

In the browser, open `ch18-exercises.ctea` and load `ch18.ctea-task` with the
assignment control. Your incomplete work can be saved, but all four statements
must have complete proofs before the assignment passes.

For the native checker:

```sh
target/debug/cetacea_cli --assignment \
  docs/book/hol-code/ch18-solutions.ctea-assignment \
  docs/book/hol-code/ch18-exercises.ctea
```

The solutions pass this policy. It requires the graph package, preserves the
four theorem signatures, and rejects unfinished proofs, new axioms, and
classical reasoning. It permits the bundled path library and the shared List
package.

This assignment uses the `hol` profile because an arbitrary edge relation is
passed to the path predicate. That profile does not itself permit classical
reasoning or additional axioms. A concrete path statement may compute to
first-order facts, while a proof using the generic concatenation theorem
retains the higher-order requirement of that dependency.

We have proved a fact about joining walks. We have not counted vertex degrees,
proved the handshake theorem, found a shortest path, or related this predicate
to the closed-set reachability definition. Those require further arguments.
