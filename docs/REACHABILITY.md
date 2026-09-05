# Reachability and preserved properties

The checked source library `std/hol/reachability.ctea` provides a first public
graph interface. A graph is supplied as a relation `E(a, b)` on a vertex type.
Edges are directed; symmetry, finiteness and absence of loops are not assumed.

`G.Closed(E, S)` says that every edge starting in `S` also ends in `S`.
`G.Reaches(E, a, b)` says that **every edge-closed set containing `a` contains
`b`**. This is the definition used by this library. It is useful for proving
that a journey preserves a property, without naming each intermediate vertex.

The public theorems are:

| Theorem | What it proves |
| --- | --- |
| `reaches_refl` | A vertex reaches itself. |
| `reaches_edge` | One edge gives reachability. |
| `reaches_trans` | Reachability from `a` to `b` and from `b` to `c` composes. |
| `reaches_invariant` | A reachable vertex belongs to every closed set containing the start. |
| `not_reaches_of_closed` | A closed set containing the start but excluding the finish rules out reachability. |

All proofs are constructive, without axioms or unfinished steps. The source
is bundled in native and Wasm builds, including virtual projects.

## A directed road example

[The checked example](hol/examples/reachability.ctea) has three vertices,
`home`, `junction`, and `campus`, and two directed roads. It proves that home
reaches campus, and that campus cannot reach home. For the second proof, the
singleton set containing campus is closed: there are no roads leaving it.

To compose the outward journey, provide the edge relation and midpoint:

```cetacea
  apply G.reaches_trans {E := Road; b := junction}
  apply G.reaches_edge {E := Road}
  exact home_to_junction
  apply G.reaches_edge {E := Road}
  exact junction_to_campus
```

The relation itself must be named. Its concrete signature, `Stop -> Stop ->
Prop`, supplies the vertex type, so `A := Stop` is optional. Explicit type
arguments are checked for consistency regardless of their position in the
argument list. Typed predicate lambdas also supply type information; an
unannotated lambda or a polymorphic predicate may still require explicit
types. The midpoint `b := junction` must agree between the two journeys.

## Explicit path lists

The separate `std/hol/graph@1` package now exposes `ValidPath`, `path_nil`, and
`path_cons`. It shares the generic List datatype with `std/hol/list@1`; imports
under different aliases can exchange lists. `builtin:std/hol/paths.ctea`
provides the constructive, source-written `path_append` theorem. Its proof
uses list induction and the two checked path equations.

Repeated vertices and edges are permitted: `ValidPath` describes a directed
walk, rather than requiring a simple path.

A path list contains the vertices visited **after** the start, including the
finish. For example, `[junction, campus]` describes the route from home via
junction to campus. An empty list means staying at the start.

| Law | Meaning |
| --- | --- |
| `path_nil` | `ValidPath(E, nil, a, b)` iff `b = a`. |
| `path_cons` | `ValidPath(E, cons(h, t), a, b)` iff `E(a, h)` and `ValidPath(E, t, h, b)`. |
| `path_append` | Paths from `a` to `b` and `b` to `c` concatenate into a path from `a` to `c`. |

[The explicit road example](hol/examples/explicit_paths.ctea) proves two legs
and joins their lists. [The concatenation proof](../std/hol/paths.ctea) is
ordinary editable source, not a trusted axiom. Check them with:

```sh
cargo run -p cetacea_cli -- --hol-profile hol docs/hol/examples/explicit_paths.ctea
```

The generic concatenation proof requires the `hol` profile. Closed path
statements can unfold to first-order facts, but the journey that invokes the
generic source theorem retains that theorem's higher-order requirement.
Classical reasoning, axioms, and unfinished proofs are not needed. Core and
Wasm tests check these imports, shared aliases, and rejection of reversed
journeys, wrong finishes, and composition at mismatched endpoints.

An explicit empty-list argument such as `t := L.nil` gets its type from the
supplied relation (`E := Road`), regardless of argument order. You can also
write `t := (L.nil : L.List Stop)` when the context does not determine its type.
Conflicting explicit types are rejected.

This interface does not find a shortest route or establish equivalence between
explicit paths and the closed-set `Reaches` definition. [Chapter 18](book/18-directed-paths.md) supplies worked examples, four exercises,
solutions, intentional mistakes, and native/browser assignment files. Degree
counting and the handshake theorem remain open.
