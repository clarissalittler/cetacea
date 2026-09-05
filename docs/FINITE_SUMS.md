# Finite sums

For a guided lesson with exercises, solutions and a browser assignment, use
[Chapter 17: Adding Up Finite Lists](book/17-finite-sums.md).

Import `std/hol/sums.ctea as S` to sum natural numbers in the shared
`std/hol/list@1` list type. An independent list alias works with the same sum:

```cetacea
import std/hol/sums.ctea as S
import std/hol/list@1 as L

theorem four : S.sum(L.cons(2, L.cons(2, L.nil))) = 4 := by
  simp
  refl
```

The public laws are `S.sum_nil`, `S.sum_cons`, and `S.sum_append`. The last
states that the sum of two concatenated lists is the sum of their totals.
Its proof uses list induction and associativity of natural-number addition.
All three laws are constructive, checked by both engines, and use no axioms
or unfinished proofs.

For a concrete list, `simp` evaluates the recursive sum. For an unknown list,
use the public laws. See [the checked examples](hol/examples/finite_sums.ctea)
for combining two known totals and then three arbitrary groups. The two
rewrites in the three-group example expose one concatenation at a time.

Repeated entries contribute repeatedly. This operation sums a list of numbers;
it does not assert that a list enumerates a set without duplicates. Summing
vertex degrees will additionally require an enumeration of vertices and a
definition of degree. The handshake theorem and that graph interface remain
future work.

The source library is bundled with native and Wasm builds and is available to
virtual projects without access to the host filesystem. It is a checked source
module, not a versioned logical package.

[Degree counting](DEGREE_COUNTING.md) adds generic weighted-sum laws and a
checked handshake proof for a three-vertex multigraph representation.
