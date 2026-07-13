# Finite Mathematics Vertical Pilot

This pilot tests a complete teaching path rather than another isolated kernel
feature. A student declares a finite datatype, exhibits an exhaustive list,
proves its cardinality, and then transports cardinality across a bijection.
The two exercises deliberately sit on opposite sides of Cetacea's enforced
FOL/HOL boundary.

## What `HasCard` says

For a type `A`, list `xs : List A`, and natural number `n`,

```text
HasCard(xs, n)
```

packages three facts:

1. `Nodup(xs)`: no element is counted twice;
2. `length(xs) = n`: the enumeration has the claimed size; and
3. `forall x : A, Member(x, xs)`: the enumeration is exhaustive.

This keeps finiteness evidence explicit. Cetacea does not pretend that an
arbitrary set has a computable cardinality.

The checked finite package exposes both directions of this interface:

```text
has_card_intro
has_card_nodup
has_card_length
has_card_coverage
```

The three elimination theorems matter pedagogically: later proofs can consume
one mathematical hypothesis, `HasCard(xs, n)`, instead of carrying its three
implementation components as unrelated premises.

## Exercise 1: enumerate a finite datatype

The [starter](finite_traffic_starter.ctea) declares a three-constructor type:

```text
data Traffic
| red
| yellow
| green
```

The goal is to prove that `[red, yellow, green]` is a duplicate-free,
exhaustive enumeration of length three. The complete checked proof is
[finite_traffic.ctea](../examples/finite_traffic.ctea).

Check the solution under the instructor policy with:

```sh
cargo run -p cetacea_cli -- \
  --assignment docs/hol/pilot/finite_traffic.ctea-assignment \
  docs/hol/examples/finite_traffic.ctea
```

The assignment permits only `std/hol/finite@1` and its exact List dependency.
It forbids classical reasoning, axioms, and incomplete proofs. The resulting
receipt is `fol+induction`: constructor no-confusion, recursive list
predicates, and datatype induction do not make the exercise higher-order.

This first solution is intentionally explicit. It exposes a real usability
finding: manually proving duplicate-freedom and coverage for three nullary
constructors takes much more ceremony than the mathematics deserves. Before
this becomes a polished book chapter, the pilot should add a small checked
enumeration derivation or a reusable fixed-length enumeration theorem. The
current proof is the acceptance case that such an improvement must shorten
without adding trust.

## Exercise 2: transport cardinality along a bijection

The [second starter](finite_bijection_starter.ctea) assumes inverse functions
`f : A -> B` and `g : B -> A`. Starting from `HasCard(xs, n)`, it asks for
`HasCard(map(f, xs), n)`. The [solution](../examples/finite_bijection.ctea)
uses the checked projections above, preservation of `Nodup`, preservation of
length, and surjective coverage.

Check it with:

```sh
cargo run -p cetacea_cli -- \
  --assignment docs/hol/pilot/finite_bijection.ctea-assignment \
  docs/hol/examples/finite_bijection.ctea
```

Both packages are imported under the same namespace `F`; their shared List
dependency is installed once and retains its own stable package receipts.

This assignment is honestly `hol`. The inverse laws themselves can be used as
first-order function-symbol schemas, but generic `map` consumes a function as
a value. The assignment manifest therefore says `profile = "hol"`; importing
the package cannot silently raise a supposedly first-order exercise.

## Current acceptance result

The pilot currently establishes four things end to end:

- a multi-constructor cardinality proof works in native and browser checking;
- datatype no-confusion is replayed as explicit HOL kernel evidence;
- `HasCard` has a usable checked introduction/elimination interface; and
- assignment manifests enforce the intended `fol+induction` versus `hol`
  distinction on the actual exercises.

The next vertical target is the pigeonhole principle. It should consume
`HasCard` evidence rather than unfold list machinery throughout its statement.
Any new automation or theorem surface should be justified by that proof and
then reused for finite-union cardinality.
