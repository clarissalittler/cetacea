# Chapter 4 — Everyone, Someone, No One: Quantifiers

> **Files for this chapter:**
> [`code/ch04-examples.ctea`](code/ch04-examples.ctea) ·
> [`code/ch04-mistakes.ctea`](code/ch04-mistakes.ctea) (intended to fail) ·
> [`code/ch04-exercises.ctea`](code/ch04-exercises.ctea) ·
> [`code/ch04-solutions.ctea`](code/ch04-solutions.ctea)

## 4.1 Two sentences that are not the same sentence

Read these carefully:

> Everyone in this class has a study partner.
>
> Someone is a study partner for everyone in this class.

Fifteen words each, nearly the same words, wildly different claims. The
first is ordinary — people pair up. The second says one heroic
individual partners with the *entire class*. The second implies the
first; the first comes nowhere near implying the second. And yet, on a
late night, three weeks into the term, they blur together — for
students, and for professionals: entire published proofs have died on
this confusion.

Propositional logic can't even *express* the difference. `P`, `Q`, and
five connectives have no way to say "everyone" or "someone" — atoms
have no insides. This chapter upgrades our language with the two
**quantifiers**, `forall` and `exists`, gives each its introduction and
elimination rules in the natural-deduction style of Chapter 2, and
ends by letting the checker referee the study-partner confusion for us.
We're back in `mode constructive` throughout — quantifiers don't need
classical logic, with one interesting exception we'll flag when we
pass it.

## 4.2 Predicates: propositions with blanks

First we need things to quantify *over*. In Cetacea you declare a
domain of discourse with `sort`, some named individuals with `const`,
and — the key upgrade — **predicates** with `pred`. A predicate is a
proposition with a blank in it: not "Alice is happy" but "___ is
happy," waiting for a subject. Our running example world:

```text
sort Person

const alice : Person
const bob : Person

pred Happy(Person)
pred Rich(Person)
pred Knows(Person, Person)
```

`Happy` by itself is not true or false — it's a machine that turns a
`Person` into a proposition. `Happy(alice)` is a proposition.
Predicates can take several arguments: `Knows(alice, bob)` — read
"alice knows bob" — is built from the two-place predicate `Knows`.
(Back in Chapter 1 we said "x + 1 = 5" wasn't a proposition. Now we can
say what it is: a predicate, waiting for its `x`.)

Quantifiers bind the blank:

- `forall x : Person, Happy(x)` — *every* person is happy.
- `exists x : Person, Happy(x)` — *at least one* person is happy
  (no claim about who, and no claim that there's only one).

The `x` is a bound variable, a pronoun with no life outside its
quantifier — `forall y : Person, Happy(y)` is the very same statement.

## 4.3 `forall`: the rules

**Elimination — from everyone to anyone.** If everybody's happy, Alice
is happy. To use a universal fact `h`, apply it to an individual, with
the same proof-expression syntax as ever — `h alice` is a proof of
`Happy(alice)`:

```text
theorem everyone_alice : (forall x : Person, Happy(x)) -> Happy(alice) := by
  intro h
  exact h alice
```

A universal hypothesis is a vending machine: insert any person, out
comes a proof about that person. (Note what the theorem *doesn't* need:
any information about who alice is. That's the shape doing the work.)

**Introduction — proving something about everyone.** You can't check
seven billion cases. The rule is subtler and lovelier: *prove it for a
person about whom you assume absolutely nothing.* If the proof works
for a total stranger, it works for everyone. The tactic is our old
friend `intro` — used on a `forall` goal, it brings an arbitrary
individual into scope:

```text
theorem forall_and_half
  : (forall x : Person, Happy(x) /\ Rich(x)) -> forall x : Person, Happy(x) := by
  intro h
  intro x
  exact (h x).left
```

Trace the goal states:

```text
h : forall x : Person, Happy(x) /\ Rich(x)  |-  forall x : Person, Happy(x)
```

After `intro x` — "let `x` be an arbitrary person":

```text
h : ..., x : Person  |-  Happy(x)
```

Now eliminate `h` at that very `x`: `h x` proves `Happy(x) /\ Rich(x)`,
and `.left` projects out the half we owe. Note the parentheses in
`(h x).left` — first apply, then project.

That `intro` handles both `->` and `forall` is no coincidence, and it
foreshadows one of the deepest ideas in logic: a universal statement
*is* a kind of function — give it an individual, it gives you a proof.

## 4.4 `exists`: the rules

**Introduction — one example settles it.** To prove somebody's happy,
produce the somebody. The tactic `exists w` names your **witness**,
then you prove the claim about them:

```text
theorem someone_happy : Happy(alice) -> exists x : Person, Happy(x) := by
  intro h
  exists alice
  exact h
```

After `exists alice` the goal is just `Happy(alice)`. Constructive
mode makes this rule feel especially honest: an existence claim is a
name plus a receipt.

**Elimination — using "someone" without knowing who.** Trickier.
Given `h : exists x : Person, Happy(x)`, you know a happy person exists
but have no name for them. The rule: `cases h with | intro w hw =>`
opens the package and *gives* them a name — a fresh one, `w`, about
which you know exactly one thing, `hw : Happy(w)`:

```text
theorem exists_weaken
  : (exists x : Person, Happy(x) /\ Rich(x)) -> exists x : Person, Happy(x) := by
  intro h
  cases h with
  | intro w hw =>
      exists w
      exact hw.left
```

Yes, it's the same `cases` that eliminated `\/` in Chapter 2, with an
arm shaped like the one that unpacks pairs — fitting, since a proof of
`exists` is a pair: a witness together with evidence about it. And
notice the pleasing rhyme with `forall`: to *prove* a `forall` you
handle an arbitrary individual; to *use* an `exists` you receive an
anonymous one.

## 4.5 The rules in concert

The quintessential quantifier argument: "every happy person is rich;
someone is happy; therefore someone is rich."

```text
theorem exists_mono_demo
  : (forall x : Person, Happy(x) -> Rich(x))
    -> (exists x : Person, Happy(x))
    -> exists x : Person, Rich(x) := by
  intro himp
  intro h
  cases h with
  | intro w hw =>
      exists w
      apply himp w
      exact hw
```

All four rules in nine lines: open the existential (get `w` and
`hw : Happy(w)`), offer the same `w` as witness for the conclusion,
then hit the goal `Rich(w)` with the universal fact specialized to `w`
— `apply himp w` works backwards through `Happy(w) -> Rich(w)`,
leaving `|- Happy(w)`, which is `hw`. The anonymous witness flows
through the whole proof without ever getting a real name.

## 4.6 Negation meets the quantifiers

How do you deny "someone is happy"? By asserting "everyone is
unhappy." Denial flips the quantifier and pushes the `not` inward —
these are De Morgan's laws again, grown up. Both useful directions are
constructive, and both are in the examples file.

Direction one — universal unhappiness refutes any alleged witness:

```text
theorem no_happy_no_witness
  : (forall x : Person, not Happy(x)) -> not exists x : Person, Happy(x) := by
  intro h
  intro he
  cases he with
  | intro w hw =>
      apply h w
      exact hw
```

(The second `intro` is Chapter 2 negation at work: the goal
`not exists ...` is `(exists ...) -> False` in disguise. We assume the
existential, unpack the supposed happy person `w`, and feed them to
`h w : not Happy(w)`.)

Direction two — if there's provably no witness, every individual case
fails:

```text
theorem no_witness_no_happy
  : (not exists x : Person, Happy(x)) -> forall x : Person, not Happy(x) := by
  intro h
  intro x
  intro hx
  apply h
  exists x
  exact hx
```

Take an arbitrary `x`, suppose `hx : Happy(x)` — well then somebody
*is* happy, namely `x`, contradicting `h`.

The other classic pair relates `not forall` and `exists not`. One
direction is a chapter exercise (4.6: a counterexample refutes a
universal claim — constructive). But its converse,

```text
not (forall x : Person, Happy(x)) -> exists x : Person, not Happy(x)
```

is the flagged exception from Section 4.1: **classical only**. Sit with
that for a moment, because it's Chapter 3's whole story replayed with
quantifiers: knowing that universal happiness *fails* hands you no
particular unhappy person — to produce the witness that constructive
`exists` demands, you'd need something like excluded middle to hunt
them down. (Cetacea's standard library ships the two constructive
directions as `forall_not_to_not_exists` and
`not_exists_to_forall_not`; more on the library in Section 4.8.)

## 4.7 Order of quantifiers: the study partners, formally

Back to Section 4.1. With a two-place predicate the two sentences
become:

```text
forall y : Person, exists x : Person, Knows(x, y)   -- everyone has someone
exists x : Person, forall y : Person, Knows(x, y)   -- someone covers everyone
```

Same pieces, opposite nesting. The direction that *does* hold — a
universal champion certainly gives each person someone — is a clean
constructive proof:

```text
theorem celebrity_spread
  : (exists x : Person, forall y : Person, Knows(x, y))
    -> forall y : Person, exists x : Person, Knows(x, y) := by
  intro h
  intro y
  cases h with
  | intro w hw =>
      exists w
      exact hw y
```

One person `w`, offered as the witness for every `y` — the proof
almost writes itself, and the *order of the tactics* tells the story:
we can open the existential before knowing which `y` we're serving,
because `w` doesn't depend on `y`.

Now try the reverse direction. The attempted proof is in the mistakes
file, and Section 4.9 shows the checker stopping it — the tactics
physically don't exist to extract one uniform witness from a family of
per-person ones. When each person's partner might be different, no
single `w` is promised. The failure isn't a gap in Cetacea; it's the
actual logical content of the distinction, enforced mechanically.

## 4.8 Don't prove it twice: the standard library

Everything we proved today was about `Person`, `Happy`, `Rich` — but
none of it *used* anything about persons or happiness. The proofs are
pure shape. Cetacea's standard library (`std/fol.ctea`, loaded by the
`import ../../../std/prelude.ctea` line our companion files always
start with) states the shapes once, over an arbitrary type `A` and
arbitrary predicates, under names like `forall_mono`, `exists_mono`,
and the negation lemmas from Section 4.6.

To use a library shape at your own domain, name the instantiation in
braces:

```text
theorem use_the_library
  : (forall x : Person, Happy(x) -> Rich(x))
    -> (forall x : Person, Happy(x))
    -> forall x : Person, Rich(x) := by
  exact forall_mono {A := Person; P := Happy; Q := Rich}
```

One line: this theorem is `forall_mono` with `A := Person`,
`P := Happy`, `Q := Rich`. (Cetacea can often infer instantiations from
the goal, so a bare `exact forall_mono` frequently works too — the
explicit braces are for when inference needs help, and for readers.)
This is the moment the course quietly changes character: you're no
longer only *making* moves, you're starting to *collect* them.

## 4.9 Common mistakes

Run [`code/ch04-mistakes.ctea`](code/ch04-mistakes.ctea) — intended to
fail, as usual.

**Mistake 1: a witness from the wrong world.** The goal wants a
`Person`; the proof, in a fit of absent-mindedness, offers the number
`0`:

```text
error: docs/book/code/ch04-mistakes.ctea:19: theorem `wrong_witness` failed: exists witness `0` has type `Nat`, but the goal needs a `Person`
  note: target: exists x : Person, Happy(x)
```

Every term in Cetacea has a **type** — `alice` is a `Person`, `0` is a
`Nat` (a natural number, star of Chapter 9) — and `exists` checks your
witness's type against the quantifier's before even looking at the
logic. Silly as this example is, its grown-up siblings (offering an
index where a value is needed, an element where a set is needed) are
everyday bugs, and this error message catches them at the source.

**Mistake 2: swapping quantifiers the wrong way.** The reverse of
`celebrity_spread` — "everyone has an admirer, so someone admires
everyone." The proof tries to `cases` the universal hypothesis, hoping
to shake a single witness out of it:

```text
error: docs/book/code/ch04-mistakes.ctea:31: theorem `everyone_has_an_admirer_so_someone_admires_everyone` failed: cases with `| intro a b` expects an existential or conjunction proof
  note: target: exists x : A, forall y : A, R(x, y)
  note: the first-order statement is false in a 2-element domain where R = {(a,b), (b,a)}. No proof can close it; check the statement itself.
```

`cases ... with | intro ...` opens things that *contain* something — an
existential's witness, a conjunction's halves. A `forall` contains no
individual to extract; it only answers when you ask about someone
specific. The tactic refuses, and with it dies the only plan the
invalid argument ever had. When you're genuinely unsure which way a
quantifier swap goes, this is the cheapest experiment in the world: try
to prove it, and see whether the rules cooperate.

Chapter 2's caveat still applies: a *failed proof* isn't by itself a
refutation, because maybe you just proved it badly. Here the checker
has more evidence. The first-order note is a concrete two-person world:
each person admires the other, so everyone has an admirer, but no one
admires everyone. For small abstract sorts and predicates, Cetacea can
now close this kind of case without making you build the world by hand.

## 4.10 Exercises

Open [`code/ch04-exercises.ctea`](code/ch04-exercises.ctea) — the
little world of `Person`s is already declared at the top. Clear the
`sorry` flags.

- **Exercise 4.1** `(forall x, Knows(x, x)) -> Knows(alice, alice)` —
  forall-elimination warm-up.
- **Exercise 4.2** `Rich(bob) -> exists x, Rich(x)` —
  exists-introduction warm-up.
- **Exercise 4.3** `(forall x, Happy(x) /\ Rich(x)) -> forall x, Rich(x)`
  — the other half of `forall_and_half`.
- **Exercise 4.4** two universal facts in, one universal conjunction
  out — `intro x` once, then serve both halves at the same `x`.
- **Exercise 4.5** `(exists x, Happy(x) \/ Rich(x)) ->
  (exists x, Happy(x)) \/ (exists x, Rich(x))` — open the box first,
  *then* case on what's inside; a `cases` within a `cases`, with
  careful indentation.
- **Exercise 4.6** `(exists x, not Happy(x)) -> not forall x, Happy(x)`
  — one counterexample sinks a universal claim, constructively. (Its
  converse is the classical exception from Section 4.6 — not
  provable in this file's mode, so don't feel bad about not proving
  it.)
- **Exercise 4.7** `(forall x y : Person, Knows(x, y)) ->
  Knows(alice, bob)` — two bound variables; specialize both at once
  with `h alice bob`.

Solutions: [`code/ch04-solutions.ctea`](code/ch04-solutions.ctea).

---

*Next up (see the [outline](OUTLINE.md)): equality — the one relation
with a substitution superpower — and after it, sets, relations, and
functions, where today's quantifiers become the working language.*
