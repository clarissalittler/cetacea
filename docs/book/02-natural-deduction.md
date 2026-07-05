# Chapter 2 — Natural Deduction: Proof as a Game with Rules

> **Files for this chapter:**
> [`code/ch02-examples.ctea`](code/ch02-examples.ctea) ·
> [`code/ch02-fallacies.ctea`](code/ch02-fallacies.ctea) (intended to fail) ·
> [`code/ch02-exercises.ctea`](code/ch02-exercises.ctea) ·
> [`code/ch02-solutions.ctea`](code/ch02-solutions.ctea)

## 2.1 Arguments, valid and otherwise

Two arguments. One is fine and one is famously not:

> If the fuse is blown, the lights are out. The fuse is blown.
> **So the lights are out.**

> If the fuse is blown, the lights are out. The lights are out.
> **So the fuse is blown.**

The second one *feels* plausible — that's what makes it dangerous. But
the lights could be out because the power's cut, or the bulbs died, or
you didn't pay the bill. The conclusion doesn't follow.

An argument is **valid** when the conclusion is true in *every*
situation where the premises are true — no exceptions, no "usually."
The first argument is valid; the second has a counterexample (blown
fuse: no; lights out: yes) and is a fallacy with a Latin name we'll get
to in Section 2.8, where we'll feed both arguments to Cetacea and watch
it accept one and reject the other — and even *print the
counterexample*.

But first we need the rulebook. In Chapter 1 you made proof moves by
instinct. This chapter lays out the complete move list — a system
called **natural deduction**, designed in the 1930s to capture how
mathematicians actually reason. Its organizing idea is beautifully
simple: every connective gets two kinds of rules —

- **introduction rules**: how to *prove* a statement built with that
  connective, and
- **elimination rules**: how to *use* one you already have.

You already know four: `split` introduces `/\`, the projections
`.left`/`.right` eliminate it, `intro` introduces `->`, and `apply`
eliminates it. That pattern extends to everything else.

## 2.2 The whole game on one table

This table is the heart of the chapter — and honestly, of the book.
Tactics to the left of the slash introduce; to the right, eliminate.

| Connective | To prove it (introduction) | To use it (elimination) |
|---|---|---|
| `P /\ Q` | `split` — prove both parts | `h.left`, `h.right` |
| `P \/ Q` | `left` or `right` — prove one part | `cases h with ...` — handle both |
| `P -> Q` | `intro hp` — assume `P`, prove `Q` | `apply h` — reduces goal `Q` to goal `P` |
| `not P` | `intro hp` — assume `P`, prove `False` | `apply h` — reduces goal `False` to goal `P` |
| `P <-> Q` | `split` — prove both directions | `h.left`, `h.right` |
| `True` | `trivial` | (nothing to extract) |
| `False` | (no intro rule — that's the point) | `exfalso` / `contradiction` |

Two things to notice before we work through the new rows. First, the
rows for `not` and `->` are identical — that's not a typo, and Section
2.5 explains it. Second, there is a pleasing asymmetry between `/\` and
`\/`: proving an "and" costs two proofs but using one gives you a
choice; proving an "or" costs one proof but *using* one makes you
handle two cases. Everything about disjunction is conjunction through a
mirror.

## 2.3 Implication: modus ponens and chains

The elimination rule for `->` is the most famous inference rule in
logic: **modus ponens** — from `P` and `P -> Q`, conclude `Q`. Here it
is as a theorem about itself:

```text
theorem modus_ponens_demo (P Q : Prop) : P -> (P -> Q) -> Q := by
  intro hp
  intro hpq
  apply hpq
  exact hp
```

After the two `intro`s the state is `hp : P, hpq : P -> Q |- Q`.
Remember from Chapter 1 that `apply` works *backwards*: the target `Q`
matches the conclusion of `hpq`, so `apply hpq` swaps the debt — you
now owe `hpq`'s premise:

```text
hp : P, hpq : P -> Q  |-  P
```

`exact hp` pays it. This backwards style takes a little getting used
to — on paper you'd reason forwards ("I have P, so I get Q") — but it
has a real advantage: the goal always tells you exactly what remains.

Chains of implications fall to repeated `apply`. This one is the rule
your geometry teacher called *hypothetical syllogism*: if P forces Q
and Q forces R, then P forces R.

```text
theorem chain_demo (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R := by
  intro hpq
  intro hqr
  intro hp
  apply hqr
  apply hpq
  exact hp
```

Watch the target shrink backwards along the chain: `R` (goal) — `apply
hqr` → `Q` — `apply hpq` → `P` — `exact hp`. You're walking the
dominoes in reverse.

## 2.4 Disjunction: committing and case-splitting

**Introduction.** To prove `P \/ Q` you prove one side — and you must
pick which, with the tactic `left` or `right`:

```text
theorem or_intro_demo (P Q : Prop) : P -> P \/ Q := by
  intro hp
  left
  exact hp
```

After `left`, the goal `P \/ Q` becomes just `P`. Note the commitment:
once you go `left`, there is no way back to the right side (short of
deleting the line and re-running — which, to be fair, is cheap).
Picking the wrong side is a classic wrong turn, and in Section 2.8
we'll see the surprisingly helpful error it produces.

**Elimination** is proof by cases. If you know `P \/ Q` holds but not
*which* side, any conclusion you draw must survive both possibilities:

```text
theorem or_elim_demo (P Q R : Prop) : (P -> R) -> (Q -> R) -> P \/ Q -> R := by
  intro hpr
  intro hqr
  intro h
  cases h with
  | left hp =>
      apply hpr
      exact hp
  | right hq =>
      apply hqr
      exact hq
```

`cases h with` splits the world in two. In the `| left hp =>` arm
you're living in the world where the left side held, with `hp : P` in
hand; in the `| right hq =>` arm, the world where `hq : Q`. Each arm
must close the goal on its own, and each arm's tactics are indented
beneath it (the indentation is meaningful — it's how the checker knows
where an arm ends).

Read the statement itself once more, because it's the pattern of every
by-cases argument you'll ever write: *if P leads to R, and Q leads to
R, then "P or Q" leads to R.* Both roads must reach the same city.

## 2.5 Negation: `not P` is an implication in a trench coat

Here's the definition that makes the whole system click. In Cetacea —
and in most proof assistants — negation is not a primitive:

> `not P` **is defined as** `P -> False`.

"P is false" *means* "P leads to absurdity." That's why `not`'s table
row duplicated `->`'s: they're the same connective. The checker treats
them as literally identical, which this two-line proof demonstrates —
no conversion step needed:

```text
theorem not_is_an_arrow (P : Prop) : (P -> False) -> not P := by
  intro h
  exact h
```

So, to **prove** `not P`: `intro hp` (assume `P`) and derive `False`.
To **use** `not P` when your goal is `False`: `apply` it, and owe `P`
instead.

But what good is `False` once you've derived it? Everything. `False`
has no introduction rule — there is no honest way to prove it — and in
exchange it has the most generous elimination rule in the game: from
`False`, conclude *anything*. Medieval logicians called it *ex falso
quodlibet* — "from falsehood, whatever you like."

```text
theorem explosion_by_hand (P Q : Prop) : P -> not P -> Q := by
  intro hp
  intro hnp
  exfalso
  apply hnp
  exact hp
```

Follow it: the goal is `Q`, a proposition with no connection to our
hypotheses whatsoever. `exfalso` says "I'll prove `False` instead"
(sounds like a bad trade — it's not, because our hypotheses are
already contradictory). Then `apply hnp` turns goal `False` into goal
`P`, and `exact hp` finishes. The shortcut tactic `contradiction` does
this dance for you whenever the context holds both a proposition and
its negation:

```text
theorem explosion_short (P Q : Prop) : P -> not P -> Q := by
  intro hp
  intro hnp
  contradiction
```

With negation unmasked, **modus tollens** — from `P -> Q` and `not Q`,
conclude `not P` — turns out to be nothing but arrow-shuffling:

```text
theorem modus_tollens_demo (P Q : Prop) : (P -> Q) -> not Q -> not P := by
  intro hpq
  intro hnq
  intro hp
  apply hnq
  apply hpq
  exact hp
```

Pause on the third `intro`. The goal at that point is `not P` — an
implication `P -> False` in disguise — so `intro hp` assumes `P` and
leaves goal `False`. Then backwards: `apply hnq` (owe `Q`), `apply
hpq` (owe `P`), `exact hp`. If it feels like `chain_demo` with a twist
at the end, that's because it is.

## 2.6 The rules in combination: disjunctive syllogism

Real arguments mix connectives, so let's do one with everything: "It's
soup or salad. It's not soup. So it's salad."

```text
theorem disjunctive_syllogism_demo (P Q : Prop) : P \/ Q -> not P -> Q := by
  intro h
  intro hnp
  cases h with
  | left hp =>
      contradiction
  | right hq =>
      exact hq
```

Case on the "or." In the right-hand world, salad in hand, done. In the
left-hand world we hold both `hp : P` and `hnp : not P` — that world
is contradictory, and `contradiction` closes it. This is the key
insight about case analysis with negative information: you don't
*avoid* the impossible case, you enter it and demolish it.

## 2.7 Biconditionals, briefly

Chapter 1 mentioned that `P <-> Q` *is* `(P -> Q) /\ (Q -> P)`. So no
new rules: `split` it, prove each direction as an implication.

```text
theorem iff_swap_demo (P Q : Prop) : P /\ Q <-> Q /\ P := by
  split
  intro h
  split
  exact h.right
  exact h.left
  intro h
  split
  exact h.right
  exact h.left
```

The two halves are the two directions, and each begins with its own
`intro`. (Yes, the two halves are eerily symmetric here. No, that's not
always the case — Chapter 3 has a biconditional whose directions
require different logics.)

## 2.8 Fallacies on trial

Now the payoff. The file
[`code/ch02-fallacies.ctea`](code/ch02-fallacies.ctea) states three
classic invalid arguments as theorems and "proves" them as best it can.
It is intended to fail. Run it:

```sh
target/debug/cetacea_cli docs/book/code/ch02-fallacies.ctea
```

**Fallacy 1: affirming the consequent.** Our blown-fuse argument from
Section 2.1: `(P -> Q) -> Q -> P`. The file's best attempt ends with
`exact hq`, offering the `Q` it has for the `P` it owes:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch02-fallacies.ctea:15: theorem `affirming_the_consequent` failed: exact proof does not solve the goal: proof has type `Q`, but expected `P`
  note: target: P
  note: the statement is not a tautology: it is false when P = false, Q = true. No proof can close it; check the statement itself.
  help: Match the proof to the target
    `exact` closes the goal only when the expression proves the current target `P`. Check which hypothesis (or which projection, `.left`/`.right`) proves exactly this target; for an implication or theorem whose conclusion matches, use `apply`.
```

(The remaining quotes in this section trim the `help:` paragraph, which
is identical on every one of these errors — you'll see it in your
terminal.)

Look at the second `note:`. The checker isn't just rejecting your
tactic — it has analyzed the *statement* and found a **countermodel**:
set `P` false and `Q` true, and the premises hold while the conclusion
fails. Fuse not blown, lights out anyway. This is exactly the
counterexample from Section 2.1, discovered mechanically, and the note
tells you the most important thing a failed proof can: **stop trying —
no proof exists.** The flaw is in the claim, not in you.

**Fallacy 2: denying the antecedent** — `(P -> Q) -> not P -> not Q`
("it didn't rain, so the grass can't be wet" — sprinklers exist). Same
countermodel, same verdict:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch02-fallacies.ctea:24: theorem `denying_the_antecedent` failed: exact proof does not solve the goal: proof has type `Q`, but expected `P`
  note: target: P
  note: the statement is not a tautology: it is false when P = false, Q = true. No proof can close it; check the statement itself.
```

Compare this *statement* with modus tollens from Section 2.5 — the
arrows differ in one place, one is a theorem, the other is refuted by
a two-line truth assignment. Formal logic is a game of millimeters.

**Fallacy 3: reading "or" as "and"** — `P \/ Q -> P`. The attempted
proof does an honest `cases`, and the left arm even succeeds; it's the
right arm — the world where only `Q` holds — where the fallacy has
nowhere to hide:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch02-fallacies.ctea:34: theorem `or_gives_both` failed: exact proof does not solve the goal: proof has type `Q`, but expected `P`
  note: target: P
  note: the statement is not a tautology: it is false when P = false, Q = true. No proof can close it; check the statement itself.
```

**And one honest mistake, for contrast.** The file's last theorem,
`wrong_turn`, states something *true* — `Q -> P \/ Q` — but the proof
goes `left` when it should go `right`. Read this error next to the
three above, carefully:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch02-fallacies.ctea:42: theorem `wrong_turn` failed: exact proof does not solve the goal: proof has type `Q`, but expected `P`
  note: target: P
  note: the open goal does not follow from the current hypotheses: it is false when P = false, Q = true. Reconsider the earlier proof steps.
```

Different note! Not "the statement is not a tautology" but "the **open
goal** does not follow from the current hypotheses ... **reconsider the
earlier proof steps**." The statement is fine; a previous move (`left`)
painted you into a corner. These two notes are the checker triaging
your failure for you:

- *"statement is not a tautology"* → the claim is wrong; fix the
  theorem.
- *"open goal does not follow"* → the claim may be fine; back up and
  take a different turn (here: `right`).

Internalize that distinction and you will save hours.

## 2.9 Exercises

Open [`code/ch02-exercises.ctea`](code/ch02-exercises.ctea) and clear
the `sorry` flags. Everything yields to the table in Section 2.2.

- **Exercise 2.1** `P \/ Q -> Q \/ P` — or is symmetric, but proving
  it takes a case split and two commitments.
- **Exercise 2.2** `P \/ P -> P` — both worlds hand you the same
  prize.
- **Exercise 2.3** `(P -> Q) -> P \/ R -> Q \/ R` — upgrade the left
  side, pass the right side through.
- **Exercise 2.4** `not (P /\ not P)` — the *law of non-contradiction*.
  Remember what `not` unfolds to; the proof starts with `intro` and is
  three lines long.
- **Exercise 2.5** `not (P \/ Q) -> not P /\ not Q` — one direction of
  De Morgan's laws: "neither" means "not this AND not that." (The
  mirror-image law about `not (P /\ Q)` has a surprise in store —
  that's Chapter 3.)
- **Exercise 2.6** `P -> not not P` — double-negation *introduction*.
  After two `intro`s you hold `hp : P` and `hnp : not P` and owe
  `False`.
- **Exercise 2.7** `P \/ Q -> not Q -> P` — disjunctive syllogism,
  mirrored from Section 2.6.

Solutions: [`code/ch02-solutions.ctea`](code/ch02-solutions.ctea).

---

*Next: [Chapter 3 — The Classical Moves](03-classical.md). Exercise 2.6
proved `P -> not not P`. Try, right now, to prove `not not P -> P` with
the rules you have. Seriously — try. When you give up, Chapter 3 will
explain why you had to, and what it costs to buy the missing rule.*
