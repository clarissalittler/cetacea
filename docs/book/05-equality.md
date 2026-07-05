# Chapter 5 — Equality: The Most Important Relation

> **Files for this chapter:**
> [`code/ch05-examples.ctea`](code/ch05-examples.ctea) ·
> [`code/ch05-mistakes.ctea`](code/ch05-mistakes.ctea) (intended to fail) ·
> [`code/ch05-exercises.ctea`](code/ch05-exercises.ctea) ·
> [`code/ch05-solutions.ctea`](code/ch05-solutions.ctea)

## 5.1 Two names, one hero

The citizens of Metropolis believe two contradictory things. They
believe Clark Kent is a mild-mannered reporter who cannot fly. They
believe Superman flies daily. And the whole engine of the story is a
single equation the citizens don't have:

```text
clark = superman
```

The philosopher Gottlob Frege built an entire theory of meaning around
puzzles like this one (his version starred the morning star and the
evening star, which are both Venus). But for us the equation matters
because of what you can *do* with it. The moment you hold a proof of
`clark = superman`, every fact about Superman converts into a fact
about Clark, and back — flight, cape, allergy to glowing rocks, all of
it. That conversion is called **substitution of equals for equals**,
and it is one of equality's two superpowers:

1. **Everything equals itself** — `x = x` always, for free.
2. **Equals substitute for equals** — if `x = y`, then anything true
   of `x` is true of `y`.

That's the entire chapter. Two superpowers, one tactic for each
(`refl` and `rewrite`), and the habits for wielding them. It doesn't
sound like much — and yet everything from Chapter 9 onward, the whole
world of arithmetic and induction and data, runs on these two moves.
Quantifiers were the language of mathematics; equality is its engine.

One ground rule before we start: `x = y` is only a legal proposition
when `x` and `y` have the *same type*. You may ask whether two
`Person`s are equal, or two `Nat`s — but `clark = 0` is not false,
it's *malformed*, and Section 5.8 shows the checker saying so.

## 5.2 `refl`: equality by computation

The tactic `refl` (for *reflexivity*) proves goals of the form
`t = t`. Stated like that it sounds useless — how often do you need to
prove `clark = clark`? But `refl` has a hidden talent: before
comparing the two sides, it **computes** them. Watch:

```text
theorem two_plus_three : add(2, 3) = 5 := by
  refl
```

`add(2, 3)` and `5` are not the same expression — one is a sum, the
other a numeral. But Cetacea's natural numbers *compute*: `add` has
built-in equations, and under the hood the numeral `5` is shorthand
for `succ(succ(succ(succ(succ(0)))))` — "the successor of the
successor of ... of zero," five layers deep. (You'll meet this
succ-tower notation properly in Chapter 9; today it's enough to know
that it's there, because error messages sometimes show it.) `refl`
evaluates `add(2, 3)`, evaluates `5`, sees the same tower of `succ`s
on both sides, and accepts. One line, and the checker did the
arithmetic.

This makes `refl` a tiny calculator that only ever says "yes" when the
answer is right:

```text
theorem seven_times_six : mul(7, 6) = 42 := by
  refl

theorem four_two_ways : add(2, 2) = add(1, 3) := by
  refl
```

Note the second one: *neither* side is a plain numeral, and `refl`
doesn't care — both compute to `4`, and that settles it.

Computation even works with variables in the way, as long as the
built-in equations can still make progress:

```text
theorem add_zero_demo (n : Nat) : add(n, 0) = n := by
  refl

theorem add_one_demo (n : Nat) : add(n, 1) = succ(n) := by
  refl
```

We don't know what `n` is, but `add(n, 0)` simplifies to `n` anyway —
adding zero is one of the equations the checker knows. When the two
sides *don't* compute to the same thing (`add(n, m) = add(m, n)`,
say — true, but no amount of evaluation shows it), `refl` refuses, and
you need either the heavier machinery below or, eventually, Chapter
9's induction.

The philosophical headline: **checking a proof and running a program
are the same activity.** `refl` is the first place the course makes
that visible, and Chapter 10 is where it becomes the whole show.

## 5.3 `rewrite`: substitution, with a direction

Now the second superpower. Suppose Lois finally has the scoop —
`h : clark = superman` — and needs to conclude that Clark flies, given
that Superman does. The tactic is `rewrite`, and here it is at work:

```text
theorem secret_identity_used
  : clark = superman -> Flies(superman) -> Flies(clark) := by
  intro h
  intro hs
  rewrite -> h
  exact hs
```

After the intros the state is:

```text
h : clark = superman, hs : Flies(superman)  |-  Flies(clark)
```

`rewrite -> h` reads the equation left-to-right: *find `clark` (the
left side) in the goal, replace it with `superman` (the right side).*
The goal becomes

```text
h : ..., hs : Flies(superman)  |-  Flies(superman)
```

and `exact hs` closes it. One substitution, exactly what you'd do on
paper — except the checker made sure you substituted a thing that's
actually equal.

The arrow matters. **Bare `rewrite h` goes the other way**: it hunts
for the equation's *right* side in the goal and replaces it with the
left side.

```text
theorem secret_identity_back
  : clark = superman -> Flies(clark) -> Flies(superman) := by
  intro h
  intro hc
  rewrite h
  exact hc
```

Here the goal `Flies(superman)` contains the equation's right side, so
bare `rewrite h` turns it back into `Flies(clark)`. A useful way to
keep the two straight: **look at your goal, find which side of the
equation appears in it, and pick the form that hunts for that side** —
`->` hunts left sides, bare hunts right sides. Getting this backwards
is this chapter's Mistake 1, and the error message (Section 5.8) tells
you precisely which term it went looking for and couldn't find.

One more variant. `rewrite` replaces *one* occurrence at a time
(handy for precision); `rewrite all` sweeps the whole goal:

```text
theorem rewrite_all_demo
  : clark = superman
    -> Flies(clark) /\ Reporter(clark)
    -> Flies(superman) /\ Reporter(superman) := by
  intro h
  intro hc
  rewrite all h
  exact hc
```

Both `superman`s in the goal become `clark`s in one stroke, and the
hypothesis `hc` fits exactly.

## 5.4 Symmetric and transitive — for free

Every equality you'll ever meet can be flipped and chained. Is that
two more rules to learn? No — and this is the pleasant surprise of the
chapter: **symmetry and transitivity are not new rules.** They're
*theorems*, provable from `refl` and `rewrite` alone, and the standard
library has already proved them (in `std/eq.ctea`, a few lines each —
go look):

```text
eq_symm  : x = y -> y = x
eq_trans : x = y -> y = z -> x = z
```

Using them is Chapter 4's library skill:

```text
theorem identity_symm : clark = superman -> superman = clark := by
  intro h
  exact eq_symm h

theorem identity_chain
  : clark = superman -> superman = kal_el -> clark = kal_el := by
  intro h1
  intro h2
  exact eq_trans h1 h2
```

(`kal_el` is the third name — Superman's birth name, for the
Kryptonian-record-keeping department.) Notice we didn't spell out the
instantiation braces: the checker infers `x`, `y`, `z` from the
hypotheses we pass in.

Lemmas also compose *inside* a rewrite, because `rewrite` accepts any
proof expression that proves an equation:

```text
theorem rewrite_symm_inline
  : superman = clark -> Flies(clark) -> Flies(superman) := by
  intro h
  intro hc
  rewrite eq_symm h
  exact hc
```

`eq_symm h` is a proof of `clark = superman`, built on the fly, and
`rewrite` uses it directly. No need to `have` it into a named
hypothesis first — though, speaking of which:

## 5.5 `have`: naming the waypoint

On paper, long arguments breathe through phrases like *"let us first
establish that..."* — you prove a small intermediate fact, give it a
moment to exist, then use it. Cetacea's version is the `have` tactic,
and this chapter is where it becomes indispensable, because equational
proofs are *chains*: `a = b`, then `b = c`, so `a = c`, and now
substitute...

`have` comes in two forms. When you already hold the proof as an
expression, attach it with `:=`:

```text
theorem fly_by_stages
  : clark = superman -> superman = kal_el -> Flies(kal_el) -> Flies(clark) := by
  intro h1
  intro h2
  intro hf
  have h3 : clark = kal_el := eq_trans h1 h2
  rewrite -> h3
  exact hf
```

The line `have h3 : clark = kal_el := eq_trans h1 h2` checks that the
expression really proves the stated formula, then adds
`h3 : clark = kal_el` to your hypotheses. The proof reads exactly like
the paper version: *first establish Clark is Kal-El (by chaining the
two equations); now substitute and finish.*

When the intermediate fact needs a real proof of its own, state it
bare and prove it as a subgoal:

```text
theorem have_subgoal_demo
  : clark = superman
    -> superman = kal_el /\ Reporter(clark)
    -> Flies(kal_el) -> Flies(clark) := by
  intro h1
  intro h2
  intro hf
  have hck : clark = kal_el
  exact eq_trans h1 h2.left
  rewrite -> hck
  exact hf
```

After `have hck : clark = kal_el`, the checker *pauses your main goal*
and makes `clark = kal_el` the current target. The next line proves it
— note `h2.left` reaching into the conjunction right there in the
argument position, no separate step needed — and then the main goal
resumes, now with `hck` available. Trace the goal states:

```text
h1, h2, hf                       |-  Flies(clark)      -- have hck : ...
h1, h2, hf                       |-  clark = kal_el    -- the waypoint
h1, h2, hf, hck : clark = kal_el |-  Flies(clark)      -- main goal resumes
```

Two habits worth forming now. First, `have` names must be fresh — the
checker rejects shadowing, same as `intro`. Second, use `have` the way
you'd use a paragraph break: whenever a proof stops being a
straight line and you feel yourself holding two thoughts at once, name
one of them.

## 5.6 Substitution reaches everywhere

Equality's second superpower is stronger than it first appears:
substitution works not just on whole statements but *inside* any
expression, however deep. Equal people have equal mothers:

```text
theorem mothers_agree
  : clark = superman -> mother(clark) = mother(superman) := by
  intro h
  rewrite -> h
  refl
```

`rewrite -> h` reaches inside the function call `mother(clark)` and
rewrites the argument, leaving `mother(superman) = mother(superman)` —
which is `refl`'s favorite kind of goal. This two-line pattern —
*rewrite, then refl* — is the fundamental rhythm of equational proof,
and you will type it a hundred times before the course is done.

The library also packages substitution as a theorem you can invoke,
under the name `congr_pred` (for *congruence*): if `x = y` then
`P(x) -> P(y)`, for any predicate `P` whatsoever. Philosophers call
this Leibniz's law — *identical things have identical properties*:

```text
theorem leibniz_demo : clark = superman -> Flies(clark) -> Flies(superman) := by
  intro h
  intro hf
  exact congr_pred {A := Person; P := Flies; x := clark; y := superman} h hf
```

Mostly you'll just `rewrite`, which does the same job with less
ceremony. But `congr_pred` earns its keep when you need to hand
"substitution itself" to another theorem as an argument — it turns a
*tactic* into a *thing* — and it will quietly star in a clever proof
in Chapter 8.

## 5.7 `simp` learns equations

You met `simp` briefly as the tactic that "computes" — it shares
`refl`'s evaluation engine. What's new: you can hand `simp` extra
equations of your own, in brackets, and it will use each one as a
left-to-right rewrite rule wherever it applies:

```text
theorem simp_rule_demo
  : mother(clark) = superman -> Flies(superman) -> Flies(mother(clark)) := by
  intro h
  intro hf
  simp [h]
  exact hf
```

`simp [h]` rewrites `mother(clark)` to `superman` in the goal — note
that this is the `->` direction; `simp`'s rules always fire
left-to-right — leaving `Flies(superman)`, which is `hf`.

And where `rewrite` transforms the *goal*, `simp ... at` transforms a
*hypothesis*:

```text
theorem simp_at_demo
  : mother(clark) = superman -> Flies(mother(clark)) -> Flies(superman) := by
  intro h
  intro hf
  simp [h] at hf
  exact hf
```

Here the goal was already what we wanted; it was the hypothesis that
needed cleaning up. `simp [h] at hf` rewrites inside `hf`, turning it
into `Flies(superman)`. (The names in the brackets can be local
hypotheses, as here, or top-level theorems; `simp at *` does goal and
hypotheses at once.) Working on hypotheses instead of the goal is
called *forward reasoning*, and sets — next chapter — will give both
directions a workout.

## 5.8 Common mistakes

Run [`code/ch05-mistakes.ctea`](code/ch05-mistakes.ctea) — intended to
fail, as always.

**Mistake 1: rewriting against the grain.** The proof holds
`h : clark = superman` and a goal about `clark`, and reaches for bare
`rewrite h` — which hunts for the equation's *right* side:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch05-mistakes.ctea:21: theorem `wrong_direction` failed: rewrite could not find `superman` in goal `Flies(clark)`
  note: target: Flies(clark)
```

Read the message the way the checker means it: *I looked for
`superman` in `Flies(clark)` and it isn't there.* That's your cue that
you wanted the other form — `rewrite -> h`. This error is harmless,
instantly diagnosable, and you will cause it roughly weekly for the
rest of your formal-proof career. (Everyone does.)

**Mistake 2: expecting `refl` to believe you.** `refl` computes both
sides and compares. If the equation is false, no tactic can help, and
the error shows you the computation-eye view:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch05-mistakes.ctea:26: theorem `arithmetic_optimism` failed: refl cannot prove `add(succ(succ(0)), succ(succ(0))) = succ(succ(succ(succ(succ(0)))))` because the sides are not identical
  note: target: add(succ(succ(0)), succ(succ(0))) = succ(succ(succ(succ(succ(0)))))
  help: Use equality simplification first
    `refl` closes goals whose two sides are already identical. Try `simp` or `rewrite` before `refl` if the sides should compute to the same term.
    try:
      simp
      refl
```

There are the succ-towers from Section 5.2: `add(2, 2)` on the left,
`5` spelled out as five `succ`s on the right, and no way to make them
the same height. Two lessons. First, this is what numerals *are*
underneath. Second, note that the `help:` block suggests `simp` before
`refl` — good advice when the sides *should* compute to the same term
and you're one simplification away, but no rescue for an equation
that's simply false. The checker flags the failed step; deciding
whether the statement was ever true remains your job.

**Mistake 3: `have` says one thing, the proof says another.** The
`:=` form of `have` checks the expression against the formula you
stated — it will not quietly accept a proof of something else, not
even the mirror image of what you asked for:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch05-mistakes.ctea:31: theorem `have_backwards` failed: have proof has type `clark = superman`, but the stated formula is `superman = clark`
  note: target: superman = clark
```

`clark = superman` and `superman = clark` are interchangeable *in
truth* — that's `eq_symm` — but they are different formulas, and
`have`'s contract is exact. The fix is one lemma: `have h2 :
superman = clark := eq_symm h`.

**Mistake 4: comparing across types.** Finally, the ground rule from
Section 5.1, enforced:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch05-mistakes.ctea:35: theorem `type_confusion` has invalid statement
  note: equality compares `clark` of type `Person` with `0` of type `Nat`
  note: target: clark = 0
```

Note the different flavor of failure: not "theorem failed" but
"theorem **has invalid statement**." No tactic ever ran — the
statement never made it into the game. Chapter 4's wrong-type witness
got caught the same way, and this is the general principle: the type
system screens out *nonsense* before the logic even considers
*falsehood*.

## 5.9 Exercises

Open [`code/ch05-exercises.ctea`](code/ch05-exercises.ctea) and clear
the `sorry` flags.

- **Exercise 5.1** `mul(3, 4) = 12` — let the checker do the
  arithmetic.
- **Exercise 5.2** `add(n, 2) = succ(succ(n))` — computation with a
  variable in the way, like `add_one_demo`.
- **Exercise 5.3** `superman = clark -> clark = superman` — one lemma;
  or, if you're feeling tactile, a `rewrite` and a `refl`.
- **Exercise 5.4** `clark = superman -> superman = kal_el ->
  clark = kal_el` — chain the equations; use the `have ... :=` form
  with `eq_trans`, even though a shorter route exists, just to have
  written one.
- **Exercise 5.5** `clark = superman -> Reporter(superman) ->
  Reporter(clark)` — substitution into a predicate. Check which side
  of the equation your goal mentions before picking a direction.
- **Exercise 5.6** the same, but with `Flies(...) /\ Reporter(...)` on
  both sides — one `rewrite all` handles it.
- **Exercise 5.7** `superman = kal_el -> mother(superman) =
  mother(kal_el)` — equal people, equal mothers: the rewrite-then-refl
  rhythm.

Solutions: [`code/ch05-solutions.ctea`](code/ch05-solutions.ctea).

---

*Next: [Chapter 6 — Sets](06-sets.md), where equality meets
collections: membership, subsets, Venn diagrams as theorems — and a
proof method (extensionality) that turns "these two sets are equal"
into a Chapter 2 exercise about an arbitrary element.*
