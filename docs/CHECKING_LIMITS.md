# Checking limits

Native batch checks can run with external process limits:

```sh
python3 scripts/run_limited.py --seconds 30 --memory-mib 1024 --output-mib 8 -- \
  target/debug/cetacea_cli --json --assignment task.ctea-assignment homework.ctea
```

These are also the defaults used by `scripts/check_all.sh` for every source,
negative JSON check and assignment-policy check, and by `hol_baseline.py` and
`hol_shadow.py` for each checker invocation. The runner requires Unix process
groups and `resource` limits, consistent with the existing Bash corpus workflow.

The runner caps elapsed checking time, virtual address space, and combined
stdout/stderr bytes. It drains both pipes concurrently and kills the process
group on timeout or excessive output, including descendants holding a pipe open.
Normal exit codes and both output streams pass through unchanged.

A timeout exits 124; excessive output, signal termination or runner setup failure
exits 125. These are infrastructure failures, not ordinary proof rejection
(exit 1), and the corpus gate rejects them. Limit failures replace partial stdout
with a small JSON failure object, so partial acceptance output is not mistaken
for a completed grading result. Signal failures report the signal without
claiming that memory exhaustion was necessarily its cause. The address-space
limit can cause allocation failure or process termination; it is not a resident
memory measurement. Core dumps are disabled for these child processes.

Six runner tests cover normal rejection output, timeouts after partial acceptance
output, simultaneous stdout/stderr flooding, descendants retaining pipes,
nonfinite limits, and a real allocation denied by the memory limit.

## Remaining core work

File checks and editor analyses now share an aggregate allowance of
250,000,000 charged operations for the lifetime of their checker. Nested
imports and nested checker scopes reuse the outer allowance. Charges cover
declaration dispatch, tactic steps, legacy and HOL proof-node inference,
HOL term traversal entries, normalization steps, and countermodel candidate
enumeration and formula/term evaluation. Legacy type/term/formula name
resolution and validation, definition unfolding, recursive-definition
normalization and environment-aware term normalization now charge traversal
entries too. The iterative successor-normalization loop charges each visited
constructor.
Parser source bytes and expression bytes are charged before constructing their
line/character buffers; parser recursion entries also consume the shared
allowance. Editor buffer entry points keep the scope alive from parsing through
checking. Parse-budget failures return diagnostics before commands are built;
there are no theorem outcomes to report when parsing itself cannot finish.
Three regressions cover these boundaries and recovery on the next check.
The existing per-call
normalization and depth limits also remain in force; starting another
normalization no longer refreshes the aggregate allowance.

Exhaustion during required checking produces a `checker resource limit` error. The declaration loop
stops, leaving subsequent theorem outcomes `not_checked`; already checked
results remain available without making the whole file accepted. Failed
imports roll back their declarations but do not refund spent work. The
thread-local scope is released on normal exit and unwinding, so the next
independent check receives a fresh allowance. Low-level operations called
outside a checker scope retain their existing local limits.

Six regressions cover repeated normalization, nested scopes, unwind recovery,
preservation of prior results and unchecked outcomes, import rollback without
refund, and exhaustion during HOL replay. These are deterministic work counts,
not time or memory measurements. Countermodel signature collection and search
now consume the same allowance. Exhaustion returns no countermodel, not a
false evaluation; only a fully evaluated falsifying assignment produces a
counterexample note. The original proof error remains available if the search
cannot finish. Four additional regressions cover unknown evaluations,
interrupted/recovered searches in all three supported fragments, and preservation
of the original proof error without an invented falsifying assignment. Interrupted
universal and existential evaluation also restore temporary bound-variable
assignments, including shadowed assignments.
Two further regressions cover budget exhaustion and recovery in legacy
validation/unfolding and iterative successor normalization, while retaining
rejection of an ill-typed arithmetic operand. The original-error diagnostic
test locates the checking/search boundary without depending on a fixed number
of validation steps.
Parsing, remaining unmetered walks (including context-free simplification,
substitution and alpha-equivalence), cloning, formatting and
allocation are not fully charged.
Consequently the aggregate allowance is a step toward a whole-pipeline budget,
not a replacement for the process and worker boundaries above.

Initial aggregate-budget validation on 2026-09-04: all 578 core and 27 Wasm tests passed, including the
six aggregate-budget regressions. All 131 teaching files passed the corpus
gate, and all 61 native/browser grading cases passed through release Wasm in
Chrome. Workspace Clippy, formatting, the kernel-boundary check and the
no-default-features core build also passed. The immutable classroom candidate
predates this change; no new candidate was deployed.

The countermodel extension passed the existing countermodel tests and all four
new regressions. The broader run passed 581 core and 27 Wasm tests before the
final quantifier-cleanup regression was added; the affected tests and Clippy
were rerun after that cleanup. All 131 teaching files and native grading
fixtures passed with search metering; the final release Wasm passed all 61
grading cases in Chrome, including after the quantifier cleanup.

After extending metering to legacy validation and normalization, all 584 core
and 27 Wasm tests passed. All 131 teaching files and 61 native grading fixtures
passed, and Chrome verified all 61 cases through the rebuilt release Wasm.
Clippy, formatting, the kernel-boundary check and the no-default-features build
also passed. Complete allocation/whole-pipeline limits remain open.

External limits protect batch automation; they do not establish a complete
in-process work budget or a compact representation of large natural literals.
The browser separately uses worker isolation, cancellation and a ten-second
request timeout. Neither boundary replaces the remaining whole-pipeline budget
work in `STUDENT_READINESS.md`. The browser assignment parity fixture generator
uses a thirty-second subprocess timeout, matching the corpus check allowance.
The earlier fifteen-second fixture limit timed out on the development checkpoint;
timeouts now also identify the fixture being graded. Build commands are outside
these per-check limits.

A September 4 modular-arithmetic trial exposed a concrete limit: certifying
`ModEq(12, mul(27,27), mul(3,3))` reached the 2048 normalization-depth limit
during statement classification. The symbolic congruence-of-squares theorem
and the smaller clock equality check successfully. Compact natural-number
representation remains necessary; a small-looking source expression is not
a guarantee of a small normalized statement.

The follow-up normalization pass releases an application's depth guard before
visiting its replacement term: sequential reductions no longer accumulate as
if they were nested source terms. Opaque constructor chains also use the
iterative path inside application/lambda continuations. The depth and
4,000,000-step limits remain in force. The direct equation `27*27 = 729`
certifies and an incorrect result is rejected. The modular-square example
initially still exceeded the work budget; that failure is addressed below.
These depth changes alone did not complete compact arithmetic.

## Structural-recursion substitution

The concrete modular-square proof now certifies within the unchanged work
budget. Structural reduction substitutes the checked arm's fields, recursive
results, and fixed arguments simultaneously, using the existing capture-safe
substitution operation. It no longer builds administrative lambdas and eagerly
normalizes their bodies and unused arguments. Binder ordering and nested scope
remain covered by the structural-recursion and substitution regressions.

The [regression example](hol/examples/modular_square.ctea) proves
`ModEq(12, mul(27,27), mul(3,3))` from the checked congruence of 27 and 3.
Native/browser grading includes the valid result and rejection of the false
result 8. A local debug CLI check took approximately 12 seconds; this is not
a universal timing guarantee. The representation is still unary, and large
expressions can still exceed the depth or work limits. Compact numerals and
whole-check budgets remain open.

The first browser run after that optimization exposed a stack overflow. The
follow-up makes term cloning iterative, keeps rigid-constructor normalization
inside heap continuations, and traverses constant-headed spines iteratively
in variable shifting, substitution, and type inference. Type inference still
checks every function domain and retains nesting guards; outward shifts still
reject escaping variables. The full modular proof is tested with the CLI's
configured 256 MiB debug stack, and separately in the actual release-Wasm
browser worker. A 16 MiB native debug thread is not equivalent to the optimized
Wasm runtime and is not claimed as a supported stack size for this proof.
