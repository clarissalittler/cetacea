//! Resource limits: oversized input is refused with an ordinary error
//! instead of exhausting the stack, and arithmetic stays affordable.
//!
//! The browser build has a small stack and no way to recover from
//! overflowing it, so every unbounded recursion needs a bound a student
//! can read about. Each check runs on its own thread with a known stack
//! so the tests do not depend on the harness's thread size.

use hol_session::{CheckResult, Options, Session, Severity, VirtualFs};

/// What a test needs from a check, as plain data: the result itself
/// holds reference-counted terms and cannot leave its thread.
struct Summary {
    ok: bool,
    has_errors: bool,
    first_error: String,
    first_note: String,
    statuses: Vec<String>,
    /// Total rule applications and number of log entries, per theorem.
    recorded: Vec<(String, u64, usize)>,
}

fn summarize(result: &CheckResult) -> Summary {
    let error = result
        .diagnostics
        .iter()
        .find(|d| d.severity == Severity::Error);
    Summary {
        ok: result.ok(),
        has_errors: result.has_errors(),
        first_error: error.map(|d| d.message.clone()).unwrap_or_default(),
        first_note: error
            .and_then(|d| d.notes.first().cloned())
            .unwrap_or_default(),
        statuses: result.decls.iter().map(|d| d.render()).collect(),
        recorded: result
            .derivations
            .iter()
            .map(|(name, steps)| {
                let total = steps
                    .iter()
                    .flat_map(|step| step.rules.iter().map(|(_, count)| count))
                    .sum();
                let entries = steps.iter().map(|step| step.rules.iter().count()).sum();
                (name.clone(), total, entries)
            })
            .collect(),
    }
}

fn check(source: String) -> Summary {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let fs = VirtualFs::default();
            let result = Session::new(&fs, Options::default()).check(Some("p.ctea"), &source);
            summarize(&result)
        })
        .unwrap()
        .join()
        .expect("the checker must not overflow its stack or panic")
}

#[test]
fn deep_nesting_is_refused_not_overflowed() {
    for source in [
        format!(
            "theorem deep : {}True{} := by\n  trivial\n",
            "(".repeat(20_000),
            ")".repeat(20_000)
        ),
        format!(
            "theorem deep (P : Prop) : {}P := by\n  sorry\n",
            "P -> ".repeat(50_000)
        ),
        format!(
            "theorem deep (P : Prop) : {}P -> True := by\n  intro h\n  trivial\n",
            "not ".repeat(50_000)
        ),
    ] {
        let result = check(source);
        assert!(
            result.first_error.contains("nested too deeply"),
            "{}",
            result.first_error
        );
    }
}

#[test]
fn ordinary_nesting_is_unaffected() {
    let result = check(format!(
        "theorem ok : {}True{} := by\n  trivial\n",
        "(".repeat(40),
        ")".repeat(40)
    ));
    assert!(result.ok, "{}", result.first_error);
    let chain = check(format!(
        "theorem ok (P : Prop) : {}P := by\n  sorry\n",
        "P -> ".repeat(150)
    ));
    assert!(!chain.has_errors, "{}", chain.first_error);
}

#[test]
fn numerals_have_a_stated_limit() {
    let ok = check("logic fol_nat\ntheorem t : 500 = 500 := by\n  refl\n".to_string());
    assert!(ok.ok, "{}", ok.first_error);
    let too_big = check("logic fol_nat\ntheorem t : 1000000 = 1000000 := by\n  refl\n".to_string());
    assert_eq!(
        too_big.first_error,
        "the numeral `1000000` is too large to check"
    );
    assert!(
        too_big.first_note.contains("numerals up to 500"),
        "{}",
        too_big.first_note
    );
}

#[test]
fn arithmetic_by_computation_stays_affordable() {
    // `refl` computes both sides by rewriting with the defining
    // equations. Before beta-normal terms were recognized without being
    // walked, `20 * 20` took several seconds in a release build and
    // `15 * 15 = 225` gave up after 200 passes.
    let start = std::time::Instant::now();
    let result = check(
        "logic fol_nat\ntheorem a : 15 * 15 = 225 := by\n  refl\n\ntheorem b : 20 * 20 = 400 := by\n  refl\n\ntheorem c : 3 * 4 = 13 := by\n  refl\n"
            .to_string(),
    );
    assert_eq!(
        result.statuses,
        vec![
            "accepted theorem a (constructive)",
            "accepted theorem b (constructive)",
            "failed theorem c"
        ]
    );
    assert!(
        start.elapsed().as_secs() < 60,
        "arithmetic took {:?}",
        start.elapsed()
    );
}

#[test]
fn recording_does_not_retain_the_computation() {
    // The kernel's rule log counts rule applications. It must not hold
    // on to the theorems themselves: an earlier version did, and this
    // computation took hundreds of megabytes.
    let result = check("logic fol_nat\ntheorem t : 12 * 12 = 144 := by\n  refl\n".to_string());
    assert!(result.ok, "{}", result.first_error);
    let (_, total, entries) = &result.recorded[0];
    assert!(
        *total > 1_000,
        "expected a long computation, saw {total} rules"
    );
    assert!(
        *entries < 100,
        "the log should be counts, saw {entries} entries"
    );
}
