use std::fs;
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Output};

struct Workspace(PathBuf);
impl Workspace {
    fn new(name: &str) -> Self {
        let path =
            std::env::temp_dir().join(format!("cetacea-student-{name}-{}", std::process::id()));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }
    fn check(&self, args: &[&str]) -> Output {
        let mut child = Command::new(env!("CARGO_BIN_EXE_cetacea_cli"))
            .current_dir(&self.0)
            .args(args)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        // Drain both pipes while checking: a complete imported-library JSON
        // report can exceed the OS pipe capacity before the child exits.
        let mut stdout = child.stdout.take().unwrap();
        let mut stderr = child.stderr.take().unwrap();
        let stdout_reader = std::thread::spawn(move || {
            let mut bytes = Vec::new();
            stdout.read_to_end(&mut bytes).unwrap();
            bytes
        });
        let stderr_reader = std::thread::spawn(move || {
            let mut bytes = Vec::new();
            stderr.read_to_end(&mut bytes).unwrap();
            bytes
        });
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        loop {
            if let Some(status) = child.try_wait().unwrap() {
                return Output {
                    status,
                    stdout: stdout_reader.join().unwrap(),
                    stderr: stderr_reader.join().unwrap(),
                };
            }
            if std::time::Instant::now() >= deadline {
                child.kill().unwrap();
                let _ = child.wait();
                panic!("checker exceeded the bounded-input deadline");
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
}
impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const HOMEWORK: &str = "import std/nat.ctea as nat\ntheorem homework (n : Nat) : add(n, 0) = n := by\n  exact nat.add_zero_right {n := n}\n";

#[test]
fn homework_and_manifest_work_outside_the_checkout() {
    let workspace = Workspace::new("portable");
    fs::write(workspace.0.join("homework.ctea"), HOMEWORK).unwrap();
    let checked = workspace.check(&["--json", "homework.ctea"]);
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stdout)
    );
    let json = String::from_utf8(checked.stdout).unwrap();
    assert!(json.contains("builtin:std/nat.ctea"), "{json}");
    fs::write(workspace.0.join("policy.ctea-assignment"), "version = 1\nprofile = 'fol+induction'\nrequired_imports = ['builtin:std/nat.ctea']\nrequired_theorem.homework = '(?0 : Nat) : add(?0, 0) = ?0'\n").unwrap();
    let graded = workspace.check(&[
        "--json",
        "--assignment",
        "policy.ctea-assignment",
        "homework.ctea",
    ]);
    assert!(
        graded.status.success(),
        "{}",
        String::from_utf8_lossy(&graded.stdout)
    );
    // A filesystem replacement cannot satisfy a required bundled dependency.
    fs::create_dir_all(workspace.0.join("std")).unwrap();
    fs::write(
        workspace.0.join("std/nat.ctea"),
        "theorem add_zero_right (n : Nat) : add(n, 0) = n := by refl\n",
    )
    .unwrap();
    let replaced = workspace.check(&[
        "--json",
        "--assignment",
        "policy.ctea-assignment",
        "homework.ctea",
    ]);
    assert_eq!(replaced.status.code(), Some(1));
    let json = String::from_utf8(replaced.stdout).unwrap();
    assert!(json.contains("required bundled import"), "{json}");
    // Explicit bundled syntax is independent of the local replacement.
    fs::write(
        workspace.0.join("homework.ctea"),
        HOMEWORK.replace("import std/", "import builtin:std/"),
    )
    .unwrap();
    let explicit = workspace.check(&[
        "--json",
        "--assignment",
        "policy.ctea-assignment",
        "homework.ctea",
    ]);
    assert!(
        explicit.status.success(),
        "{}",
        String::from_utf8_lossy(&explicit.stdout)
    );
}

#[test]
fn bundled_modules_keep_their_own_dependencies() {
    let workspace = Workspace::new("closure");
    fs::create_dir_all(workspace.0.join("std")).unwrap();
    fs::write(
        workspace.0.join("std/nat.ctea"),
        "this is a broken local replacement\n",
    )
    .unwrap();
    fs::write(workspace.0.join("counting.ctea"), "import builtin:std/hol/counting.ctea as C\ntheorem count (S : Set Nat) (xs : C.List Nat) (n : Nat) : C.HasSize(S, xs, n) -> C.length(xs) = n := by\n  exact C.has_size_length {A := Nat; S := S; xs := xs; n := n}\n").unwrap();
    let checked = workspace.check(&["--json", "counting.ctea"]);
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stdout)
    );
    let json = String::from_utf8(checked.stdout).unwrap();
    assert!(json.contains("builtin:std/nat.ctea"), "{json}");
    assert!(json.contains("std/hol/list@1"), "{json}");
    // Transitive dependencies must all be authorized, not just the entry file.
    fs::write(workspace.0.join("policy.ctea-assignment"), "version = 1\nprofile = 'fol+induction'\nallowed_imports = ['builtin:std/hol/counting.ctea', 'std/hol/list@1']\n").unwrap();
    let denied = workspace.check(&[
        "--json",
        "--assignment",
        "policy.ctea-assignment",
        "counting.ctea",
    ]);
    assert_eq!(denied.status.code(), Some(1));
    let json = String::from_utf8(denied.stdout).unwrap();
    assert!(json.contains("builtin:std/nat.ctea"), "{json}");
}

#[test]
fn excessive_student_input_returns_json_without_crashing_or_hanging() {
    let workspace = Workspace::new("parser-limits");
    for statement in [
        format!("{}True{}", "(".repeat(50_000), ")".repeat(50_000)),
        format!("{}True{}", "(".repeat(1_000), ")".repeat(1_000)),
        format!("{}True", "not ".repeat(1_000)),
        std::iter::repeat_n("True", 30)
            .collect::<Vec<_>>()
            .join(" <-> "),
        "1000000000 = 1000000000".to_string(),
    ] {
        fs::write(
            workspace.0.join("oversized.ctea"),
            format!("theorem oversized : {statement} := by trivial\n"),
        )
        .unwrap();
        let output = workspace.check(&["--json", "oversized.ctea"]);
        assert_eq!(
            output.status.code(),
            Some(1),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let json = String::from_utf8(output.stdout).unwrap();
        assert!(
            json.starts_with('{') && json.trim_end().ends_with('}'),
            "{json}"
        );
        assert!(json.contains("parser resource limit"), "{json}");
    }
}

#[test]
fn exact_package_theorem_grants_do_not_follow_aliases_or_open_the_profile() {
    let workspace = Workspace::new("theorem-grants");
    let source = "import std/hol/cardinality@1 as C\nmode constructive\ntheorem demo (A B : Type) (f : A -> B) (xs : C.List A) : True := by\n  have h : C.length(C.map(f, xs)) = C.length(xs) := by\n    exact C.map_length {A := A; B := B; f := f; xs := xs}\n  trivial\n";
    let policy = "version = 1\nprofile = 'fol+induction'\nallowed_imports = ['std/hol/list@1', 'std/hol/finite@1', 'std/hol/cardinality@1']\n";
    fs::write(workspace.0.join("proof.ctea"), source).unwrap();
    fs::write(workspace.0.join("policy.ctea-assignment"), policy).unwrap();
    let args = [
        "--json",
        "--assignment",
        "policy.ctea-assignment",
        "proof.ctea",
    ];
    let denied = workspace.check(&args);
    assert!(!denied.status.success());
    assert!(String::from_utf8_lossy(&denied.stdout).contains("dependency_fragment"));
    let granted = format!("{policy}allowed_theorems = ['std/hol/cardinality@1::map_length']\n");
    fs::write(workspace.0.join("policy.ctea-assignment"), &granted).unwrap();
    let accepted = workspace.check(&args);
    assert!(
        accepted.status.success(),
        "{}",
        String::from_utf8_lossy(&accepted.stdout)
    );
    assert!(String::from_utf8_lossy(&accepted.stdout)
        .contains("\"allowed_theorems\":[\"std/hol/cardinality@1::map_length\"]"));
    fs::write(
        workspace.0.join("proof.ctea"),
        source
            .replace(" as C", " as Renamed")
            .replace("C.", "Renamed."),
    )
    .unwrap();
    assert!(workspace.check(&args).status.success());
    // A local theorem with the requested spelling cannot satisfy a package grant.
    fs::write(
        workspace.0.join("proof.ctea"),
        "theorem map_length : True := by\n  trivial\n",
    )
    .unwrap();
    let fake = workspace.check(&args);
    assert!(!fake.status.success());
    assert!(String::from_utf8_lossy(&fake.stdout).contains("allowed_theorem"));
    // The public map function is not a theorem and cannot receive this grant.
    fs::write(workspace.0.join("proof.ctea"), source).unwrap();
    fs::write(
        workspace.0.join("policy.ctea-assignment"),
        granted.replace("::map_length", "::map"),
    )
    .unwrap();
    assert!(!workspace.check(&args).status.success());
    // The supplied lemma does not authorize a higher-order root statement.
    fs::write(workspace.0.join("policy.ctea-assignment"), &granted).unwrap();
    fs::write(workspace.0.join("proof.ctea"), "import std/hol/cardinality@1 as C\ntheorem own (A B : Type) (f : A -> B) (xs : C.List A) : C.length(C.map(f, xs)) = C.length(xs) := by\n  exact C.map_length {A := A; B := B; f := f; xs := xs}\n").unwrap();
    let own = workspace.check(&args);
    assert!(!own.status.success());
    let json = String::from_utf8_lossy(&own.stdout);
    assert!(json.contains("\"kind\":\"statement_fragment\""), "{json}");
    assert!(json.contains("\"diagnostics\":[]"), "{json}");
}

#[test]
fn bundled_source_grant_supports_the_pigeonhole_client_without_opening_hol() {
    let workspace = Workspace::new("source-grants");
    let source = include_str!("../../../docs/hol/pilot/pigeonhole_client.ctea");
    let manifest = include_str!("../../../docs/hol/pilot/pigeonhole_client.ctea-assignment");
    fs::write(workspace.0.join("proof.ctea"), source).unwrap();
    fs::write(workspace.0.join("policy.ctea-assignment"), manifest).unwrap();
    let args = [
        "--json",
        "--assignment",
        "policy.ctea-assignment",
        "proof.ctea",
    ];
    let accepted = workspace.check(&args);
    assert!(
        accepted.status.success(),
        "{}",
        String::from_utf8_lossy(&accepted.stdout)
    );
    let json = String::from_utf8_lossy(&accepted.stdout);
    assert!(
        json.contains("\"required_fragment\":\"hol\""),
        "receipt facts remain unchanged"
    );
    fs::write(
        workspace.0.join("proof.ctea"),
        source
            .replace(" as P", " as Supplied")
            .replace("P.pigeonhole", "Supplied.pigeonhole"),
    )
    .unwrap();
    assert!(workspace.check(&args).status.success());
    let denied_manifest = manifest
        .lines()
        .filter(|line| !line.starts_with("allowed_theorems"))
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(workspace.0.join("policy.ctea-assignment"), denied_manifest).unwrap();
    let denied = workspace.check(&args);
    assert!(!denied.status.success());
    assert!(String::from_utf8_lossy(&denied.stdout).contains("dependency_fragment"));
}

#[test]
fn source_grants_pin_the_file_and_export_and_reject_untrusted_helpers() {
    let workspace = Workspace::new("source-grant-identity");
    let helper = "theorem helper : True := by\n  trivial\n";
    for file in ["helpers.ctea", "other.ctea"] {
        fs::write(workspace.0.join(file), helper).unwrap();
    }
    let manifest = "version = 1\nprofile = 'fol'\nallowed_imports = ['helpers.ctea', 'other.ctea']\nallowed_theorems = ['helpers.ctea::helper']\n";
    fs::write(workspace.0.join("policy.ctea-assignment"), manifest).unwrap();
    let args = [
        "--json",
        "--assignment",
        "policy.ctea-assignment",
        "proof.ctea",
    ];
    fs::write(workspace.0.join("proof.ctea"), "import helpers.ctea as H\nimport helpers.ctea as R\ntheorem root : True := by\n  exact R.helper\n").unwrap();
    assert!(workspace.check(&args).status.success());
    fs::write(
        workspace.0.join("proof.ctea"),
        "import other.ctea as H\ntheorem root : True := by\n  exact H.helper\n",
    )
    .unwrap();
    let wrong_file = workspace.check(&args);
    assert!(!wrong_file.status.success());
    assert!(String::from_utf8_lossy(&wrong_file.stdout).contains("allowed_theorem"));
    fs::write(
        workspace.0.join("proof.ctea"),
        "import helpers.ctea as H\ntheorem root : True := by\n  exact H.helper\n",
    )
    .unwrap();
    for helper in [
        "axiom helper : True\n",
        "theorem helper : True := by\n  sorry\n",
    ] {
        fs::write(workspace.0.join("helpers.ctea"), helper).unwrap();
        let rejected = workspace.check(&args);
        assert!(!rejected.status.success());
        assert!(String::from_utf8_lossy(&rejected.stdout).contains("allowed_theorem"));
    }
}

#[test]
fn collision_witness_bundle_and_grant_preserve_classical_policy() {
    let workspace = Workspace::new("collision");
    fs::write(
        workspace.0.join("collision.ctea"),
        include_str!("../../../docs/hol/examples/pigeonhole_collision.ctea"),
    )
    .unwrap();
    let checked = workspace.check(&["--hol-shadow", "--json", "collision.ctea"]);
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stdout)
    );
    let policy = include_str!("../../../docs/hol/examples/pigeonhole_collision.ctea-assignment")
        .replace("allow_classical = true", "allow_classical = false");
    fs::write(workspace.0.join("policy.ctea-assignment"), &policy).unwrap();
    let denied = workspace.check(&[
        "--json",
        "--assignment",
        "policy.ctea-assignment",
        "collision.ctea",
    ]);
    assert_eq!(denied.status.code(), Some(1));
    let json = String::from_utf8_lossy(&denied.stdout);
    assert!(
        json.contains("proof feature `classical` is not allowed"),
        "{json}"
    );
    fs::write(
        workspace.0.join("policy.ctea-assignment"),
        policy.replace("allow_classical = false", "allow_classical = true"),
    )
    .unwrap();
    let allowed = workspace.check(&[
        "--json",
        "--assignment",
        "policy.ctea-assignment",
        "collision.ctea",
    ]);
    assert!(
        allowed.status.success(),
        "{}",
        String::from_utf8_lossy(&allowed.stdout)
    );
}

#[test]
fn concrete_square_certifies_and_wrong_result_is_rejected() {
    let workspace = Workspace::new("concrete-square");
    for (result, accepted) in [(729, true), (728, false)] {
        fs::write(
            workspace.0.join("square.ctea"),
            format!("theorem square : mul(27, 27) = {result} := by\n  refl\n"),
        )
        .unwrap();
        let output = workspace.check(&["--hol-profile", "hol", "square.ctea"]);
        assert_eq!(
            output.status.success(),
            accepted,
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        if accepted {
            assert!(stdout.contains("HOL kernel certified 1 declarations"));
        } else {
            assert!(String::from_utf8_lossy(&output.stderr).contains("different numbers"));
        }
    }
}
