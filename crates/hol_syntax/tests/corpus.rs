//! Every `.ctea` file in the repository must parse without errors.

use std::path::{Path, PathBuf};

use hol_syntax::{parse_file, Command, TacticKind};

fn corpus_files() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    for dir in ["std", "examples", "docs/cs250/code", "docs/book/code"] {
        for entry in std::fs::read_dir(root.join(dir)).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().map(|e| e == "ctea").unwrap_or(false) {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

#[test]
fn whole_corpus_parses() {
    let mut failures = Vec::new();
    let mut theorems = 0;
    let mut tactics = 0;
    for path in corpus_files() {
        let source = std::fs::read_to_string(&path).unwrap();
        let output = parse_file(&source);
        for error in &output.errors {
            failures.push(format!(
                "{}:{}: {}",
                path.display(),
                error.span,
                error.message
            ));
        }
        for command in &output.file.commands {
            if let Command::Theorem { proof, .. } = command {
                theorems += 1;
                tactics += count_tactics(proof);
            }
        }
    }
    assert!(
        failures.is_empty(),
        "parse failures:\n{}",
        failures.join("\n")
    );
    assert!(theorems > 400, "only {theorems} theorems parsed");
    assert!(tactics > 2000, "only {tactics} tactics parsed");
}

fn count_tactics(tactics: &[hol_syntax::Tactic]) -> usize {
    tactics
        .iter()
        .map(|t| {
            1 + match &t.kind {
                TacticKind::Cases { arms, .. } | TacticKind::Induction { arms, .. } => {
                    arms.iter().map(|arm| count_tactics(&arm.body)).sum()
                }
                TacticKind::Have {
                    proof: hol_syntax::HaveProof::Block(body),
                    ..
                } => count_tactics(body),
                _ => 0,
            }
        })
        .sum()
}
