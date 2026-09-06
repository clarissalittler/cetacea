//! Command-line checker for Cetacea 2.

use std::process::ExitCode;

use hol_session::{check_path, Options, Policy, Severity};
use hol_syntax::Tier;

fn usage() -> ExitCode {
    eprintln!(
        "usage: cetacea2 [--strict] [--deny-sorry] [--deny-axioms] [--deny-classical] [--json] [--std DIR] [--tier fol|fol_nat|hol] FILE"
    );
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let mut opts = Options {
        std_dir: Some("lib".to_string()),
        ..Options::default()
    };
    let mut json = false;
    let mut file: Option<String> = None;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--strict" => {
                opts.policy.deny_sorry = true;
                opts.policy.deny_axioms = true;
            }
            "--deny-sorry" => opts.policy.deny_sorry = true,
            "--deny-axioms" => opts.policy.deny_axioms = true,
            "--deny-classical" => opts.policy.deny_classical = true,
            "--json" => json = true,
            "--std" => match args.next() {
                Some(dir) => opts.std_dir = Some(dir),
                None => return usage(),
            },
            "--no-std-map" => opts.std_dir = None,
            "--tier" => match args.next().as_deref().and_then(Tier::parse) {
                Some(tier) => opts.tier = Some(tier),
                None => return usage(),
            },
            other if other.starts_with("--") => return usage(),
            other => file = Some(other.to_string()),
        }
    }
    let Some(file) = file else {
        return usage();
    };
    let policy: Policy = opts.policy;
    let Some(result) = check_path(&file, opts) else {
        eprintln!("error: cannot read `{file}`");
        return ExitCode::from(2);
    };
    if json {
        let mut value: serde_json::Value = serde_json::from_str(&result.to_json()).unwrap();
        value["policy"] = serde_json::to_value(policy).unwrap();
        println!("{value}");
    } else {
        let mut printed = false;
        for decl in result.decls.iter().filter(|d| !d.is_imported) {
            println!("{}", decl.render());
            printed = true;
        }
        if !printed && !result.has_errors() {
            println!("accepted file");
        }
        for diag in &result.diagnostics {
            if diag.severity == Severity::Error {
                eprintln!("{}", diag.render());
            } else {
                println!("{}", diag.render());
            }
        }
        for violation in &result.violations {
            eprintln!("error: policy violation: {violation}");
        }
    }
    if result.ok() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}
