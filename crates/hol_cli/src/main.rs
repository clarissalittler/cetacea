//! Command-line checker for Cetacea 2.

use std::process::ExitCode;

use hol_session::{
    check_manifest, check_path, manifest_from_result, Manifest, Options, Policy, Severity,
};
use hol_syntax::Tier;

fn usage() -> ExitCode {
    eprintln!(
        "usage: cetacea2 [--strict] [--deny-sorry] [--deny-axioms] [--deny-classical] [--deny-tactics a,b] [--json] [--std DIR] [--tier fol|fol_nat|hol] [--assignment MANIFEST.json | --make-assignment TITLE] FILE"
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
    let mut assignment: Option<String> = None;
    let mut make_assignment: Option<String> = None;
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
            "--deny-tactics" => match args.next() {
                Some(list) => opts
                    .policy
                    .deny_tactics
                    .extend(list.split(',').map(|t| t.trim().to_string())),
                None => return usage(),
            },
            "--assignment" => match args.next() {
                Some(path) => assignment = Some(path),
                None => return usage(),
            },
            "--make-assignment" => match args.next() {
                Some(title) => make_assignment = Some(title),
                None => return usage(),
            },
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
    let manifest: Option<Manifest> = match &assignment {
        Some(path) => match std::fs::read_to_string(path)
            .ok()
            .and_then(|text| serde_json::from_str::<Manifest>(&text).ok())
        {
            Some(manifest) => Some(manifest),
            None => {
                eprintln!("error: cannot read the assignment manifest `{path}`");
                return ExitCode::from(2);
            }
        },
        None => None,
    };
    if let Some(manifest) = &manifest {
        if let Some(tier) = manifest.tier.as_deref().and_then(Tier::parse) {
            opts.tier = Some(tier);
        }
        let policy = manifest.policy.clone();
        opts.policy.deny_sorry |= policy.deny_sorry;
        opts.policy.deny_axioms |= policy.deny_axioms;
        opts.policy.deny_classical |= policy.deny_classical;
        opts.policy.deny_tactics.extend(policy.deny_tactics);
    }
    let policy: Policy = opts.policy.clone();
    let tier_name = opts.tier.map(|t| t.name().to_string());
    let Some(result) = check_path(&file, opts) else {
        eprintln!("error: cannot read `{file}`");
        return ExitCode::from(2);
    };
    if let Some(title) = make_assignment {
        let manifest = manifest_from_result(&result, &title, tier_name.as_deref());
        println!("{}", serde_json::to_string_pretty(&manifest).unwrap());
        return if result.has_errors() {
            ExitCode::from(1)
        } else {
            ExitCode::SUCCESS
        };
    }
    let report = manifest.as_ref().map(|m| check_manifest(&result, m));
    if json {
        let mut value: serde_json::Value = serde_json::from_str(&result.to_json()).unwrap();
        value["policy"] = serde_json::to_value(&policy).unwrap();
        if let Some(report) = &report {
            value["assignment"] = serde_json::to_value(report).unwrap();
        }
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
        if let Some(report) = &report {
            for violation in &report.violations {
                eprintln!("error: assignment violation: {violation}");
            }
            for theorem in &report.theorems {
                println!("assignment {}: {}", theorem.name, theorem.status);
            }
            println!(
                "assignment {}: {}",
                report.title,
                if report.complete && report.violations.is_empty() {
                    "complete"
                } else {
                    "not complete"
                }
            );
        }
    }
    let assignment_ok = report
        .as_ref()
        .map(|r| r.violations.is_empty())
        .unwrap_or(true);
    if result.ok() && assignment_ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}
