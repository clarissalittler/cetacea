//! Command-line checker for Cetacea 2.

use std::process::ExitCode;

use hol_session::{
    check_manifest, check_path, manifest_with_policy, Course, Manifest, Options, Policy, Severity,
};
use hol_syntax::Tier;

const USAGE: &str = "usage: cetacea2 [options] FILE
       cetacea2 --course COURSE.json --list-sections

checking:
  --tier fol|fol_nat|hol     logic tier when the file has no `logic` line
  --std DIR                  where `std/` imports resolve (default: lib)
  --json                     machine-readable report
  --derivation               for each finished proof, list the kernel
                             rules every tactic ran

policy:
  --strict                   no `sorry`, no root axioms
  --deny-sorry  --deny-axioms  --deny-classical
  --deny-tactics a,b         tactics that may not be used
  --allow-tactics a,b        the only tactics that may be used
  --deny-theorems p,q        imported theorems that may not be cited
                             (names or `*` patterns such as `add_*`)
  --allow-theorems p,q       the only imported theorems that may be cited
                             (`--allow-theorems none` for no library at all)
  --advisory                 report tactic and theorem rules as warnings

course sections:
  --course COURSE.json       a course definition with named sections
  --section ID               check under that section's tier and rules
  --list-sections            print each section's resolved rules

assignments:
  --make-assignment TITLE    print a manifest for the skeleton FILE
                             (includes the section's rules when one is given)
  --assignment MANIFEST.json grade FILE against a manifest";

fn usage() -> ExitCode {
    eprintln!("{USAGE}");
    ExitCode::from(2)
}

fn list(arg: Option<String>) -> Option<Vec<String>> {
    let text = arg?;
    if text == "none" {
        return Some(Vec::new());
    }
    Some(
        text.split(',')
            .map(|t| t.trim().to_string())
            .filter(|t| !t.is_empty())
            .collect(),
    )
}

fn describe_policy(policy: &Policy) -> Vec<String> {
    let mut lines = Vec::new();
    match policy.available_tactics() {
        Some(tactics) if tactics.is_empty() => lines.push("tactics: none".to_string()),
        Some(tactics) => lines.push(format!("tactics: only {}", tactics.join(", "))),
        None if policy.deny_tactics.is_empty() => lines.push("tactics: all".to_string()),
        None => lines.push(format!(
            "tactics: all except {}",
            policy.deny_tactics.join(", ")
        )),
    }
    match &policy.allow_theorems {
        Some(allowed) if allowed.is_empty() => {
            lines.push("library theorems: none (only theorems proved in the file)".to_string())
        }
        Some(allowed) => lines.push(format!("library theorems: only {}", allowed.join(", "))),
        None => lines.push("library theorems: all".to_string()),
    }
    if !policy.deny_theorems.is_empty() {
        lines.push(format!(
            "library theorems denied: {}",
            policy.deny_theorems.join(", ")
        ));
    }
    let mut flags = Vec::new();
    if policy.deny_sorry {
        flags.push("no sorry");
    }
    if policy.deny_axioms {
        flags.push("no root axioms");
    }
    if policy.deny_classical {
        flags.push("constructive only");
    }
    if policy.advisory {
        flags.push("advisory (warnings only)");
    }
    if !flags.is_empty() {
        lines.push(format!("also: {}", flags.join(", ")));
    }
    lines
}

/// The recorded derivation of every finished root theorem: one row per
/// tactic, in source order.
fn derivation_rows(
    result: &hol_session::CheckResult,
) -> Vec<(String, Vec<(u32, hol_session::analysis::KernelView)>)> {
    let mut theorems = Vec::new();
    for (name, recorded) in &result.derivations {
        let Some((span, steps)) = result.steps.get(name) else {
            continue;
        };
        let mut rows: Vec<(u32, hol_session::analysis::KernelView)> = steps
            .iter()
            .map(|step| {
                (
                    step.span.line,
                    hol_session::analysis::kernel_view(recorded, step.span),
                )
            })
            .collect();
        rows.sort_by_key(|(line, _)| *line);
        theorems.push((span.line, name.clone(), rows));
    }
    theorems.sort_by_key(|(line, _, _)| *line);
    theorems
        .into_iter()
        .map(|(_, name, rows)| (name, rows))
        .collect()
}

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let mut opts = Options {
        std_dir: Some("lib".to_string()),
        ..Options::default()
    };
    let mut flags = Policy::default();
    let mut json = false;
    let mut assignment: Option<String> = None;
    let mut make_assignment: Option<String> = None;
    let mut course_path: Option<String> = None;
    let mut section: Option<String> = None;
    let mut list_sections = false;
    let mut derivation = false;
    let mut file: Option<String> = None;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-h" | "--help" => {
                println!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            "--strict" => {
                flags.deny_sorry = true;
                flags.deny_axioms = true;
            }
            "--deny-sorry" => flags.deny_sorry = true,
            "--deny-axioms" => flags.deny_axioms = true,
            "--deny-classical" => flags.deny_classical = true,
            "--advisory" => flags.advisory = true,
            "--deny-tactics" => match list(args.next()) {
                Some(items) => flags.deny_tactics.extend(items),
                None => return usage(),
            },
            "--allow-tactics" => match list(args.next()) {
                Some(items) => flags
                    .allow_tactics
                    .get_or_insert_with(Vec::new)
                    .extend(items),
                None => return usage(),
            },
            "--deny-theorems" => match list(args.next()) {
                Some(items) => flags.deny_theorems.extend(items),
                None => return usage(),
            },
            "--allow-theorems" => match list(args.next()) {
                Some(items) => flags
                    .allow_theorems
                    .get_or_insert_with(Vec::new)
                    .extend(items),
                None => return usage(),
            },
            "--course" => match args.next() {
                Some(path) => course_path = Some(path),
                None => return usage(),
            },
            "--section" => match args.next() {
                Some(id) => section = Some(id),
                None => return usage(),
            },
            "--list-sections" => list_sections = true,
            "--assignment" => match args.next() {
                Some(path) => assignment = Some(path),
                None => return usage(),
            },
            "--make-assignment" => match args.next() {
                Some(title) => make_assignment = Some(title),
                None => return usage(),
            },
            "--json" => json = true,
            "--derivation" => derivation = true,
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
    let unknown = flags.unknown_tactics();
    if !unknown.is_empty() {
        eprintln!("error: unknown tactic name: {}", unknown.join(", "));
        return ExitCode::from(2);
    }

    let course: Option<Course> = match &course_path {
        Some(path) => {
            let text = match std::fs::read_to_string(path) {
                Ok(text) => text,
                Err(_) => {
                    eprintln!("error: cannot read the course file `{path}`");
                    return ExitCode::from(2);
                }
            };
            match Course::parse(&text) {
                Ok(course) => Some(course),
                Err(message) => {
                    eprintln!("error: {path}: {message}");
                    return ExitCode::from(2);
                }
            }
        }
        None => None,
    };
    if list_sections {
        let Some(course) = &course else {
            eprintln!("error: --list-sections needs --course COURSE.json");
            return ExitCode::from(2);
        };
        if !course.title.is_empty() {
            println!("{}", course.title);
        }
        for entry in &course.sections {
            let resolved = course
                .resolve(&entry.id)
                .expect("a parsed course resolves every section");
            println!();
            if resolved.title.is_empty() {
                println!("{}", resolved.id);
            } else {
                println!("{}: {}", resolved.id, resolved.title);
            }
            if !resolved.description.is_empty() {
                println!("  {}", resolved.description);
            }
            println!(
                "  tier: {}",
                resolved.tier.as_deref().unwrap_or("(file default)")
            );
            for line in describe_policy(&resolved.policy) {
                println!("  {line}");
            }
        }
        return ExitCode::SUCCESS;
    }
    let Some(file) = file else {
        return usage();
    };

    // The section sets the baseline; flags and a manifest only restrict.
    let mut policy = Policy::default();
    if let Some(id) = &section {
        let Some(course) = &course else {
            eprintln!("error: --section needs --course COURSE.json");
            return ExitCode::from(2);
        };
        match course.resolve(id) {
            Ok(resolved) => {
                if let Some(tier) = resolved.tier.as_deref().and_then(Tier::parse) {
                    opts.tier = Some(tier);
                }
                policy = resolved.policy;
            }
            Err(message) => {
                eprintln!("error: {message}");
                return ExitCode::from(2);
            }
        }
    }
    policy.restrict_with(&flags);
    if flags.advisory {
        // `--advisory` relaxes the section's rules to warnings. A
        // manifest, merged below, is graded strictly regardless.
        policy.advisory = true;
    }

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
        policy.restrict_with(&manifest.policy);
    }
    if make_assignment.is_some() {
        // A skeleton is full of `sorry`; its own check runs unrestricted
        // and the rules are written into the manifest instead.
        opts.policy = Policy::default();
    } else {
        opts.policy = policy.clone();
    }
    let tier_name = opts.tier.map(|t| t.name().to_string());
    let Some(result) = check_path(&file, opts) else {
        eprintln!("error: cannot read `{file}`");
        return ExitCode::from(2);
    };
    if let Some(title) = make_assignment {
        let manifest = manifest_with_policy(&result, &title, tier_name.as_deref(), policy);
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
        if derivation {
            let mut all = serde_json::Map::new();
            for (name, steps) in derivation_rows(&result) {
                let rows: Vec<serde_json::Value> = steps
                    .into_iter()
                    .map(|(line, view)| {
                        serde_json::json!({
                            "line": line,
                            "rules": view.rules,
                            "equational_rules": view.equational,
                            "introduces": view.introduces,
                        })
                    })
                    .collect();
                all.insert(name, serde_json::Value::Array(rows));
            }
            value["derivations"] = serde_json::Value::Object(all);
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
        if derivation {
            let source = std::fs::read_to_string(&file).unwrap_or_default();
            let lines: Vec<&str> = source.lines().collect();
            for (name, steps) in derivation_rows(&result) {
                println!("derivation of {name}:");
                for (line, view) in steps {
                    let text = lines
                        .get(line.saturating_sub(1) as usize)
                        .map(|l| l.trim())
                        .unwrap_or("");
                    let mut detail = view.rules.join(", ");
                    if view.equational > 0 {
                        let note = format!(
                            "{} equality step{}",
                            view.equational,
                            if view.equational == 1 { "" } else { "s" }
                        );
                        if detail.is_empty() {
                            detail = note;
                        } else {
                            detail.push_str(&format!(" (+{note})"));
                        }
                    }
                    if detail.is_empty() {
                        detail = "(uses a hypothesis as it stands)".to_string();
                    }
                    if !view.introduces.is_empty() {
                        detail.push_str(&format!("   [introduces {}]", view.introduces.join(", ")));
                    }
                    println!("  line {line:>3}  {text:<36} {detail}");
                }
            }
        }
        // Tactic and theorem rules were already reported at their lines.
        for violation in result
            .violations
            .iter()
            .filter(|v| !result.located_violations.contains(*v))
        {
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
