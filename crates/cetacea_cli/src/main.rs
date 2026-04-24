use std::env;
use std::fs;
use std::process;

fn main() {
    let mut args = env::args().skip(1);
    let Some(path) = args.next() else {
        eprintln!("usage: cetacea <file.ctea>");
        process::exit(2);
    };

    if args.next().is_some() {
        eprintln!("usage: cetacea <file.ctea>");
        process::exit(2);
    }

    let source = match fs::read_to_string(&path) {
        Ok(source) => source,
        Err(err) => {
            eprintln!("error: could not read `{path}`: {err}");
            process::exit(1);
        }
    };

    let result = cetacea_core::check_file(&source);
    if result.diagnostics.is_empty() {
        for theorem in result.theorems {
            println!("accepted theorem {} ({})", theorem.name, theorem.mode_used);
        }
        return;
    }

    for diagnostic in result.diagnostics {
        eprintln!("error: {}", diagnostic.message);
        for note in diagnostic.notes {
            eprintln!("  note: {note}");
        }
    }
    process::exit(1);
}
