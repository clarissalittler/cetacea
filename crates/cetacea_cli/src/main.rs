use std::env;
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

    let result = cetacea_core::check_file_at_path(&path);
    if result.diagnostics.is_empty() {
        let mut accepted = false;
        for theorem in result
            .theorems
            .into_iter()
            .filter(|theorem| !theorem.is_imported)
        {
            accepted = true;
            let kind = if theorem.is_axiom { "axiom" } else { "theorem" };
            println!("accepted {kind} {} ({})", theorem.name, theorem.mode_used);
        }
        if !accepted {
            println!("accepted file");
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
