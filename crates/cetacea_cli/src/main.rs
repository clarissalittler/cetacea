use std::env;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process;

use cetacea_core::{
    check_file_at_path, explain_theorem_at_path, goals_at_path, outline, run_tactic_at_path,
    CheckResult, Diagnostic, ExplanationResult, GoalSnapshot, GoalStepResult, Position,
    SourceOutline,
};

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.iter().any(|arg| arg == "-h" || arg == "--help") {
        print_usage();
        return;
    }
    let Some(config) = parse_args(&args) else {
        print_usage();
        process::exit(2);
    };

    if config.interactive {
        if let Err(err) = run_interactive(config.path) {
            eprintln!("error: {err}");
            process::exit(1);
        }
        return;
    }

    process::exit(run_check(&config.path));
}

struct CliConfig {
    interactive: bool,
    path: PathBuf,
}

fn parse_args(args: &[String]) -> Option<CliConfig> {
    let mut interactive = false;
    let mut path = None;
    for arg in args {
        match arg.as_str() {
            "-i" | "--interactive" => interactive = true,
            _ if path.is_none() => path = Some(PathBuf::from(arg)),
            _ => return None,
        }
    }

    Some(CliConfig {
        interactive,
        path: path?,
    })
}

fn print_usage() {
    eprintln!("usage: cetacea [--interactive|-i] <file.ctea>");
}

fn run_check(path: &Path) -> i32 {
    let result = check_file_at_path(path);
    if result.diagnostics.is_empty() {
        print_accepted(&result);
        0
    } else {
        print_diagnostics(&result.diagnostics);
        1
    }
}

struct InteractiveState {
    path: PathBuf,
    outline: SourceOutline,
    last_check: CheckResult,
    selected_theorem: Option<String>,
    next_tactic_index: usize,
    current_goals: Option<GoalStepResult>,
}

impl InteractiveState {
    fn new(path: PathBuf) -> Self {
        Self {
            path,
            outline: SourceOutline::default(),
            last_check: CheckResult::default(),
            selected_theorem: None,
            next_tactic_index: 0,
            current_goals: None,
        }
    }

    fn reload(&mut self) {
        self.outline = load_outline(&self.path);
        self.last_check = check_file_at_path(&self.path);
        if self
            .selected_theorem
            .as_ref()
            .is_none_or(|name| !self.outline.theorems.iter().any(|item| &item.name == name))
        {
            self.selected_theorem = self
                .outline
                .theorems
                .first()
                .map(|theorem| theorem.name.clone());
        }
        self.next_tactic_index = 0;
        self.current_goals = None;
    }

    fn selected_outline_index(&self) -> Option<usize> {
        let selected = self.selected_theorem.as_ref()?;
        self.outline
            .theorems
            .iter()
            .position(|theorem| &theorem.name == selected)
    }
}

fn run_interactive(path: PathBuf) -> io::Result<()> {
    let mut state = InteractiveState::new(path);
    state.reload();

    println!("Cetacea interactive mode");
    println!("File: {}", state.path.display());
    println!("Type `help` for commands.");
    if state.last_check.diagnostics.is_empty() {
        print_accepted_summary(&state.last_check);
    } else {
        print_diagnostics(&state.last_check.diagnostics);
    }
    if let Some(name) = &state.selected_theorem {
        println!("Selected theorem: {name}");
    }

    let stdin = io::stdin();
    loop {
        print!("cetacea> ");
        io::stdout().flush()?;

        let mut line = String::new();
        if stdin.read_line(&mut line)? == 0 {
            println!();
            break;
        }
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if !handle_interactive_command(&mut state, line) {
            break;
        }
    }

    Ok(())
}

fn handle_interactive_command(state: &mut InteractiveState, line: &str) -> bool {
    let (command, rest) = split_command(line);
    match command {
        "q" | "quit" | "exit" => false,
        "h" | "help" | "menu" => {
            print_interactive_help();
            true
        }
        "r" | "reload" => {
            state.reload();
            println!("Reloaded {}", state.path.display());
            if state.last_check.diagnostics.is_empty() {
                print_accepted_summary(&state.last_check);
            } else {
                print_diagnostics(&state.last_check.diagnostics);
            }
            true
        }
        "c" | "check" => {
            state.last_check = check_file_at_path(&state.path);
            if state.last_check.diagnostics.is_empty() {
                print_accepted(&state.last_check);
            } else {
                print_diagnostics(&state.last_check.diagnostics);
            }
            true
        }
        "t" | "theorems" | "outline" => {
            print_outline(state);
            true
        }
        "select" | "s" => {
            select_theorem(state, rest);
            true
        }
        "reset" => {
            reset_selected_theorem(state);
            true
        }
        "step" | "n" | "next" => {
            step_selected_theorem(state, rest);
            true
        }
        "goals" | "g" => {
            show_goals_at_position(state, rest);
            true
        }
        "hints" => {
            print_current_hints(state);
            true
        }
        "search" | "library" | "find" => {
            search_theorems(state, rest);
            true
        }
        "explain" | "interpret" | "why" => {
            explain_selected_or_named_theorem(state, rest);
            true
        }
        "accepted" => {
            print_accepted(&state.last_check);
            true
        }
        "diagnostics" | "errors" => {
            if state.last_check.diagnostics.is_empty() {
                println!("No diagnostics from the last check.");
            } else {
                print_diagnostics(&state.last_check.diagnostics);
            }
            true
        }
        "status" => {
            println!("File: {}", state.path.display());
            println!(
                "Selected theorem: {}",
                state.selected_theorem.as_deref().unwrap_or("(none)")
            );
            println!("Next tactic index: {}", state.next_tactic_index);
            true
        }
        other => {
            println!("Unknown command `{other}`. Type `help` for commands.");
            true
        }
    }
}

fn split_command(line: &str) -> (&str, &str) {
    line.split_once(char::is_whitespace)
        .map(|(command, rest)| (command, rest.trim()))
        .unwrap_or((line, ""))
}

fn print_interactive_help() {
    println!("Commands:");
    println!("  check | c                  check the file");
    println!("  reload | r                 reload file, outline, and check result");
    println!("  theorems | t               list source theorems");
    println!("  select <name|number>       select a theorem from the outline");
    println!("  reset                      show the selected theorem's initial goal");
    println!("  step [count] | n [count]   run one or more tactics in the selected theorem");
    println!("  goals <line> [column]      show goals at a source position");
    println!("  hints                      show hints for the current goals");
    println!("  search <text>              search checked local and imported theorems");
    println!("  explain [theorem]          explain a checked tactic script");
    println!("  accepted                   list accepted root declarations");
    println!("  diagnostics                show diagnostics from the last check");
    println!("  status                     show current interactive state");
    println!("  quit | q                   exit");
}

fn load_outline(path: &Path) -> SourceOutline {
    match fs::read_to_string(path) {
        Ok(source) => outline(&source),
        Err(err) => SourceOutline {
            theorems: Vec::new(),
            diagnostics: vec![Diagnostic {
                span: None,
                location: None,
                message: format!("could not read `{}`", path.display()),
                notes: vec![err.to_string()],
                suggestions: Vec::new(),
            }],
        },
    }
}

fn print_outline(state: &InteractiveState) {
    if !state.outline.diagnostics.is_empty() {
        print_diagnostics(&state.outline.diagnostics);
        return;
    }
    if state.outline.theorems.is_empty() {
        println!("No source theorems.");
        return;
    }
    for (idx, theorem) in state.outline.theorems.iter().enumerate() {
        let marker = if state.selected_theorem.as_ref() == Some(&theorem.name) {
            "*"
        } else {
            " "
        };
        println!(
            "{marker} {:>2}. {} (line {}, {} tactics)",
            idx + 1,
            theorem.name,
            theorem.line,
            theorem.tactic_count
        );
    }
}

fn select_theorem(state: &mut InteractiveState, selector: &str) {
    if selector.is_empty() {
        print_outline(state);
        return;
    }

    let selected = if let Ok(index) = selector.parse::<usize>() {
        state
            .outline
            .theorems
            .get(index.saturating_sub(1))
            .map(|theorem| theorem.name.clone())
    } else {
        state
            .outline
            .theorems
            .iter()
            .find(|theorem| theorem.name == selector)
            .map(|theorem| theorem.name.clone())
    };

    match selected {
        Some(name) => {
            state.selected_theorem = Some(name.clone());
            state.next_tactic_index = 0;
            state.current_goals = None;
            println!("Selected theorem: {name}");
            reset_selected_theorem(state);
        }
        None => println!("No theorem matched `{selector}`."),
    }
}

fn reset_selected_theorem(state: &mut InteractiveState) {
    let Some(index) = state.selected_outline_index() else {
        println!("No theorem selected.");
        return;
    };
    let theorem = &state.outline.theorems[index];
    let result = goals_at_path(
        &state.path,
        Position {
            line: theorem.line,
            column: 1,
        },
    );
    state.next_tactic_index = result.next_tactic_index;
    state.current_goals = Some(result.clone());
    print_goal_result(&result);
}

fn step_selected_theorem(state: &mut InteractiveState, rest: &str) {
    let Some(theorem) = state.selected_theorem.clone() else {
        println!("No theorem selected.");
        return;
    };
    let count = if rest.is_empty() {
        1
    } else {
        match rest.parse::<usize>() {
            Ok(count) if count > 0 => count,
            _ => {
                println!("step count must be a positive integer");
                return;
            }
        }
    };

    let mut result = None;
    for _ in 0..count {
        let step = run_tactic_at_path(&state.path, &theorem, state.next_tactic_index);
        state.next_tactic_index = step.next_tactic_index;
        let should_stop = step.completed || !step.diagnostics.is_empty();
        result = Some(step);
        if should_stop {
            break;
        }
    }

    if let Some(step) = result {
        state.current_goals = Some(step.clone());
        print_goal_result(&step);
    }
}

fn show_goals_at_position(state: &mut InteractiveState, rest: &str) {
    let mut parts = rest.split_whitespace();
    let Some(line) = parts.next().and_then(|part| part.parse::<usize>().ok()) else {
        println!("usage: goals <line> [column]");
        return;
    };
    let column = parts
        .next()
        .and_then(|part| part.parse::<usize>().ok())
        .unwrap_or(1);
    let result = goals_at_path(&state.path, Position { line, column });
    state.next_tactic_index = result.next_tactic_index;
    if let Some(theorem) = &result.theorem {
        state.selected_theorem = Some(theorem.clone());
    }
    state.current_goals = Some(result.clone());
    print_goal_result(&result);
}

fn print_goal_result(result: &GoalStepResult) {
    if !result.diagnostics.is_empty() {
        print_diagnostics(&result.diagnostics);
    }
    match &result.theorem {
        Some(theorem) => println!(
            "{}: tactic {}/{}{}",
            theorem,
            result.next_tactic_index,
            result.tactic_count,
            if result.completed { " (complete)" } else { "" }
        ),
        None => println!("No theorem selected by this proof state."),
    }
    if result.goals.is_empty() {
        println!(
            "{}",
            if result.completed {
                "Complete."
            } else {
                "No goals."
            }
        );
        return;
    }
    for (idx, goal) in result.goals.iter().enumerate() {
        print_goal(idx + 1, goal);
    }
}

fn print_goal(index: usize, goal: &GoalSnapshot) {
    println!("Goal {index}:");
    if goal.context.is_empty() {
        println!("  Context: (empty)");
    } else {
        println!("  Context:");
        for entry in &goal.context {
            println!("    {entry}");
        }
    }
    println!("  Target:");
    println!("    |- {}", goal.target);
    if !goal.hints.is_empty() {
        println!("  Hints:");
        for hint in goal.hints.iter().take(6) {
            println!("    {}: `{}`", hint.title, hint.tactic);
            println!("      {}", hint.detail);
        }
    }
}

fn print_current_hints(state: &InteractiveState) {
    let Some(result) = &state.current_goals else {
        println!("No current goals. Use `reset`, `step`, or `goals <line>` first.");
        return;
    };
    for (idx, goal) in result.goals.iter().enumerate() {
        println!("Goal {} hints:", idx + 1);
        if goal.hints.is_empty() {
            println!("  (none)");
        } else {
            for hint in &goal.hints {
                println!("  {}: `{}`", hint.title, hint.tactic);
                println!("    {}", hint.detail);
            }
        }
    }
}

fn search_theorems(state: &mut InteractiveState, query: &str) {
    if query.is_empty() {
        println!("usage: search <text>");
        return;
    }
    if !state.last_check.diagnostics.is_empty() {
        println!("The last check had diagnostics; search results may be incomplete.");
    }
    let query = query.to_lowercase();
    let mut matches = state
        .last_check
        .theorems
        .iter()
        .filter(|theorem| {
            theorem.name.to_lowercase().contains(&query)
                || theorem.statement.to_lowercase().contains(&query)
        })
        .collect::<Vec<_>>();
    matches.sort_by_key(|theorem| (theorem.is_imported, theorem.name.clone()));

    if matches.is_empty() {
        println!("No matching theorems.");
        return;
    }
    for (idx, theorem) in matches.iter().take(25).enumerate() {
        let origin = if theorem.is_imported {
            "imported"
        } else {
            "local"
        };
        let kind = if theorem.is_axiom { "axiom" } else { "theorem" };
        println!(
            "{:>2}. [{} {kind} {}] {} : {}",
            idx + 1,
            origin,
            theorem.mode_used,
            theorem.name,
            theorem.statement
        );
    }
    if matches.len() > 25 {
        println!("Showing 25 of {} matches.", matches.len());
    }
}

fn explain_selected_or_named_theorem(state: &InteractiveState, name: &str) {
    let theorem = if name.is_empty() {
        match &state.selected_theorem {
            Some(name) => name.as_str(),
            None => {
                println!("No theorem selected.");
                return;
            }
        }
    } else {
        name
    };
    let result = explain_theorem_at_path(&state.path, theorem);
    print_explanation(&result);
}

fn print_explanation(result: &ExplanationResult) {
    if !result.diagnostics.is_empty() && result.steps.is_empty() {
        print_diagnostics(&result.diagnostics);
        return;
    }
    println!(
        "{}{}",
        result.theorem.as_deref().unwrap_or("(unknown theorem)"),
        if result.completed {
            ""
        } else {
            " (incomplete)"
        }
    );
    if let Some(statement) = &result.statement {
        println!("Statement: {statement}");
    }
    for step in &result.steps {
        println!();
        println!("Line {}: {}", step.line, step.tactic);
        println!("  Before: |- {}", step.before.target);
        for sentence in &step.explanation {
            println!("  - {sentence}");
        }
        if step.after.is_empty() {
            println!("  After: current goal closed");
        } else {
            println!("  After:");
            for (idx, goal) in step.after.iter().enumerate() {
                println!("    {}. |- {}", idx + 1, goal.target);
            }
        }
    }
    if !result.diagnostics.is_empty() {
        println!();
        println!("Explanation stopped with diagnostics:");
        print_diagnostics(&result.diagnostics);
    }
}

fn print_accepted_summary(result: &CheckResult) {
    let count = result
        .theorems
        .iter()
        .filter(|theorem| !theorem.is_imported)
        .count();
    println!("Accepted {count} root declarations.");
}

fn print_accepted(result: &CheckResult) {
    let mut accepted = false;
    for theorem in result
        .theorems
        .iter()
        .filter(|theorem| !theorem.is_imported)
    {
        accepted = true;
        let kind = if theorem.is_axiom { "axiom" } else { "theorem" };
        println!("accepted {kind} {} ({})", theorem.name, theorem.mode_used);
    }
    if !accepted {
        println!("accepted file");
    }
}

fn print_diagnostics(diagnostics: &[Diagnostic]) {
    for diagnostic in diagnostics {
        match &diagnostic.location {
            Some(location) => match &location.path {
                Some(path) => eprintln!("error: {path}:{}: {}", location.line, diagnostic.message),
                None => eprintln!("error: line {}: {}", location.line, diagnostic.message),
            },
            None => eprintln!("error: {}", diagnostic.message),
        }
        for note in &diagnostic.notes {
            eprintln!("  note: {note}");
        }
        for suggestion in &diagnostic.suggestions {
            eprintln!("  help: {}", suggestion.title);
            eprintln!("    {}", suggestion.detail);
            if let Some(example) = &suggestion.example {
                eprintln!("    try:\n{}", indent_block(example, "      "));
            }
        }
    }
}

fn indent_block(text: &str, prefix: &str) -> String {
    text.lines()
        .map(|line| format!("{prefix}{line}"))
        .collect::<Vec<_>>()
        .join("\n")
}
