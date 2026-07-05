use std::env;
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{self, Command, Stdio};

use cetacea_core::{
    check_file_at_path, check_source_at_path, explain_theorem_at_path,
    explain_theorem_in_source_at_path, goals_at_path, goals_at_source_path, outline,
    run_tactic_at_path, CheckResult, Diagnostic, ExplanationResult, GoalSnapshot, GoalStepResult,
    Position, SourceOutline,
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

    match config.mode {
        RunMode::Check => process::exit(run_check(&config.path)),
        RunMode::LineInteractive => {
            if let Err(err) = run_interactive(config.path) {
                eprintln!("error: {err}");
                process::exit(1);
            }
        }
        RunMode::Tui => {
            if let Err(err) = run_tui(config.path) {
                eprintln!("error: {err}");
                process::exit(1);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RunMode {
    Check,
    LineInteractive,
    Tui,
}

struct CliConfig {
    mode: RunMode,
    path: PathBuf,
}

fn parse_args(args: &[String]) -> Option<CliConfig> {
    let mut mode = RunMode::Check;
    let mut path = None;
    for arg in args {
        match arg.as_str() {
            "-i" | "--interactive" | "--tui" => mode = RunMode::Tui,
            "--line" | "--repl" => mode = RunMode::LineInteractive,
            _ if path.is_none() => path = Some(PathBuf::from(arg)),
            _ => return None,
        }
    }

    Some(CliConfig { mode, path: path? })
}

fn print_usage() {
    eprintln!("usage: cetacea [--tui|--interactive|-i|--line] <file.ctea>");
}

fn run_check(path: &Path) -> i32 {
    let result = check_file_at_path(path);
    print_accepted(&result);
    if result.diagnostics.is_empty() {
        0
    } else {
        print_diagnostics(&result.diagnostics);
        1
    }
}

fn run_tui(path: PathBuf) -> io::Result<()> {
    let mut app = TuiApp::open(path)?;
    let _guard = TerminalGuard::enter()?;
    app.refresh_analysis();
    let mut stdout = io::stdout();
    let mut stdin = io::stdin();
    let mut needs_draw = true;

    loop {
        if needs_draw {
            let (rows, cols) = terminal_size();
            app.draw(&mut stdout, rows, cols)?;
            needs_draw = false;
        }
        if app.should_quit {
            break;
        }
        if let Some(key) = read_key(&mut stdin)? {
            app.handle_key(key);
            needs_draw = true;
        }
    }

    Ok(())
}

struct TerminalGuard {
    saved_stty: String,
}

impl TerminalGuard {
    fn enter() -> io::Result<Self> {
        let output = Command::new("stty")
            .arg("-g")
            .stdin(Stdio::inherit())
            .output()?;
        let saved_stty = String::from_utf8_lossy(&output.stdout).trim().to_string();
        let status = Command::new("stty")
            .args(["raw", "-echo", "min", "0", "time", "1"])
            .stdin(Stdio::inherit())
            .status()?;
        if !status.success() {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "failed to put terminal in raw mode",
            ));
        }
        print!("\x1b[?1049h\x1b[?25l\x1b[2J\x1b[H");
        io::stdout().flush()?;
        Ok(Self { saved_stty })
    }
}

impl Drop for TerminalGuard {
    fn drop(&mut self) {
        if !self.saved_stty.is_empty() {
            let _ = Command::new("stty")
                .arg(&self.saved_stty)
                .stdin(Stdio::inherit())
                .status();
        }
        print!("\x1b[0m\x1b[?25h\x1b[?1049l");
        let _ = io::stdout().flush();
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Key {
    Char(char),
    Ctrl(char),
    Backspace,
    Delete,
    Enter,
    Esc,
    Tab,
    Up,
    Down,
    Left,
    Right,
    PageUp,
    PageDown,
    Home,
    End,
    F(u8),
}

fn read_key(stdin: &mut io::Stdin) -> io::Result<Option<Key>> {
    let mut byte = [0_u8; 1];
    if stdin.read(&mut byte)? == 0 {
        return Ok(None);
    }
    match byte[0] {
        b'\r' | b'\n' => Ok(Some(Key::Enter)),
        b'\t' => Ok(Some(Key::Tab)),
        0x7f | 0x08 => Ok(Some(Key::Backspace)),
        0x01..=0x1a => Ok(Some(Key::Ctrl((byte[0] + b'a' - 1) as char))),
        0x1b => read_escape_key(stdin),
        byte if byte.is_ascii_graphic() || byte == b' ' => Ok(Some(Key::Char(byte as char))),
        _ => Ok(None),
    }
}

fn read_escape_key(stdin: &mut io::Stdin) -> io::Result<Option<Key>> {
    let mut seq = [0_u8; 6];
    let mut len = 0;
    while len < seq.len() {
        let read = stdin.read(&mut seq[len..len + 1])?;
        if read == 0 {
            break;
        }
        len += read;
        if len >= 2 && (seq[len - 1].is_ascii_alphabetic() || seq[len - 1] == b'~') {
            break;
        }
    }
    if len == 0 {
        return Ok(Some(Key::Esc));
    }
    let key = match &seq[..len] {
        b"[A" => Key::Up,
        b"[B" => Key::Down,
        b"[C" => Key::Right,
        b"[D" => Key::Left,
        b"[H" | b"OH" => Key::Home,
        b"[F" | b"OF" => Key::End,
        b"[3~" => Key::Delete,
        b"[5~" => Key::PageUp,
        b"[6~" => Key::PageDown,
        b"OP" => Key::F(1),
        b"OQ" => Key::F(2),
        b"OR" => Key::F(3),
        b"OS" => Key::F(4),
        b"[15~" => Key::F(5),
        b"[17~" => Key::F(6),
        b"[18~" => Key::F(7),
        b"[19~" => Key::F(8),
        _ => Key::Esc,
    };
    Ok(Some(key))
}

fn terminal_size() -> (usize, usize) {
    let Ok(output) = Command::new("stty")
        .arg("size")
        .stdin(Stdio::inherit())
        .output()
    else {
        return (24, 80);
    };
    if !output.status.success() {
        return (24, 80);
    }
    let text = String::from_utf8_lossy(&output.stdout);
    let mut parts = text.split_whitespace();
    let rows = parts
        .next()
        .and_then(|part| part.parse::<usize>().ok())
        .unwrap_or(24);
    let cols = parts
        .next()
        .and_then(|part| part.parse::<usize>().ok())
        .unwrap_or(80);
    (rows.max(10), cols.max(40))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TuiFocus {
    Editor,
    Panel,
    Menu,
    Search,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TuiPanel {
    Goals,
    Theorems,
    Search,
    Explain,
    Diagnostics,
    Help,
}

impl TuiPanel {
    fn title(self) -> &'static str {
        match self {
            TuiPanel::Goals => "Goals",
            TuiPanel::Theorems => "Theorems",
            TuiPanel::Search => "Search",
            TuiPanel::Explain => "Explain",
            TuiPanel::Diagnostics => "Diagnostics",
            TuiPanel::Help => "Help",
        }
    }
}

struct TextBuffer {
    lines: Vec<String>,
    dirty: bool,
}

impl TextBuffer {
    fn from_source(source: String) -> Self {
        let mut lines = source.lines().map(str::to_string).collect::<Vec<String>>();
        if lines.is_empty() {
            lines.push(String::new());
        }
        Self {
            lines,
            dirty: false,
        }
    }

    fn to_source(&self) -> String {
        let mut source = self.lines.join("\n");
        source.push('\n');
        source
    }

    fn line_count(&self) -> usize {
        self.lines.len()
    }

    fn line_len(&self, line: usize) -> usize {
        self.lines
            .get(line)
            .map(|line| line.chars().count())
            .unwrap_or_default()
    }

    fn clamp_cursor(&self, cursor_line: &mut usize, cursor_col: &mut usize) {
        *cursor_line = (*cursor_line).min(self.lines.len().saturating_sub(1));
        *cursor_col = (*cursor_col).min(self.line_len(*cursor_line));
    }

    fn insert_char(&mut self, line: usize, col: usize, ch: char) -> (usize, usize) {
        let byte_idx = char_to_byte_index(&self.lines[line], col);
        self.lines[line].insert(byte_idx, ch);
        self.dirty = true;
        (line, col + 1)
    }

    fn insert_newline(&mut self, line: usize, col: usize) -> (usize, usize) {
        let byte_idx = char_to_byte_index(&self.lines[line], col);
        let tail = self.lines[line].split_off(byte_idx);
        self.lines.insert(line + 1, tail);
        self.dirty = true;
        (line + 1, 0)
    }

    fn backspace(&mut self, line: usize, col: usize) -> (usize, usize) {
        if col > 0 {
            let prev = col - 1;
            let start = char_to_byte_index(&self.lines[line], prev);
            let end = char_to_byte_index(&self.lines[line], col);
            self.lines[line].replace_range(start..end, "");
            self.dirty = true;
            (line, prev)
        } else if line > 0 {
            let prev_len = self.line_len(line - 1);
            let current = self.lines.remove(line);
            self.lines[line - 1].push_str(&current);
            self.dirty = true;
            (line - 1, prev_len)
        } else {
            (line, col)
        }
    }

    fn delete(&mut self, line: usize, col: usize) -> (usize, usize) {
        let len = self.line_len(line);
        if col < len {
            let start = char_to_byte_index(&self.lines[line], col);
            let end = char_to_byte_index(&self.lines[line], col + 1);
            self.lines[line].replace_range(start..end, "");
            self.dirty = true;
        } else if line + 1 < self.lines.len() {
            let next = self.lines.remove(line + 1);
            self.lines[line].push_str(&next);
            self.dirty = true;
        }
        (line, col)
    }
}

const UNDO_LIMIT: usize = 200;

#[derive(Clone)]
struct EditSnapshot {
    lines: Vec<String>,
    cursor_line: usize,
    cursor_col: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EditKind {
    InsertChar,
    Backspace,
    Delete,
    Newline,
    Replace,
}

fn char_to_byte_index(text: &str, char_idx: usize) -> usize {
    text.char_indices()
        .nth(char_idx)
        .map(|(idx, _)| idx)
        .unwrap_or(text.len())
}

struct TuiApp {
    path: PathBuf,
    buffer: TextBuffer,
    cursor_line: usize,
    cursor_col: usize,
    row_scroll: usize,
    col_scroll: usize,
    focus: TuiFocus,
    panel: TuiPanel,
    menu_index: usize,
    theorem_index: usize,
    search_index: usize,
    search_query: String,
    selected_theorem: Option<String>,
    quit_confirm: bool,
    undo_stack: Vec<EditSnapshot>,
    redo_stack: Vec<EditSnapshot>,
    last_edit: Option<(EditKind, usize, usize)>,
    saved_lines: Option<Vec<String>>,
    outline: SourceOutline,
    check_result: CheckResult,
    goals: GoalStepResult,
    explanation: ExplanationResult,
    status: String,
    should_quit: bool,
}

impl TuiApp {
    fn open(path: PathBuf) -> io::Result<Self> {
        let source = fs::read_to_string(&path)?;
        let initial_outline = outline(&source);
        let cursor_line = initial_outline
            .theorems
            .first()
            .map(|theorem| theorem.line.saturating_sub(1))
            .unwrap_or(0);
        let buffer = TextBuffer::from_source(source);
        let saved_lines = Some(buffer.lines.clone());
        Ok(Self {
            path,
            buffer,
            cursor_line,
            cursor_col: 0,
            row_scroll: 0,
            col_scroll: 0,
            focus: TuiFocus::Editor,
            panel: TuiPanel::Goals,
            menu_index: 0,
            theorem_index: 0,
            search_index: 0,
            search_query: String::new(),
            selected_theorem: None,
            quit_confirm: false,
            undo_stack: Vec::new(),
            redo_stack: Vec::new(),
            last_edit: None,
            saved_lines,
            outline: initial_outline,
            check_result: CheckResult::default(),
            goals: GoalStepResult::default(),
            explanation: ExplanationResult::default(),
            status: "Loaded file. Ctrl-S saves, Ctrl-Q quits, m opens menu.".to_string(),
            should_quit: false,
        })
    }

    fn source(&self) -> String {
        self.buffer.to_source()
    }

    fn refresh_analysis(&mut self) {
        let source = self.source();
        self.outline = outline(&source);
        self.check_result = check_source_at_path(&source, &self.path);
        self.goals = goals_at_source_path(
            &source,
            &self.path,
            Position {
                line: self.cursor_line + 1,
                column: self.cursor_col + 1,
            },
        );
        if let Some(theorem) = &self.goals.theorem {
            self.selected_theorem = Some(theorem.clone());
            if let Some(index) = self
                .outline
                .theorems
                .iter()
                .position(|item| &item.name == theorem)
            {
                self.theorem_index = index;
            }
        } else if self.selected_theorem.is_none() {
            self.selected_theorem = self.outline.theorems.first().map(|item| item.name.clone());
        }
        if let Some(theorem) = &self.selected_theorem {
            self.explanation = explain_theorem_in_source_at_path(&source, &self.path, theorem);
        } else {
            self.explanation = ExplanationResult::default();
        }
        self.search_index = self
            .search_index
            .min(self.search_results().len().saturating_sub(1));
    }

    fn snapshot(&self) -> EditSnapshot {
        EditSnapshot {
            lines: self.buffer.lines.clone(),
            cursor_line: self.cursor_line,
            cursor_col: self.cursor_col,
        }
    }

    fn push_undo_snapshot(&mut self) {
        if self.undo_stack.len() >= UNDO_LIMIT {
            self.undo_stack.remove(0);
        }
        self.undo_stack.push(self.snapshot());
    }

    /// Called before a mutating edit is applied. Pushes an undo snapshot of
    /// the pre-edit state unless this edit continues a run of consecutive
    /// single-character insertions at the position where the previous
    /// insertion left the cursor.
    fn record_edit(&mut self, kind: EditKind) {
        let coalesce = kind == EditKind::InsertChar
            && self.last_edit == Some((EditKind::InsertChar, self.cursor_line, self.cursor_col));
        if !coalesce {
            self.push_undo_snapshot();
        }
        self.redo_stack.clear();
    }

    fn undo(&mut self) {
        let Some(snapshot) = self.undo_stack.pop() else {
            self.status = "Nothing to undo.".to_string();
            return;
        };
        let current = self.snapshot();
        self.redo_stack.push(current);
        self.restore_snapshot(snapshot);
        self.status = "Undid last edit.".to_string();
    }

    fn redo(&mut self) {
        let Some(snapshot) = self.redo_stack.pop() else {
            self.status = "Nothing to redo.".to_string();
            return;
        };
        self.push_undo_snapshot();
        self.restore_snapshot(snapshot);
        self.status = "Redid last edit.".to_string();
    }

    fn restore_snapshot(&mut self, snapshot: EditSnapshot) {
        self.buffer.lines = snapshot.lines;
        self.cursor_line = snapshot.cursor_line;
        self.cursor_col = snapshot.cursor_col;
        self.buffer
            .clamp_cursor(&mut self.cursor_line, &mut self.cursor_col);
        self.buffer.dirty = match &self.saved_lines {
            Some(saved) => &self.buffer.lines != saved,
            None => true,
        };
        self.last_edit = None;
        self.quit_confirm = false;
        self.refresh_analysis();
    }

    fn handle_key(&mut self, key: Key) {
        match self.focus {
            TuiFocus::Menu => self.handle_menu_key(key),
            TuiFocus::Search => self.handle_search_key(key),
            TuiFocus::Panel => self.handle_panel_key(key),
            TuiFocus::Editor => self.handle_editor_key(key),
        }
    }

    fn handle_editor_key(&mut self, key: Key) {
        match key {
            Key::Ctrl('q') => self.request_quit(),
            Key::Ctrl('s') | Key::F(6) => self.save(),
            Key::Ctrl('r') | Key::F(7) => self.reload(),
            Key::Ctrl('z') => self.undo(),
            Key::Ctrl('y') => self.redo(),
            Key::F(8) => {
                self.refresh_analysis();
                self.status = "Checked current buffer.".to_string();
            }
            Key::F(1) => self.panel = TuiPanel::Help,
            Key::F(2) => {
                self.panel = TuiPanel::Theorems;
                self.focus = TuiFocus::Panel;
            }
            Key::F(3) | Key::Char('/') => {
                self.panel = TuiPanel::Search;
                self.focus = TuiFocus::Search;
            }
            Key::F(4) | Key::Char('e') => {
                self.panel = TuiPanel::Explain;
                self.refresh_analysis();
            }
            Key::F(5) => self.panel = TuiPanel::Diagnostics,
            Key::Char('m') => self.focus = TuiFocus::Menu,
            Key::Tab => self.focus = TuiFocus::Panel,
            Key::Up => self.move_cursor_up(1),
            Key::Down => self.move_cursor_down(1),
            Key::Left => self.move_cursor_left(),
            Key::Right => self.move_cursor_right(),
            Key::PageUp => self.move_cursor_up(10),
            Key::PageDown => self.move_cursor_down(10),
            Key::Home => self.cursor_col = 0,
            Key::End => self.cursor_col = self.buffer.line_len(self.cursor_line),
            Key::Enter => {
                self.record_edit(EditKind::Newline);
                let (line, col) = self
                    .buffer
                    .insert_newline(self.cursor_line, self.cursor_col);
                self.cursor_line = line;
                self.cursor_col = col;
                self.last_edit = Some((EditKind::Newline, line, col));
                self.quit_confirm = false;
                self.refresh_analysis();
            }
            Key::Backspace => {
                let is_noop = self.cursor_line == 0 && self.cursor_col == 0;
                if !is_noop {
                    self.record_edit(EditKind::Backspace);
                }
                let (line, col) = self.buffer.backspace(self.cursor_line, self.cursor_col);
                self.cursor_line = line;
                self.cursor_col = col;
                if !is_noop {
                    self.last_edit = Some((EditKind::Backspace, line, col));
                }
                self.quit_confirm = false;
                self.refresh_analysis();
            }
            Key::Delete => {
                let is_noop = self.cursor_col >= self.buffer.line_len(self.cursor_line)
                    && self.cursor_line + 1 >= self.buffer.line_count();
                if !is_noop {
                    self.record_edit(EditKind::Delete);
                }
                let (line, col) = self.buffer.delete(self.cursor_line, self.cursor_col);
                self.cursor_line = line;
                self.cursor_col = col;
                if !is_noop {
                    self.last_edit = Some((EditKind::Delete, line, col));
                }
                self.quit_confirm = false;
                self.refresh_analysis();
            }
            Key::Char(ch) => {
                self.record_edit(EditKind::InsertChar);
                let (line, col) = self
                    .buffer
                    .insert_char(self.cursor_line, self.cursor_col, ch);
                self.cursor_line = line;
                self.cursor_col = col;
                self.last_edit = Some((EditKind::InsertChar, line, col));
                self.quit_confirm = false;
                self.refresh_analysis();
            }
            _ => {}
        }
    }

    fn handle_panel_key(&mut self, key: Key) {
        match key {
            Key::Ctrl('q') => self.request_quit(),
            Key::Esc | Key::Tab => self.focus = TuiFocus::Editor,
            Key::Char('m') => self.focus = TuiFocus::Menu,
            Key::F(1) => self.panel = TuiPanel::Help,
            Key::F(2) => self.panel = TuiPanel::Theorems,
            Key::F(3) | Key::Char('/') => {
                self.panel = TuiPanel::Search;
                self.focus = TuiFocus::Search;
            }
            Key::F(4) | Key::Char('e') => self.panel = TuiPanel::Explain,
            Key::F(5) => self.panel = TuiPanel::Diagnostics,
            Key::Up => self.move_panel_selection(-1),
            Key::Down => self.move_panel_selection(1),
            Key::PageUp => self.move_panel_selection(-10),
            Key::PageDown => self.move_panel_selection(10),
            Key::Enter => self.activate_panel_selection(),
            Key::Ctrl('s') | Key::F(6) => self.save(),
            Key::Ctrl('r') | Key::F(7) => self.reload(),
            Key::F(8) => {
                self.refresh_analysis();
                self.status = "Checked current buffer.".to_string();
            }
            _ => {}
        }
    }

    fn handle_search_key(&mut self, key: Key) {
        match key {
            Key::Ctrl('q') => self.request_quit(),
            Key::Esc | Key::Tab => self.focus = TuiFocus::Editor,
            Key::Enter => {
                if let Some(name) = self
                    .search_results()
                    .get(self.search_index)
                    .map(|theorem| theorem.name.clone())
                {
                    self.selected_theorem = Some(name.clone());
                    self.explanation =
                        explain_theorem_in_source_at_path(&self.source(), &self.path, &name);
                    self.panel = TuiPanel::Explain;
                    self.focus = TuiFocus::Panel;
                }
            }
            Key::Up => self.move_search_selection(-1),
            Key::Down => self.move_search_selection(1),
            Key::Backspace => {
                self.search_query.pop();
                self.search_index = 0;
            }
            Key::Char(ch) => {
                self.search_query.push(ch);
                self.search_index = 0;
            }
            _ => {}
        }
    }

    fn handle_menu_key(&mut self, key: Key) {
        match key {
            Key::Ctrl('q') => self.request_quit(),
            Key::Esc | Key::Tab => self.focus = TuiFocus::Editor,
            Key::Up => {
                if self.menu_index > 0 {
                    self.menu_index -= 1;
                }
            }
            Key::Down => {
                self.menu_index = (self.menu_index + 1).min(MENU_ITEMS.len().saturating_sub(1));
            }
            Key::Enter => self.activate_menu_item(),
            _ => {}
        }
    }

    fn request_quit(&mut self) {
        if self.buffer.dirty && !self.quit_confirm {
            self.status =
                "Unsaved changes. Press Ctrl-Q again to quit without saving, or Ctrl-S to save."
                    .to_string();
            self.quit_confirm = true;
        } else {
            self.should_quit = true;
        }
    }

    fn save(&mut self) {
        match fs::write(&self.path, self.source()) {
            Ok(()) => {
                self.buffer.dirty = false;
                self.quit_confirm = false;
                self.saved_lines = Some(self.buffer.lines.clone());
                self.status = format!("Saved {}.", self.path.display());
                self.refresh_analysis();
            }
            Err(err) => self.status = format!("Could not save {}: {err}", self.path.display()),
        }
    }

    fn reload(&mut self) {
        match fs::read_to_string(&self.path) {
            Ok(source) => {
                self.record_edit(EditKind::Replace);
                self.last_edit = None;
                self.buffer = TextBuffer::from_source(source);
                self.saved_lines = Some(self.buffer.lines.clone());
                self.quit_confirm = false;
                self.cursor_line = self
                    .cursor_line
                    .min(self.buffer.line_count().saturating_sub(1));
                self.cursor_col = self.cursor_col.min(self.buffer.line_len(self.cursor_line));
                self.status = format!("Reloaded {}.", self.path.display());
                self.refresh_analysis();
            }
            Err(err) => self.status = format!("Could not reload {}: {err}", self.path.display()),
        }
    }

    fn move_cursor_up(&mut self, count: usize) {
        self.cursor_line = self.cursor_line.saturating_sub(count);
        self.buffer
            .clamp_cursor(&mut self.cursor_line, &mut self.cursor_col);
        self.refresh_analysis();
    }

    fn move_cursor_down(&mut self, count: usize) {
        self.cursor_line =
            (self.cursor_line + count).min(self.buffer.line_count().saturating_sub(1));
        self.buffer
            .clamp_cursor(&mut self.cursor_line, &mut self.cursor_col);
        self.refresh_analysis();
    }

    fn move_cursor_left(&mut self) {
        if self.cursor_col > 0 {
            self.cursor_col -= 1;
        } else if self.cursor_line > 0 {
            self.cursor_line -= 1;
            self.cursor_col = self.buffer.line_len(self.cursor_line);
        }
        self.refresh_analysis();
    }

    fn move_cursor_right(&mut self) {
        if self.cursor_col < self.buffer.line_len(self.cursor_line) {
            self.cursor_col += 1;
        } else if self.cursor_line + 1 < self.buffer.line_count() {
            self.cursor_line += 1;
            self.cursor_col = 0;
        }
        self.refresh_analysis();
    }

    fn move_panel_selection(&mut self, delta: isize) {
        match self.panel {
            TuiPanel::Theorems => {
                self.theorem_index = add_clamped(
                    self.theorem_index,
                    delta,
                    self.outline.theorems.len().saturating_sub(1),
                );
            }
            TuiPanel::Search => self.move_search_selection(delta),
            _ => {}
        }
    }

    fn move_search_selection(&mut self, delta: isize) {
        self.search_index = add_clamped(
            self.search_index,
            delta,
            self.search_results().len().saturating_sub(1),
        );
    }

    fn activate_panel_selection(&mut self) {
        match self.panel {
            TuiPanel::Theorems => {
                if let Some(theorem) = self.outline.theorems.get(self.theorem_index) {
                    self.cursor_line = theorem.line.saturating_sub(1);
                    self.cursor_col = 0;
                    self.selected_theorem = Some(theorem.name.clone());
                    self.panel = TuiPanel::Goals;
                    self.focus = TuiFocus::Editor;
                    self.refresh_analysis();
                }
            }
            TuiPanel::Search => {
                if let Some(name) = self
                    .search_results()
                    .get(self.search_index)
                    .map(|theorem| theorem.name.clone())
                {
                    self.selected_theorem = Some(name.clone());
                    self.explanation =
                        explain_theorem_in_source_at_path(&self.source(), &self.path, &name);
                    self.panel = TuiPanel::Explain;
                }
            }
            _ => {}
        }
    }

    fn activate_menu_item(&mut self) {
        match MENU_ITEMS[self.menu_index].action {
            MenuAction::Goals => self.panel = TuiPanel::Goals,
            MenuAction::Theorems => {
                self.panel = TuiPanel::Theorems;
                self.focus = TuiFocus::Panel;
                return;
            }
            MenuAction::Search => {
                self.panel = TuiPanel::Search;
                self.focus = TuiFocus::Search;
                return;
            }
            MenuAction::Explain => {
                self.panel = TuiPanel::Explain;
                self.refresh_analysis();
            }
            MenuAction::Diagnostics => self.panel = TuiPanel::Diagnostics,
            MenuAction::Help => self.panel = TuiPanel::Help,
            MenuAction::Save => self.save(),
            MenuAction::Reload => self.reload(),
            MenuAction::Check => {
                self.refresh_analysis();
                self.status = "Checked current buffer.".to_string();
            }
            MenuAction::Quit => self.request_quit(),
        }
        self.focus = TuiFocus::Editor;
    }

    fn search_results(&self) -> Vec<&cetacea_core::CheckedTheorem> {
        let query = self.search_query.to_lowercase();
        let mut matches = self
            .check_result
            .theorems
            .iter()
            .filter(|theorem| {
                query.is_empty()
                    || theorem.name.to_lowercase().contains(&query)
                    || theorem.statement.to_lowercase().contains(&query)
            })
            .collect::<Vec<_>>();
        matches.sort_by_key(|theorem| (theorem.is_imported, theorem.name.clone()));
        matches
    }

    fn draw(&mut self, stdout: &mut io::Stdout, rows: usize, cols: usize) -> io::Result<()> {
        let panel_min = 24.min(cols.saturating_sub(20)).max(12);
        let editor_max = cols.saturating_sub(panel_min + 1).max(1);
        let editor_target = if cols < 70 {
            (cols * 2) / 3
        } else {
            (cols * 62) / 100
        };
        let editor_width = editor_target.clamp(1, editor_max).max(1);
        let panel_width = cols.saturating_sub(editor_width + 1);
        let body_rows = rows.saturating_sub(3);
        self.keep_cursor_visible(body_rows, editor_width);

        write!(stdout, "\x1b[?25l\x1b[H")?;
        self.draw_top_bar(stdout, cols)?;
        for row in 0..body_rows {
            write!(stdout, "\x1b[{};1H", row + 2)?;
            self.draw_editor_row(stdout, row, editor_width)?;
            write!(stdout, "|")?;
            self.draw_panel_row(stdout, row, panel_width)?;
        }
        self.draw_status_bar(stdout, rows, cols)?;
        if self.focus == TuiFocus::Menu {
            self.draw_menu(stdout, rows, cols)?;
        }
        self.place_cursor(stdout, editor_width)?;
        stdout.flush()
    }

    fn keep_cursor_visible(&mut self, body_rows: usize, editor_width: usize) {
        if self.cursor_line < self.row_scroll {
            self.row_scroll = self.cursor_line;
        } else if self.cursor_line >= self.row_scroll + body_rows {
            self.row_scroll = self.cursor_line.saturating_sub(body_rows.saturating_sub(1));
        }

        let gutter = self.gutter_width();
        let text_width = editor_width.saturating_sub(gutter + 1).max(1);
        if self.cursor_col < self.col_scroll {
            self.col_scroll = self.cursor_col;
        } else if self.cursor_col >= self.col_scroll + text_width {
            self.col_scroll = self.cursor_col.saturating_sub(text_width.saturating_sub(1));
        }
    }

    fn gutter_width(&self) -> usize {
        self.buffer.line_count().to_string().len() + 3
    }

    fn draw_top_bar(&self, stdout: &mut io::Stdout, cols: usize) -> io::Result<()> {
        let dirty = if self.buffer.dirty { "*" } else { "" };
        let focus = match self.focus {
            TuiFocus::Editor => "editor",
            TuiFocus::Panel => "panel",
            TuiFocus::Menu => "menu",
            TuiFocus::Search => "search",
        };
        let title = format!(
            " Cetacea TUI{dirty}  {}  [{}]  F1 Help F2 Theorems F3 Search F4 Explain F5 Diagnostics ",
            self.path.display(),
            focus
        );
        write!(stdout, "\x1b[7m{}\x1b[0m", fit_line(&title, cols))
    }

    fn draw_editor_row(&self, stdout: &mut io::Stdout, row: usize, width: usize) -> io::Result<()> {
        let line_idx = self.row_scroll + row;
        let gutter = self.gutter_width();
        if line_idx >= self.buffer.line_count() {
            write!(stdout, "{}", " ".repeat(width))?;
            return Ok(());
        }
        let marker = if line_idx == self.cursor_line {
            ">"
        } else {
            " "
        };
        let line_no = format!("{marker}{:>width$} ", line_idx + 1, width = gutter - 2);
        let text_width = width.saturating_sub(gutter);
        let text = visible_chars(&self.buffer.lines[line_idx], self.col_scroll, text_width);
        if line_idx == self.cursor_line {
            write!(
                stdout,
                "\x1b[48;5;236m{}{}\x1b[0m",
                line_no,
                fit_line(&text, text_width)
            )
        } else {
            write!(stdout, "{}{}", line_no, fit_line(&text, text_width))
        }
    }

    fn panel_lines(&self, width: usize) -> Vec<String> {
        let mut lines = Vec::new();
        lines.push(format!(" {} ", self.panel.title()));
        lines.push("".to_string());
        match self.panel {
            TuiPanel::Goals => self.goal_panel_lines(&mut lines, width),
            TuiPanel::Theorems => self.theorem_panel_lines(&mut lines),
            TuiPanel::Search => self.search_panel_lines(&mut lines),
            TuiPanel::Explain => self.explain_panel_lines(&mut lines, width),
            TuiPanel::Diagnostics => self.diagnostic_panel_lines(&mut lines, width),
            TuiPanel::Help => self.help_panel_lines(&mut lines),
        }
        lines
    }

    fn goal_panel_lines(&self, lines: &mut Vec<String>, width: usize) {
        if !self.goals.diagnostics.is_empty() {
            lines.push("Current proof state diagnostics:".to_string());
            for diagnostic in &self.goals.diagnostics {
                push_wrapped(lines, &format!("error: {}", diagnostic.message), width);
            }
            return;
        }
        match &self.goals.theorem {
            Some(theorem) => lines.push(format!(
                "{theorem}: tactic {}/{}{}",
                self.goals.next_tactic_index,
                self.goals.tactic_count,
                if self.goals.completed {
                    " complete"
                } else {
                    ""
                }
            )),
            None => lines.push("No theorem at cursor.".to_string()),
        }
        if self.goals.goals.is_empty() {
            lines.push(if self.goals.completed {
                "Complete.".to_string()
            } else {
                "No goals.".to_string()
            });
            return;
        }
        for (idx, goal) in self.goals.goals.iter().enumerate() {
            lines.push("".to_string());
            lines.push(format!("Goal {}", idx + 1));
            if goal.context.is_empty() {
                lines.push("  Context: empty".to_string());
            } else {
                lines.push("  Context:".to_string());
                for entry in &goal.context {
                    push_wrapped(lines, &format!("    {entry}"), width);
                }
            }
            push_wrapped(lines, &format!("  |- {}", goal.target), width);
            if !goal.hints.is_empty() {
                lines.push("  Hints:".to_string());
                for hint in goal.hints.iter().take(4) {
                    push_wrapped(
                        lines,
                        &format!("    {}: {}", hint.title, hint.tactic),
                        width,
                    );
                }
            }
        }
    }

    fn theorem_panel_lines(&self, lines: &mut Vec<String>) {
        if !self.outline.diagnostics.is_empty() {
            lines.push("Outline diagnostics:".to_string());
            for diagnostic in &self.outline.diagnostics {
                lines.push(format!("error: {}", diagnostic.message));
            }
            return;
        }
        if self.outline.theorems.is_empty() {
            lines.push("No source theorems.".to_string());
            return;
        }
        lines.push("Enter jumps to theorem. Tab returns.".to_string());
        for (idx, theorem) in self.outline.theorems.iter().enumerate() {
            let marker = if idx == self.theorem_index { ">" } else { " " };
            lines.push(format!(
                "{marker} {:>2}. {} line {} ({} tactics)",
                idx + 1,
                theorem.name,
                theorem.line,
                theorem.tactic_count
            ));
        }
    }

    fn search_panel_lines(&self, lines: &mut Vec<String>) {
        lines.push(format!("Query: {}", self.search_query));
        lines.push("Type to search. Enter explains result.".to_string());
        for (idx, theorem) in self.search_results().iter().take(40).enumerate() {
            let marker = if idx == self.search_index { ">" } else { " " };
            let origin = if theorem.is_imported {
                "import"
            } else {
                "local"
            };
            lines.push(format!(
                "{marker} {} [{}] {} : {}",
                idx + 1,
                origin,
                theorem.name,
                theorem.statement
            ));
        }
    }

    fn explain_panel_lines(&self, lines: &mut Vec<String>, width: usize) {
        if !self.explanation.diagnostics.is_empty() && self.explanation.steps.is_empty() {
            for diagnostic in &self.explanation.diagnostics {
                push_wrapped(lines, &format!("error: {}", diagnostic.message), width);
            }
            return;
        }
        if let Some(theorem) = &self.explanation.theorem {
            lines.push(format!(
                "{}{}",
                theorem,
                if self.explanation.completed {
                    ""
                } else {
                    " (incomplete)"
                }
            ));
        } else {
            lines.push("No theorem selected.".to_string());
        }
        if let Some(statement) = &self.explanation.statement {
            push_wrapped(lines, &format!("Statement: {statement}"), width);
        }
        for step in self.explanation.steps.iter().take(30) {
            lines.push("".to_string());
            lines.push(format!("Line {}: {}", step.line, step.tactic));
            push_wrapped(lines, &format!("Before: |- {}", step.before.target), width);
            for sentence in &step.explanation {
                push_wrapped(lines, &format!("- {sentence}"), width);
            }
            if step.after.is_empty() {
                lines.push("After: current goal closed".to_string());
            } else {
                for (idx, goal) in step.after.iter().enumerate() {
                    push_wrapped(
                        lines,
                        &format!("After {}: |- {}", idx + 1, goal.target),
                        width,
                    );
                }
            }
        }
    }

    fn diagnostic_panel_lines(&self, lines: &mut Vec<String>, width: usize) {
        if self.check_result.diagnostics.is_empty() {
            lines.push("No diagnostics in current buffer.".to_string());
            return;
        }
        for diagnostic in &self.check_result.diagnostics {
            let location = diagnostic
                .location
                .as_ref()
                .map(|loc| format!("line {}: ", loc.line))
                .unwrap_or_default();
            push_wrapped(
                lines,
                &format!("error: {location}{}", diagnostic.message),
                width,
            );
            for note in &diagnostic.notes {
                push_wrapped(lines, &format!("  note: {note}"), width);
            }
            for suggestion in &diagnostic.suggestions {
                push_wrapped(lines, &format!("  help: {}", suggestion.title), width);
                push_wrapped(lines, &format!("    {}", suggestion.detail), width);
            }
            lines.push("".to_string());
        }
    }

    fn help_panel_lines(&self, lines: &mut Vec<String>) {
        lines.extend([
            "Editor keys".to_string(),
            "  arrows/PageUp/PageDown move cursor".to_string(),
            "  typing edits the proof buffer".to_string(),
            "  Ctrl-S saves".to_string(),
            "  Ctrl-Z undoes, Ctrl-Y redoes".to_string(),
            "  Ctrl-R reloads from disk".to_string(),
            "  Ctrl-Q quits".to_string(),
            "".to_string(),
            "Menus and panels".to_string(),
            "  m opens the command menu".to_string(),
            "  Tab switches between editor and panel".to_string(),
            "  F2 theorem outline".to_string(),
            "  F3 theorem search".to_string(),
            "  F4 proof explainer".to_string(),
            "  F5 diagnostics".to_string(),
            "  F8 re-checks current buffer".to_string(),
        ]);
    }

    fn draw_panel_row(&self, stdout: &mut io::Stdout, row: usize, width: usize) -> io::Result<()> {
        let lines = self.panel_lines(width);
        let line = lines.get(row).map(String::as_str).unwrap_or("");
        if row == 0 {
            write!(stdout, "\x1b[1m{}\x1b[0m", fit_line(line, width))
        } else {
            write!(stdout, "{}", fit_line(line, width))
        }
    }

    fn draw_status_bar(&self, stdout: &mut io::Stdout, rows: usize, cols: usize) -> io::Result<()> {
        let diag_count = self.check_result.diagnostics.len();
        let dirty = if self.buffer.dirty {
            "modified"
        } else {
            "saved"
        };
        let status = format!(
            " {} | {} | line {}, col {} | {} diagnostic(s) | {} ",
            dirty,
            self.selected_theorem.as_deref().unwrap_or("no theorem"),
            self.cursor_line + 1,
            self.cursor_col + 1,
            diag_count,
            self.status
        );
        write!(
            stdout,
            "\x1b[{};1H\x1b[7m{}\x1b[0m",
            rows.saturating_sub(1),
            fit_line(&status, cols)
        )?;
        write!(
            stdout,
            "\x1b[{};1H{}",
            rows,
            fit_line(
                " Ctrl-S save  Ctrl-Z undo  Ctrl-Y redo  Ctrl-R reload  Ctrl-Q quit  m menu  Tab panel  / search ",
                cols
            )
        )
    }

    fn draw_menu(&self, stdout: &mut io::Stdout, rows: usize, cols: usize) -> io::Result<()> {
        let width = 32.min(cols.saturating_sub(4)).max(20);
        let height = MENU_ITEMS.len() + 2;
        let top = rows.saturating_sub(height) / 2;
        let left = cols.saturating_sub(width) / 2;
        write!(stdout, "\x1b[{};{}H+{}+", top, left, "-".repeat(width - 2))?;
        for (idx, item) in MENU_ITEMS.iter().enumerate() {
            write!(stdout, "\x1b[{};{}H|", top + idx + 1, left)?;
            let label = format!(
                " {} {}",
                if idx == self.menu_index { ">" } else { " " },
                item.label
            );
            if idx == self.menu_index {
                write!(stdout, "\x1b[7m{}\x1b[0m", fit_line(&label, width - 2))?;
            } else {
                write!(stdout, "{}", fit_line(&label, width - 2))?;
            }
            write!(stdout, "|")?;
        }
        write!(
            stdout,
            "\x1b[{};{}H+{}+",
            top + height - 1,
            left,
            "-".repeat(width - 2)
        )
    }

    fn place_cursor(&self, stdout: &mut io::Stdout, editor_width: usize) -> io::Result<()> {
        if self.focus != TuiFocus::Editor {
            return write!(stdout, "\x1b[?25l");
        }
        let gutter = self.gutter_width();
        let row = self.cursor_line.saturating_sub(self.row_scroll) + 2;
        let col = gutter + self.cursor_col.saturating_sub(self.col_scroll) + 1;
        if col <= editor_width {
            write!(stdout, "\x1b[?25h\x1b[{row};{col}H")
        } else {
            write!(stdout, "\x1b[?25l")
        }
    }
}

#[derive(Clone, Copy)]
enum MenuAction {
    Goals,
    Theorems,
    Search,
    Explain,
    Diagnostics,
    Help,
    Save,
    Reload,
    Check,
    Quit,
}

struct MenuItem {
    label: &'static str,
    action: MenuAction,
}

const MENU_ITEMS: &[MenuItem] = &[
    MenuItem {
        label: "Goals",
        action: MenuAction::Goals,
    },
    MenuItem {
        label: "Theorems",
        action: MenuAction::Theorems,
    },
    MenuItem {
        label: "Search",
        action: MenuAction::Search,
    },
    MenuItem {
        label: "Explain",
        action: MenuAction::Explain,
    },
    MenuItem {
        label: "Diagnostics",
        action: MenuAction::Diagnostics,
    },
    MenuItem {
        label: "Help",
        action: MenuAction::Help,
    },
    MenuItem {
        label: "Save",
        action: MenuAction::Save,
    },
    MenuItem {
        label: "Reload",
        action: MenuAction::Reload,
    },
    MenuItem {
        label: "Check",
        action: MenuAction::Check,
    },
    MenuItem {
        label: "Quit",
        action: MenuAction::Quit,
    },
];

fn add_clamped(current: usize, delta: isize, max: usize) -> usize {
    if delta.is_negative() {
        current.saturating_sub(delta.unsigned_abs()).min(max)
    } else {
        current.saturating_add(delta as usize).min(max)
    }
}

fn visible_chars(text: &str, start: usize, width: usize) -> String {
    text.chars().skip(start).take(width).collect()
}

fn fit_line(text: &str, width: usize) -> String {
    let mut result = text.chars().take(width).collect::<String>();
    let len = result.chars().count();
    if len < width {
        result.push_str(&" ".repeat(width - len));
    }
    result
}

fn push_wrapped(lines: &mut Vec<String>, text: &str, width: usize) {
    let wrap_width = width.max(8);
    let mut remaining = text.trim_end();
    while remaining.chars().count() > wrap_width {
        let mut split_at = 0;
        let mut count = 0;
        for (idx, ch) in remaining.char_indices() {
            if count >= wrap_width {
                break;
            }
            if ch.is_whitespace() {
                split_at = idx;
            }
            count += 1;
        }
        if split_at == 0 {
            split_at = char_to_byte_index(remaining, wrap_width);
        }
        lines.push(remaining[..split_at].trim_end().to_string());
        remaining = remaining[split_at..].trim_start();
    }
    lines.push(remaining.to_string());
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
        let mut notes = vec![theorem.mode_used.to_string()];
        if theorem.uses_sorry {
            notes.push("incomplete: uses sorry".to_string());
        }
        if !theorem.is_axiom && !theorem.axiom_deps.is_empty() {
            notes.push(format!("axioms: {}", theorem.axiom_deps.join(", ")));
        }
        println!("accepted {kind} {} ({})", theorem.name, notes.join("; "));
    }
    if !accepted && result.diagnostics.is_empty() {
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
