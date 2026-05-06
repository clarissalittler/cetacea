const wasmPaths = [
  "./pkg/cetacea_wasm.wasm",
  "../target/wasm32-unknown-unknown/release/cetacea_wasm.wasm",
];

const sampleSource = `mode constructive

theorem and_comm (P Q : Prop) : P /\\ Q -> Q /\\ P := by
  intro h
  split
  exact h.right
  exact h.left

mode classical

theorem em_demo (P : Prop) : P \\/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h
`;

const encoder = new TextEncoder();
const decoder = new TextDecoder();

const editor = document.querySelector("#sourceEditor");
const sourceHighlights = document.querySelector("#sourceHighlights");
const checkButton = document.querySelector("#checkButton");
const resetButton = document.querySelector("#resetButton");
const stepButton = document.querySelector("#stepButton");
const theoremSelect = document.querySelector("#theoremSelect");
const statusEl = document.querySelector("#status");
const goalMetaEl = document.querySelector("#goalMeta");
const goalsEl = document.querySelector("#goals");
const tacticsEl = document.querySelector("#tactics");
const proofExplanationEl = document.querySelector("#proofExplanation");
const librarySearchEl = document.querySelector("#librarySearch");
const libraryScopeEl = document.querySelector("#libraryScope");
const theoremLibraryEl = document.querySelector("#theoremLibrary");
const diagnosticsEl = document.querySelector("#diagnostics");
const acceptedEl = document.querySelector("#accepted");

let wasm = null;
let stepIndex = -1;
let activeGoalResult = null;
let cursorSyncTimer = 0;
let theoremLibraryItems = [];
let lastEditorSelection = { start: 0, end: 0 };

editor.value = sampleSource;
rememberEditorSelection();
renderSourceHighlights();
setControls(false);
loadWasm();

checkButton.addEventListener("click", () => {
  if (!wasm) return;
  refreshOutline();
  renderCheck(callSource("cetacea_check", editor.value));
});

resetButton.addEventListener("click", () => {
  if (!wasm) return;
  const selected = theoremSelect.value;
  if (!selected) return;
  const theorem = currentOutline().find((item) => item.name === selected);
  const line = theorem ? theorem.line : 1;
  stepIndex = -1;
  renderGoals(callGoalsAt(editor.value, line, 1));
});

stepButton.addEventListener("click", () => {
  if (!wasm) return;
  const theorem = theoremSelect.value;
  if (!theorem) return;
  const result = callRunTactic(editor.value, theorem, stepIndex + 1);
  stepIndex = result.next_tactic_index - 1;
  renderGoals(result);
});

theoremSelect.addEventListener("change", () => {
  stepIndex = -1;
  const theorem = currentOutline().find((item) => item.name === theoremSelect.value);
  if (theorem && wasm) {
    renderGoals(callGoalsAt(editor.value, theorem.line, 1));
    renderExplanationForSelected();
  }
});

librarySearchEl.addEventListener("input", renderTheoremLibrary);
libraryScopeEl.addEventListener("change", renderTheoremLibrary);

editor.addEventListener("input", () => {
  rememberEditorSelection();
  if (!wasm) return;
  stepIndex = -1;
  activeGoalResult = null;
  refreshOutline();
  renderTactics(null);
  renderExplanationForSelected();
  renderSourceHighlights(null);
  renderTheoremLibrary();
  scheduleCursorSync();
});
editor.addEventListener("click", () => {
  rememberEditorSelection();
  scheduleCursorSync();
});
editor.addEventListener("keyup", () => {
  rememberEditorSelection();
  scheduleCursorSync();
});
editor.addEventListener("select", () => {
  rememberEditorSelection();
  scheduleCursorSync();
});
editor.addEventListener("scroll", syncHighlightScroll);

async function loadWasm() {
  let lastError = null;
  for (const path of wasmPaths) {
    try {
      const response = await fetch(path);
      if (!response.ok) throw new Error(`${response.status} ${response.statusText}`);
      const bytes = await response.arrayBuffer();
      const instance = await WebAssembly.instantiate(bytes, {});
      wasm = instance.instance.exports;
      statusEl.textContent = `Loaded ${path}`;
      statusEl.classList.remove("error");
      setControls(true);
      refreshOutline();
      renderCheck(callSource("cetacea_check", editor.value));
      const first = currentOutline()[0];
      if (first) renderGoals(callGoalsAt(editor.value, first.line, 1));
      renderExplanationForSelected();
      return;
    } catch (error) {
      lastError = error;
    }
  }
  statusEl.textContent = `Wasm module not found: ${lastError?.message ?? "load failed"}`;
  statusEl.classList.add("error");
}

function setControls(enabled) {
  for (const button of [checkButton, resetButton, stepButton]) {
    button.disabled = !enabled;
  }
  theoremSelect.disabled = !enabled;
}

function refreshOutline() {
  const previous = theoremSelect.value;
  const result = callSource("cetacea_outline", editor.value);
  theoremSelect.replaceChildren();
  for (const theorem of result.theorems ?? []) {
    const option = document.createElement("option");
    option.value = theorem.name;
    option.textContent = theorem.name;
    theoremSelect.append(option);
  }
  theoremSelect.dataset.outline = JSON.stringify(result.theorems ?? []);
  if ((result.theorems ?? []).some((item) => item.name === previous)) {
    theoremSelect.value = previous;
  }
  renderDiagnostics(result.diagnostics ?? []);
}

function currentOutline() {
  try {
    return JSON.parse(theoremSelect.dataset.outline || "[]");
  } catch {
    return [];
  }
}

function callSource(exportName, source) {
  const input = writeString(source);
  const resultPtr = wasm[exportName](input.ptr, input.len);
  wasm.cetacea_free(input.ptr, input.len);
  return readResponse(resultPtr);
}

function callGoalsAt(source, line, column) {
  const input = writeString(source);
  const resultPtr = wasm.cetacea_goals_at(input.ptr, input.len, line, column);
  wasm.cetacea_free(input.ptr, input.len);
  return readResponse(resultPtr);
}

function callRunTactic(source, theorem, tacticIndex) {
  const sourceInput = writeString(source);
  const theoremInput = writeString(theorem);
  const resultPtr = wasm.cetacea_run_tactic(
    sourceInput.ptr,
    sourceInput.len,
    theoremInput.ptr,
    theoremInput.len,
    tacticIndex,
  );
  wasm.cetacea_free(sourceInput.ptr, sourceInput.len);
  wasm.cetacea_free(theoremInput.ptr, theoremInput.len);
  return readResponse(resultPtr);
}

function callExplainTheorem(source, theorem) {
  const sourceInput = writeString(source);
  const theoremInput = writeString(theorem);
  const resultPtr = wasm.cetacea_explain_theorem(
    sourceInput.ptr,
    sourceInput.len,
    theoremInput.ptr,
    theoremInput.len,
  );
  wasm.cetacea_free(sourceInput.ptr, sourceInput.len);
  wasm.cetacea_free(theoremInput.ptr, theoremInput.len);
  return readResponse(resultPtr);
}

function writeString(value) {
  const bytes = encoder.encode(value);
  const ptr = wasm.cetacea_alloc(bytes.length);
  new Uint8Array(wasm.memory.buffer, ptr, bytes.length).set(bytes);
  return { ptr, len: bytes.length };
}

function readResponse(ptr) {
  const view = new DataView(wasm.memory.buffer);
  const len = view.getUint32(ptr, true);
  const bytes = new Uint8Array(wasm.memory.buffer, ptr + 4, len).slice();
  wasm.cetacea_free(ptr, len + 4);
  return JSON.parse(decoder.decode(bytes));
}

function cursorPosition(textarea) {
  return cursorPositionFromOffset(textarea.value, textarea.selectionStart);
}

function cursorPositionFromOffset(text, offset) {
  const before = text.slice(0, Math.max(0, Math.min(offset, text.length)));
  const lines = before.split("\n");
  return {
    line: lines.length,
    column: lines[lines.length - 1].length + 1,
  };
}

function currentEditorOffset() {
  return document.activeElement === editor ? editor.selectionStart : lastEditorSelection.start;
}

function rememberEditorSelection() {
  lastEditorSelection = {
    start: editor.selectionStart,
    end: editor.selectionEnd,
  };
}

function syncCursorGoals(options = {}) {
  if (!wasm) return;
  window.clearTimeout(cursorSyncTimer);
  if (document.activeElement === editor) rememberEditorSelection();
  const position = cursorPositionFromOffset(editor.value, currentEditorOffset());
  const result = callGoalsAt(editor.value, position.line, position.column);
  stepIndex = result.next_tactic_index - 1;
  renderGoals(result, { position, announce: options.announce });
}

function scheduleCursorSync() {
  if (!wasm) return;
  window.clearTimeout(cursorSyncTimer);
  cursorSyncTimer = window.setTimeout(syncCursorGoals, 120);
}

function renderCheck(result) {
  renderDiagnostics(result.diagnostics ?? []);
  const theorems = result.theorems ?? [];
  theoremLibraryItems = theorems;
  renderTheoremLibrary();
  acceptedEl.replaceChildren();
  if (theorems.length === 0) {
    acceptedEl.append(empty("No accepted declarations"));
  } else {
    for (const theorem of theorems.filter((item) => !item.is_imported)) {
      const item = document.createElement("div");
      item.className = "accepted-item";
      item.textContent = `${theorem.is_axiom ? "axiom" : "theorem"} ${theorem.name} (${theorem.mode})`;
      acceptedEl.append(item);
    }
  }
  renderExplanationForSelected();
}

function renderExplanationForSelected() {
  if (!wasm || !theoremSelect.value) {
    renderExplanation(null);
    return;
  }
  renderExplanation(callExplainTheorem(editor.value, theoremSelect.value));
}

function renderGoals(result, options = {}) {
  activeGoalResult = result;
  if (result.theorem) theoremSelect.value = result.theorem;
  renderDiagnostics(result.diagnostics ?? []);
  renderTactics(result);
  renderSourceHighlights(result);
  goalsEl.replaceChildren();
  if (result.theorem) {
    goalMetaEl.textContent = `${result.theorem} - ${result.next_tactic_index}/${result.tactic_count}`;
  } else if (options.position) {
    goalMetaEl.textContent = `Cursor line ${options.position.line}, column ${options.position.column}`;
  } else {
    goalMetaEl.textContent = "";
  }
  if (options.announce) {
    const cursorText = options.position
      ? `line ${options.position.line}, column ${options.position.column}`
      : "the selected cursor position";
    statusEl.textContent = result.theorem
      ? `Showing goals at ${cursorText}`
      : `No theorem at ${cursorText}`;
    statusEl.classList.toggle("error", !result.theorem);
  }
  stepButton.disabled =
    !wasm ||
    !result.theorem ||
    result.completed ||
    result.next_tactic_index >= result.tactic_count;

  if ((result.goals ?? []).length === 0) {
    goalsEl.append(empty(result.completed ? "Complete" : "No goals"));
    renderTheoremLibrary();
    return;
  }

  for (const goal of result.goals) {
    const item = document.createElement("div");
    item.className = "goal";
    const context = document.createElement("div");
    context.className = "goal-context";
    context.append(pre((goal.context ?? []).join("\n") || "(empty)"));
    const target = document.createElement("div");
    target.className = "goal-target";
    target.append(pre(`|- ${goal.target}`));
    item.append(context, target, renderGoalHints(goal.hints ?? []));
    goalsEl.append(item);
  }
  renderTheoremLibrary();
}

function renderGoalHints(hints) {
  const shell = document.createElement("div");
  shell.className = "goal-hints";
  if (!hints.length) {
    shell.append(empty("No tactic hints for this goal"));
    return shell;
  }

  const title = document.createElement("div");
  title.className = "hint-heading";
  title.textContent = "Try next";
  shell.append(title);

  for (const hint of hints) {
    const item = document.createElement("div");
    item.className = "hint-item";
    const tactic = document.createElement("button");
    tactic.type = "button";
    tactic.className = "hint-tactic";
    tactic.textContent = hint.tactic;
    addInsertButtonHandlers(tactic, hint.tactic);

    const body = document.createElement("div");
    body.className = "hint-body";
    const hintTitle = document.createElement("div");
    hintTitle.className = "hint-title";
    hintTitle.textContent = hint.title;
    const detail = document.createElement("div");
    detail.className = "hint-detail";
    detail.textContent = hint.detail;
    body.append(hintTitle, detail);
    item.append(tactic, body);
    shell.append(item);
  }
  return shell;
}

function renderTactics(result) {
  tacticsEl.replaceChildren();
  const theoremName = result?.theorem ?? theoremSelect.value;
  const theorem = currentOutline().find((item) => item.name === theoremName);
  if (!theorem || (theorem.tactics ?? []).length === 0) {
    tacticsEl.append(empty("No tactics"));
    return;
  }

  const nextIndex = result?.theorem === theorem.name ? result.next_tactic_index : -1;
  const currentIndex = nextIndex - 1;
  for (const tactic of theorem.tactics) {
    const item = document.createElement("button");
    item.type = "button";
    item.className = "tactic-item";
    if (tactic.index < nextIndex) item.classList.add("is-done");
    if (tactic.index === currentIndex) item.classList.add("is-current");
    if (tactic.index === nextIndex && !result?.completed) item.classList.add("is-next");
    item.setAttribute(
      "aria-label",
      `line ${tactic.line}, tactic ${tactic.index + 1}: ${tactic.text}`,
    );
    item.addEventListener("click", () => {
      moveCursorToLineEnd(tactic.line);
      syncCursorGoals();
    });

    const line = document.createElement("span");
    line.className = "tactic-line";
    line.textContent = tactic.line;
    const text = document.createElement("span");
    text.className = "tactic-text";
    text.textContent = tactic.text;
    item.append(line, text);
    tacticsEl.append(item);
  }
}

function renderExplanation(result) {
  proofExplanationEl.replaceChildren();
  if (!result?.theorem) {
    proofExplanationEl.append(empty("Select a theorem to explain"));
    return;
  }
  if (result.diagnostics?.length && !result.steps?.length) {
    proofExplanationEl.append(empty("No checked proof steps to explain yet"));
    return;
  }

  const meta = document.createElement("div");
  meta.className = "explain-meta";
  meta.textContent = result.completed
    ? `${result.theorem} (${result.mode})`
    : `${result.theorem} (incomplete)`;
  proofExplanationEl.append(meta);

  for (const step of result.steps ?? []) {
    const item = document.createElement("div");
    item.className = "explain-step";

    const head = document.createElement("div");
    head.className = "explain-head";
    const line = document.createElement("span");
    line.className = "explain-line";
    line.textContent = `line ${step.line}`;
    const tactic = document.createElement("code");
    tactic.textContent = step.tactic;
    head.append(line, tactic);

    const before = document.createElement("pre");
    before.className = "explain-before";
    before.textContent = `Before: |- ${step.before.target}`;

    const body = document.createElement("div");
    body.className = "explain-body";
    for (const sentence of step.explanation ?? []) {
      const paragraph = document.createElement("p");
      paragraph.textContent = sentence;
      body.append(paragraph);
    }

    const after = document.createElement("pre");
    after.className = "explain-after";
    const afterGoals = step.after ?? [];
    after.textContent = afterGoals.length
      ? `After:\n${afterGoals.map((goal, idx) => `${idx + 1}. |- ${goal.target}`).join("\n")}`
      : "After: current goal closed";

    item.append(head, before, body, after);
    proofExplanationEl.append(item);
  }

  if (result.diagnostics?.length) {
    const note = document.createElement("div");
    note.className = "explain-warning";
    note.textContent = "The explanation stops at the first failing or incomplete proof step.";
    proofExplanationEl.append(note);
  }
}

function renderSourceHighlights(result = activeGoalResult) {
  sourceHighlights.replaceChildren();
  const lines = editor.value.split("\n");
  const highlight = highlightedLines(result);
  for (const [index, line] of lines.entries()) {
    const lineNumber = index + 1;
    const element = document.createElement("span");
    element.className = "source-line";
    if (lineNumber === highlight.current) element.classList.add("is-current");
    if (lineNumber === highlight.next) element.classList.add("is-next");
    element.textContent = line || " ";
    sourceHighlights.append(element);
  }
  syncHighlightScroll();
}

function highlightedLines(result) {
  if (!result?.theorem) return { current: null, next: null };
  const theorem = currentOutline().find((item) => item.name === result.theorem);
  if (!theorem) return { current: null, next: null };
  const current = (theorem.tactics ?? []).find(
    (tactic) => tactic.index === result.next_tactic_index - 1,
  );
  const next = (theorem.tactics ?? []).find(
    (tactic) => tactic.index === result.next_tactic_index,
  );
  return {
    current: current?.line ?? null,
    next: result.completed ? null : (next?.line ?? null),
  };
}

function syncHighlightScroll() {
  sourceHighlights.scrollTop = editor.scrollTop;
  sourceHighlights.scrollLeft = editor.scrollLeft;
}

function moveCursorToLineEnd(lineNumber) {
  const lines = editor.value.split("\n");
  const before = lines.slice(0, Math.max(0, lineNumber - 1)).join("\n");
  const line = lines[lineNumber - 1] ?? "";
  const offset = (before ? before.length + 1 : 0) + line.length;
  editor.focus();
  editor.setSelectionRange(offset, offset);
  rememberEditorSelection();
}

function renderDiagnostics(diagnostics) {
  diagnosticsEl.replaceChildren();
  if (!diagnostics.length) {
    diagnosticsEl.append(empty("No diagnostics"));
    return;
  }
  for (const diagnostic of diagnostics) {
    const item = document.createElement("div");
    item.className = "diagnostic";
    const title = document.createElement("div");
    title.className = "diagnostic-title";
    const location = diagnostic.location ? `line ${diagnostic.location.line}: ` : "";
    title.textContent = `${location}${diagnostic.message}`;
    item.append(title);
    for (const note of diagnostic.notes ?? []) {
      const noteEl = document.createElement("div");
      noteEl.className = "diagnostic-note";
      noteEl.textContent = note;
      item.append(noteEl);
    }
    for (const suggestion of diagnostic.suggestions ?? []) {
      const help = document.createElement("div");
      help.className = "diagnostic-help";
      const helpTitle = document.createElement("div");
      helpTitle.className = "diagnostic-help-title";
      helpTitle.textContent = suggestion.title;
      const helpDetail = document.createElement("div");
      helpDetail.className = "diagnostic-help-detail";
      helpDetail.textContent = suggestion.detail;
      help.append(helpTitle, helpDetail);
      if (suggestion.example) {
        const example = pre(suggestion.example);
        example.className = "diagnostic-example";
        help.append(example);
      }
      item.append(help);
    }
    diagnosticsEl.append(item);
  }
}

function renderTheoremLibrary() {
  theoremLibraryEl.replaceChildren();
  const query = librarySearchEl.value.trim().toLowerCase();
  const scope = libraryScopeEl.value;
  const suggested = suggestedTheoremNames();

  let items = theoremLibraryItems.filter((theorem) => {
    if (scope === "imported" && !theorem.is_imported) return false;
    if (scope === "local" && theorem.is_imported) return false;
    if (!query) return true;
    return (
      theorem.name.toLowerCase().includes(query) ||
      (theorem.statement ?? "").toLowerCase().includes(query)
    );
  });

  items = items.slice().sort((left, right) => {
    const leftSuggested = suggested.has(left.name) ? 0 : 1;
    const rightSuggested = suggested.has(right.name) ? 0 : 1;
    if (leftSuggested !== rightSuggested) return leftSuggested - rightSuggested;
    if (left.is_imported !== right.is_imported) return left.is_imported ? 1 : -1;
    return left.name.localeCompare(right.name);
  });

  if (!items.length) {
    theoremLibraryEl.append(empty(theoremLibraryItems.length ? "No matching theorems" : "Run Check to load theorems"));
    return;
  }

  for (const theorem of items.slice(0, 80)) {
    const item = document.createElement("div");
    item.className = "library-item";
    if (suggested.has(theorem.name)) item.classList.add("is-suggested");

    const head = document.createElement("div");
    head.className = "library-head";
    const name = document.createElement("button");
    name.type = "button";
    name.className = "library-name";
    name.textContent = theorem.name;
    addInsertButtonHandlers(name, `apply ${theorem.name}`);
    const badges = document.createElement("div");
    badges.className = "library-badges";
    badges.append(
      badge(theorem.is_axiom ? "axiom" : "theorem"),
      badge(theorem.mode),
      badge(theorem.is_imported ? "imported" : "local"),
    );
    if (suggested.has(theorem.name)) badges.append(badge("suggested"));
    head.append(name, badges);

    const statement = document.createElement("pre");
    statement.className = "library-statement";
    statement.textContent = theorem.statement ?? "";
    item.append(head, statement);
    theoremLibraryEl.append(item);
  }

  if (items.length > 80) {
    theoremLibraryEl.append(empty(`Showing 80 of ${items.length} matches`));
  }
}

function suggestedTheoremNames() {
  const known = new Set(theoremLibraryItems.map((theorem) => theorem.name));
  const suggested = new Set();
  for (const goal of activeGoalResult?.goals ?? []) {
    for (const hint of goal.hints ?? []) {
      const match = /^(?:apply|exact)\s+([A-Za-z_][A-Za-z0-9_]*)/.exec(hint.tactic);
      if (match && known.has(match[1])) suggested.add(match[1]);
    }
  }
  return suggested;
}

function badge(text) {
  const element = document.createElement("span");
  element.className = "badge";
  element.textContent = text;
  return element;
}

function addInsertButtonHandlers(button, tactic) {
  button.addEventListener("mousedown", (event) => {
    event.preventDefault();
  });
  button.addEventListener("click", () => insertTacticAfterCursorLine(tactic));
}

function insertTacticAfterCursorLine(tactic) {
  const value = editor.value;
  const start =
    document.activeElement === editor ? editor.selectionStart : lastEditorSelection.start;
  const lineStart = value.lastIndexOf("\n", start - 1) + 1;
  const nextNewline = value.indexOf("\n", start);
  const lineEnd = nextNewline === -1 ? value.length : nextNewline;
  const currentLine = value.slice(lineStart, lineEnd);
  const indent = currentLine.match(/^\s*/)?.[0] ?? "";
  const text = `\n${indent}${tactic}`;
  const insertAt = lineEnd;
  editor.setRangeText(text, insertAt, insertAt, "end");
  editor.focus();
  rememberEditorSelection();
  editor.dispatchEvent(new Event("input", { bubbles: true }));
}

function pre(text) {
  const element = document.createElement("pre");
  element.textContent = text;
  return element;
}

function empty(text) {
  const element = document.createElement("div");
  element.className = "empty";
  element.textContent = text;
  return element;
}
