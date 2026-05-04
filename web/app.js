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
const cursorGoalsButton = document.querySelector("#cursorGoalsButton");
const resetButton = document.querySelector("#resetButton");
const stepButton = document.querySelector("#stepButton");
const theoremSelect = document.querySelector("#theoremSelect");
const statusEl = document.querySelector("#status");
const goalMetaEl = document.querySelector("#goalMeta");
const goalsEl = document.querySelector("#goals");
const tacticsEl = document.querySelector("#tactics");
const diagnosticsEl = document.querySelector("#diagnostics");
const acceptedEl = document.querySelector("#accepted");

let wasm = null;
let stepIndex = -1;
let activeGoalResult = null;
let cursorSyncTimer = 0;

editor.value = sampleSource;
renderSourceHighlights();
setControls(false);
loadWasm();

checkButton.addEventListener("click", () => {
  if (!wasm) return;
  refreshOutline();
  renderCheck(callSource("cetacea_check", editor.value));
});

cursorGoalsButton.addEventListener("click", () => {
  syncCursorGoals();
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
  }
});

editor.addEventListener("input", () => {
  if (!wasm) return;
  stepIndex = -1;
  activeGoalResult = null;
  refreshOutline();
  renderTactics(null);
  renderSourceHighlights(null);
  scheduleCursorSync();
});
editor.addEventListener("click", scheduleCursorSync);
editor.addEventListener("keyup", scheduleCursorSync);
editor.addEventListener("select", scheduleCursorSync);
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
      return;
    } catch (error) {
      lastError = error;
    }
  }
  statusEl.textContent = `Wasm module not found: ${lastError?.message ?? "load failed"}`;
  statusEl.classList.add("error");
}

function setControls(enabled) {
  for (const button of [checkButton, cursorGoalsButton, resetButton, stepButton]) {
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
  const before = textarea.value.slice(0, textarea.selectionStart);
  const lines = before.split("\n");
  return {
    line: lines.length,
    column: lines[lines.length - 1].length + 1,
  };
}

function syncCursorGoals() {
  if (!wasm) return;
  window.clearTimeout(cursorSyncTimer);
  const position = cursorPosition(editor);
  const result = callGoalsAt(editor.value, position.line, position.column);
  stepIndex = result.next_tactic_index - 1;
  renderGoals(result);
}

function scheduleCursorSync() {
  if (!wasm) return;
  window.clearTimeout(cursorSyncTimer);
  cursorSyncTimer = window.setTimeout(syncCursorGoals, 120);
}

function renderCheck(result) {
  renderDiagnostics(result.diagnostics ?? []);
  const theorems = result.theorems ?? [];
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
}

function renderGoals(result) {
  activeGoalResult = result;
  if (result.theorem) theoremSelect.value = result.theorem;
  renderDiagnostics(result.diagnostics ?? []);
  renderTactics(result);
  renderSourceHighlights(result);
  goalsEl.replaceChildren();
  goalMetaEl.textContent = result.theorem
    ? `${result.theorem} - ${result.next_tactic_index}/${result.tactic_count}`
    : "";
  stepButton.disabled =
    !wasm ||
    !result.theorem ||
    result.completed ||
    result.next_tactic_index >= result.tactic_count;

  if ((result.goals ?? []).length === 0) {
    goalsEl.append(empty(result.completed ? "Complete" : "No goals"));
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
    item.append(context, target);
    goalsEl.append(item);
  }
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
    diagnosticsEl.append(item);
  }
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
