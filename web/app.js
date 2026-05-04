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
const checkButton = document.querySelector("#checkButton");
const cursorGoalsButton = document.querySelector("#cursorGoalsButton");
const resetButton = document.querySelector("#resetButton");
const stepButton = document.querySelector("#stepButton");
const theoremSelect = document.querySelector("#theoremSelect");
const statusEl = document.querySelector("#status");
const goalMetaEl = document.querySelector("#goalMeta");
const goalsEl = document.querySelector("#goals");
const diagnosticsEl = document.querySelector("#diagnostics");
const acceptedEl = document.querySelector("#accepted");

let wasm = null;
let stepIndex = -1;

editor.value = sampleSource;
setControls(false);
loadWasm();

checkButton.addEventListener("click", () => {
  if (!wasm) return;
  refreshOutline();
  renderCheck(callSource("cetacea_check", editor.value));
});

cursorGoalsButton.addEventListener("click", () => {
  if (!wasm) return;
  const position = cursorPosition(editor);
  const result = callGoalsAt(editor.value, position.line, position.column);
  if (result.theorem) theoremSelect.value = result.theorem;
  stepIndex = result.next_tactic_index - 1;
  renderGoals(result);
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
  refreshOutline();
});

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
  const result = callSource("cetacea_outline", editor.value);
  theoremSelect.replaceChildren();
  for (const theorem of result.theorems ?? []) {
    const option = document.createElement("option");
    option.value = theorem.name;
    option.textContent = theorem.name;
    theoremSelect.append(option);
  }
  theoremSelect.dataset.outline = JSON.stringify(result.theorems ?? []);
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
  renderDiagnostics(result.diagnostics ?? []);
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
