// Cetacea 2 browser UI: CodeMirror editor on the left, proof state on
// the right, the checker in a Web Worker. No build step: CodeMirror is
// loaded as ES modules from a CDN with pinned versions.

import { basicSetup } from "https://esm.sh/codemirror@6.0.1";
import { EditorState, StateField, StateEffect, RangeSetBuilder } from "https://esm.sh/@codemirror/state@6";
import { EditorView, Decoration, keymap } from "https://esm.sh/@codemirror/view@6";
import { indentWithTab } from "https://esm.sh/@codemirror/commands@6";
import { EXAMPLES } from "./examples.js";

const STORAGE_SOURCE = "cetacea2.source";
const STORAGE_TIER = "cetacea2.tier";

const statusEl = document.getElementById("status");
const goalsEl = document.getElementById("goals");
const goalMetaEl = document.getElementById("goalMeta");
const diagnosticsEl = document.getElementById("diagnostics");
const hintsEl = document.getElementById("hints");
const explanationEl = document.getElementById("explanation");
const libraryEl = document.getElementById("library");
const librarySearchEl = document.getElementById("librarySearch");
const libraryScopeEl = document.getElementById("libraryScope");
const exampleSelect = document.getElementById("exampleSelect");
const tierSelect = document.getElementById("tierSelect");
const checkButton = document.getElementById("checkButton");
const hintButton = document.getElementById("hintButton");
const downloadButton = document.getElementById("downloadButton");

// ---------------------------------------------------------------------
// Worker
// ---------------------------------------------------------------------

const worker = new Worker("./worker.js", { type: "module" });
const pending = new Map();
let nextId = 1;

function request(kind, payload) {
  const id = nextId++;
  return new Promise((resolve, reject) => {
    pending.set(id, { resolve, reject });
    worker.postMessage({ id, kind, ...payload });
  });
}

worker.onmessage = (event) => {
  const { id, result, error } = event.data;
  const entry = pending.get(id);
  if (!entry) return;
  pending.delete(id);
  if (error) entry.reject(new Error(error));
  else entry.resolve(result);
};

// ---------------------------------------------------------------------
// Editor with line decorations for errors and the current step
// ---------------------------------------------------------------------

const setLineMarks = StateEffect.define();

const errorLine = Decoration.line({ class: "cm-error-line" });
const stepLine = Decoration.line({ class: "cm-current-step" });

const lineMarks = StateField.define({
  create() {
    return Decoration.none;
  },
  update(marks, transaction) {
    for (const effect of transaction.effects) {
      if (effect.is(setLineMarks)) {
        const builder = new RangeSetBuilder();
        const doc = transaction.state.doc;
        const entries = effect.value
          .filter((m) => m.line >= 1 && m.line <= doc.lines)
          .sort((a, b) => a.line - b.line);
        let last = -1;
        for (const mark of entries) {
          if (mark.line === last) continue;
          last = mark.line;
          const from = doc.line(mark.line).from;
          builder.add(from, from, mark.kind === "error" ? errorLine : stepLine);
        }
        return builder.finish();
      }
    }
    return transaction.docChanged ? marks.map(transaction.changes) : marks;
  },
  provide: (field) => EditorView.decorations.from(field),
});

let analysis = null;
let analysisSource = "";
let debounceTimer = null;
let checking = false;

function currentLine() {
  const pos = editor.state.selection.main.head;
  return editor.state.doc.lineAt(pos).number;
}

const editor = new EditorView({
  parent: document.getElementById("editor"),
  state: EditorState.create({
    doc: loadSavedSource(),
    extensions: [
      basicSetup,
      keymap.of([indentWithTab]),
      lineMarks,
      EditorView.updateListener.of((update) => {
        if (update.docChanged) {
          saveSource();
          scheduleAnalysis();
        }
        if (update.selectionSet || update.docChanged) {
          renderCursorPanels();
        }
      }),
    ],
  }),
});

function loadSavedSource() {
  try {
    const saved = localStorage.getItem(STORAGE_SOURCE);
    if (saved) return saved;
  } catch (_) {
    /* storage unavailable */
  }
  return EXAMPLES[0].source;
}

function saveSource() {
  try {
    localStorage.setItem(STORAGE_SOURCE, editor.state.doc.toString());
  } catch (_) {
    /* storage unavailable */
  }
}

function setSource(text) {
  editor.dispatch({
    changes: { from: 0, to: editor.state.doc.length, insert: text },
    selection: { anchor: 0 },
  });
}

function insertAfterLine(lineNumber, text) {
  const line = editor.state.doc.line(lineNumber);
  const indent = line.text.match(/^\s*/)[0];
  const block = text
    .split("\n")
    .map((t) => indent + t)
    .join("\n");
  editor.dispatch({
    changes: { from: line.to, insert: "\n" + block },
    selection: { anchor: line.to + 1 + block.length },
  });
  editor.focus();
}

function options() {
  return { tier: tierSelect.value, path: "web/main.ctea" };
}

// ---------------------------------------------------------------------
// Analysis
// ---------------------------------------------------------------------

function scheduleAnalysis() {
  clearTimeout(debounceTimer);
  debounceTimer = setTimeout(runAnalysis, 250);
}

async function runAnalysis() {
  const source = editor.state.doc.toString();
  checking = true;
  statusEl.textContent = "Checking…";
  statusEl.className = "status";
  try {
    const result = await request("analyze", { source, options: options() });
    if (source !== editor.state.doc.toString()) return; // stale
    analysis = result;
    analysisSource = source;
    renderStatus();
    renderDiagnostics();
    renderLibrary();
    renderCursorPanels();
  } catch (error) {
    statusEl.textContent = `Checker error: ${error.message}`;
    statusEl.className = "status error";
  } finally {
    checking = false;
  }
}

function renderStatus() {
  const local = analysis.declarations.filter((d) => !d.is_imported);
  const accepted = local.filter((d) => d.status === "accepted").length;
  const incomplete = local.filter((d) => d.status === "incomplete").length;
  const failed = local.filter((d) => d.status === "failed").length;
  const axioms = local.filter((d) => d.status === "trusted_axiom").length;
  const errors = analysis.diagnostics.filter((d) => d.severity === "error").length;
  const parts = [];
  if (accepted) parts.push(`${accepted} accepted`);
  if (incomplete) parts.push(`${incomplete} incomplete`);
  if (failed) parts.push(`${failed} failed`);
  if (axioms) parts.push(`${axioms} axiom${axioms === 1 ? "" : "s"}`);
  if (errors) parts.push(`${errors} error${errors === 1 ? "" : "s"}`);
  if (parts.length === 0) parts.push("no declarations yet");
  statusEl.textContent = `${parts.join(", ")} · logic ${analysis.tier}, mode ${analysis.mode}`;
  statusEl.className = "status " + (errors ? "error" : "ok");
}

function renderDiagnostics() {
  diagnosticsEl.replaceChildren();
  const items = analysis.diagnostics;
  if (items.length === 0) {
    diagnosticsEl.appendChild(empty("Nothing to report."));
    updateMarks();
    return;
  }
  for (const diag of items) {
    const div = document.createElement("div");
    div.className = `diag ${diag.severity}`;
    const where = document.createElement("div");
    where.className = "where";
    where.textContent = `${diag.severity} · line ${diag.line}`;
    const message = document.createElement("div");
    message.textContent = diag.message;
    div.append(where, message);
    if (diag.notes.length) {
      const list = document.createElement("ul");
      for (const note of diag.notes) {
        const li = document.createElement("li");
        li.textContent = note;
        list.appendChild(li);
      }
      div.appendChild(list);
    }
    if (diag.suggestion) {
      const tryEl = document.createElement("div");
      tryEl.className = "try";
      tryEl.append("try: ");
      const code = document.createElement("code");
      code.textContent = diag.suggestion;
      tryEl.appendChild(code);
      div.appendChild(tryEl);
    }
    div.addEventListener("click", () => jumpToLine(diag.line));
    diagnosticsEl.appendChild(div);
  }
  updateMarks();
}

function jumpToLine(lineNumber) {
  const lines = editor.state.doc.lines;
  const clamped = Math.max(1, Math.min(lineNumber, lines));
  const line = editor.state.doc.line(clamped);
  editor.dispatch({ selection: { anchor: line.to }, scrollIntoView: true });
  editor.focus();
}

function theoremAt(lineNumber) {
  if (!analysis) return null;
  return analysis.theorems.find((t) => lineNumber >= t.line && lineNumber <= t.end_line) || null;
}

function goalsAt(theorem, lineNumber) {
  let goals = theorem.initial;
  let stepIndex = -1;
  theorem.steps.forEach((step, index) => {
    if (step.line <= lineNumber) {
      goals = step.after;
      stepIndex = index;
    }
  });
  return { goals, stepIndex };
}

function renderCursorPanels() {
  if (!analysis || analysisSource !== editor.state.doc.toString()) {
    goalMetaEl.textContent = checking ? "(checking…)" : "(edited; checking…)";
    return;
  }
  const lineNumber = currentLine();
  const theorem = theoremAt(lineNumber);
  goalsEl.replaceChildren();
  explanationEl.replaceChildren();
  if (!theorem) {
    goalMetaEl.textContent = "";
    goalsEl.appendChild(empty("Place the cursor inside a proof."));
    explanationEl.appendChild(empty("Place the cursor inside a theorem."));
    updateMarks();
    return;
  }
  const { goals, stepIndex } = goalsAt(theorem, lineNumber);
  goalMetaEl.textContent = `${theorem.name} · ${goals.length} open`;
  if (goals.length === 0) {
    const done = document.createElement("div");
    done.className = "goal done";
    done.textContent = "No goals remain.";
    goalsEl.appendChild(done);
  }
  goals.forEach((goal, index) => {
    const div = document.createElement("div");
    div.className = "goal mono";
    for (const v of goal.vars) {
      const line = document.createElement("div");
      line.className = "hyp";
      line.textContent = v;
      div.appendChild(line);
    }
    for (const [name, formula] of goal.hyps) {
      const line = document.createElement("div");
      line.className = "hyp";
      const b = document.createElement("b");
      b.textContent = name;
      line.append(b, ` : ${formula}`);
      div.appendChild(line);
    }
    const target = document.createElement("div");
    target.className = "target";
    target.textContent = (goals.length > 1 ? `[${index + 1}] ` : "") + "⊢ " + goal.target;
    div.appendChild(target);
    goalsEl.appendChild(div);
  });
  if (theorem.steps.length === 0) {
    explanationEl.appendChild(empty("This proof has no tactics yet."));
  }
  theorem.steps.forEach((step, index) => {
    const div = document.createElement("div");
    div.className = "step" + (index === stepIndex ? " current" : "");
    const code = document.createElement("code");
    code.textContent = step.text;
    const why = document.createElement("span");
    why.className = "why";
    why.textContent = step.explanation;
    div.append(code, why);
    div.addEventListener("click", () => jumpToLine(step.line));
    explanationEl.appendChild(div);
  });
  updateMarks(stepIndex >= 0 ? theorem.steps[stepIndex].line : null);
}

function updateMarks(currentStepLine = null) {
  const marks = [];
  if (analysis) {
    for (const diag of analysis.diagnostics) {
      if (diag.severity === "error" && diag.line > 0) marks.push({ line: diag.line, kind: "error" });
    }
  }
  if (currentStepLine) marks.push({ line: currentStepLine, kind: "step" });
  editor.dispatch({ effects: setLineMarks.of(marks) });
}

// ---------------------------------------------------------------------
// Hints
// ---------------------------------------------------------------------

async function runHints() {
  const source = editor.state.doc.toString();
  const line = currentLine();
  hintsEl.replaceChildren(empty("Trying tactics…"));
  hintButton.disabled = true;
  try {
    const hints = await request("hints", { source, options: options(), line });
    hintsEl.replaceChildren();
    if (!Array.isArray(hints) || hints.length === 0) {
      hintsEl.appendChild(empty("No suggestion applies to the goal on this line. Try describing the next step yourself, or look at the tactic reference below."));
      return;
    }
    for (const hint of hints) {
      const div = document.createElement("div");
      div.className = "hint" + (hint.closes_goal ? " closes" : "");
      const code = document.createElement("code");
      code.textContent = hint.tactic.split("\n")[0] + (hint.tactic.includes("\n") ? " …" : "");
      const why = document.createElement("span");
      why.className = "why";
      why.textContent = hint.description + (hint.closes_goal ? " (closes the goal)" : "");
      div.append(code, why);
      div.addEventListener("click", () => insertAfterLine(line, hint.tactic));
      hintsEl.appendChild(div);
    }
  } catch (error) {
    hintsEl.replaceChildren(empty(`Could not compute hints: ${error.message}`));
  } finally {
    hintButton.disabled = false;
  }
}

// ---------------------------------------------------------------------
// Library
// ---------------------------------------------------------------------

function renderLibrary() {
  libraryEl.replaceChildren();
  if (!analysis) return;
  const query = librarySearchEl.value.trim().toLowerCase();
  const scope = libraryScopeEl.value;
  const entries = analysis.library.filter((entry) => {
    if (scope === "imported" && !entry.is_imported) return false;
    if (scope === "local" && entry.is_imported) return false;
    if (!query) return true;
    return entry.name.toLowerCase().includes(query) || entry.statement.toLowerCase().includes(query);
  });
  if (entries.length === 0) {
    libraryEl.appendChild(empty("No theorems match."));
    return;
  }
  for (const entry of entries.slice(0, 200)) {
    const div = document.createElement("div");
    div.className = "lib-item";
    const name = document.createElement("span");
    name.className = "name mono";
    name.textContent = entry.name;
    const badge = document.createElement("span");
    badge.className = "badge " + (entry.status === "accepted" ? "ok" : entry.status);
    badge.textContent = entry.is_imported ? `imported · ${entry.status}` : entry.status;
    const stmt = document.createElement("span");
    stmt.className = "stmt mono";
    stmt.textContent = entry.statement;
    div.append(name, badge, stmt);
    div.title = "Click to insert the name at the cursor";
    div.addEventListener("click", () => {
      const pos = editor.state.selection.main.head;
      editor.dispatch({ changes: { from: pos, insert: entry.name }, selection: { anchor: pos + entry.name.length } });
      editor.focus();
    });
    libraryEl.appendChild(div);
  }
}

// ---------------------------------------------------------------------
// Wiring
// ---------------------------------------------------------------------

function empty(text) {
  const p = document.createElement("p");
  p.className = "empty";
  p.textContent = text;
  return p;
}

for (const [index, example] of EXAMPLES.entries()) {
  const option = document.createElement("option");
  option.value = String(index);
  option.textContent = example.name;
  exampleSelect.appendChild(option);
}

exampleSelect.addEventListener("change", () => {
  const index = Number(exampleSelect.value);
  if (Number.isInteger(index) && EXAMPLES[index]) {
    setSource(EXAMPLES[index].source);
  }
  exampleSelect.value = "";
});

try {
  const savedTier = localStorage.getItem(STORAGE_TIER);
  if (savedTier) tierSelect.value = savedTier;
} catch (_) {
  /* storage unavailable */
}

tierSelect.addEventListener("change", () => {
  try {
    localStorage.setItem(STORAGE_TIER, tierSelect.value);
  } catch (_) {
    /* storage unavailable */
  }
  runAnalysis();
});

checkButton.addEventListener("click", runAnalysis);
hintButton.addEventListener("click", runHints);
librarySearchEl.addEventListener("input", renderLibrary);
libraryScopeEl.addEventListener("change", renderLibrary);

downloadButton.addEventListener("click", () => {
  const blob = new Blob([editor.state.doc.toString()], { type: "text/plain" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "proof.ctea";
  a.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
});

request("ping", {})
  .then(() => runAnalysis())
  .catch((error) => {
    statusEl.textContent = `Checker error: ${error.message}`;
    statusEl.className = "status error";
  });
