import { tacticInsertion } from './proof-editing.mjs';
import { readAssignmentArchive } from './assignment-files.mjs?v=2';
import { libraryEntries } from "./theorem-library.mjs";
import { CheckerClient } from "./checker-client.mjs?v=2";
import { StudentWork, readProofFile, WORK_KEY } from "./student-work.mjs?v=2";
import { ProjectFiles, readProjectArchive, serializeProjectArchive } from "./project-files.mjs";
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

const work = new StudentWork(() => window.localStorage, sampleSource, {
  withLock: callback => {
    if (!navigator.locks) throw new Error('Safe storage locking is unavailable');
    return navigator.locks.request('cetacea.web.autosave', callback);
  },
  onStatus: () => renderSaveStatus(),
});


const editor = document.querySelector("#sourceEditor");
// Keep skip navigation inside this editor even when an embedding page sets a
// base URL. Default fragment navigation would otherwise load that base page.
for (const link of document.querySelectorAll('.skip-links a[href^="#"]')) {
  link.addEventListener('click', event => {
    const target = document.getElementById(link.getAttribute('href').slice(1));
    if (!target) return;
    event.preventDefault();
    target.focus();
    target.scrollIntoView({block: 'nearest'});
  });
}
const sourceHighlights = document.querySelector("#sourceHighlights");
const checkButton = document.querySelector("#checkButton");
const resetButton = document.querySelector("#resetButton");
const exampleSelect = document.querySelector("#exampleSelect");
const resetSampleButton = document.querySelector("#resetSampleButton");
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
const saveStatus = document.querySelector("#saveStatus");
const recoverySelect = document.querySelector("#recoverySelect");
const fileInput = document.querySelector("#proofFile");
const fileNameInput = document.querySelector("#fileName");
const projectSelect = document.querySelector("#projectSelect");
const projectInput = document.querySelector("#projectInput");
let currentProject = work.state.project
  ? new ProjectFiles(work.state.project, {allowOversizedSources: true}) : null;

let currentAssignment = work.state.assignment ?? null;
const assignmentStatus = document.querySelector('#assignmentStatus');
const assignmentViolations = document.querySelector('#assignmentViolations');
let assignmentLoadSequence = 0;
let checkingEnabled = true;
let revision = 0;
const requestVersions = new Map();
const cancelButton = document.querySelector("#cancelButton");
const checker = new CheckerClient({ onBusy: busy => { cancelButton.disabled = !busy; } });
cancelButton.addEventListener("click", () => {
  revision += 1;
  checker.stop();
  clearTimeout(editDebounceTimer);
  clearTimeout(cursorSyncTimer);
  checkingEnabled = false;
  saveSource();
  statusEl.textContent = "Checking cancelled. Your source is preserved; press Check to resume.";
  statusEl.classList.remove("error");
});
let stepIndex = -1;
let activeGoalResult = null;
let cursorSyncTimer = 0;
let editDebounceTimer = 0;
let theoremLibraryItems = [];
let lastEditorSelection = { start: 0, end: 0 };
let diagnosticLineMarks = new Map();
let lastCheckResult = null;

editor.value = work.state.source;
fileNameInput.value = work.state.name;
renderSaveStatus();
renderRecovery();
renderProject();
renderAssignment();
if (currentAssignment) assignmentStatus.closest('details').open = true;
rememberEditorSelection();
renderSourceHighlights();
populateExampleSelect();
setControls(false);
loadWasm();

document.querySelector("#openFileButton").addEventListener("click", () => fileInput.click());
fileInput.addEventListener("change", async () => {
  const file = fileInput.files[0];
  fileInput.value = "";
  if (!file) return;
  const version = revision;
  try {
    const loaded = await readProofFile(file);
    if (version !== revision) throw new Error('The source changed while the file was opening. Open the file again when ready.');
    setEditorSource(loaded.source, loaded.name);
    exampleSelect.value = "";
  } catch (error) {
    saveStatus.textContent = `${error.message} Current work is unchanged. ${work.error}`.trim();
    saveStatus.classList.add("error");
  }
});
document.querySelector("#downloadButton").addEventListener("click", () => {
  saveSource();
  const url = URL.createObjectURL(new Blob([editor.value], {type: "text/plain;charset=utf-8"}));
  const link = document.createElement("a");
  link.href = url;
  link.download = work.state.name;
  document.body.append(link);
  link.click();
  link.remove();
  window.setTimeout(() => URL.revokeObjectURL(url), 1000);
});
fileNameInput.addEventListener("change", saveSource);
document.querySelector('#downloadSavedDataButton').addEventListener('click', () => {
  if (work.recoveryData === null) return;
  const archive = JSON.stringify({format: 'cetacea-saved-data', version: 1, raw: work.recoveryData});
  const url = URL.createObjectURL(new Blob([archive], {type: 'application/json'}));
  const link = document.createElement('a');
  link.href = url;
  link.download = 'cetacea-saved-data.json';
  document.body.append(link);
  link.click();
  link.remove();
  window.setTimeout(() => URL.revokeObjectURL(url), 1000);
});
document.querySelector('#resumeAutosaveButton').addEventListener('click', async () => {
  await saveSource();
  await work.resumeAutosave();
  renderSaveStatus();
});
window.addEventListener("beforeunload", event => {
  if (work.error || work.saving) {
    event.preventDefault();
    event.returnValue = "";
  }
});
window.addEventListener('storage', event => {
  if (event.key === WORK_KEY || event.key === null) work.observeStorageChange();
});
document.querySelector("#checkpointButton").addEventListener("click", () => {
  work.checkpoint(editor.value, fileNameInput.value, projectSnapshot(), currentAssignment);
  renderSaveStatus();
  renderRecovery();
});
document.querySelector("#restoreWorkButton").addEventListener("click", () => {
  if (recoverySelect.value === "") return;
  const entry = work.state.history[Number(recoverySelect.value)];
  if (entry) setEditorSource(entry.source, entry.name, entry.project, entry.assignment ?? null);
});

document.querySelector('#openProjectButton').addEventListener('click', () => projectInput.click());
projectInput.addEventListener('change', async () => {
  const file = projectInput.files[0];
  projectInput.value = '';
  if (!file) return;
  const version = revision;
  try {
    const project = await readProjectArchive(file);
    if (version !== revision) throw new Error('Work changed while opening the archive. Open it again when ready.');
    const next = new ProjectFiles(project);
    setEditorSource(next.source, project.root, project);
    exampleSelect.value = '';
  } catch (error) { projectError(error); }
});
projectSelect.addEventListener('change', () => {
  try {
    const next = new ProjectFiles(projectSnapshot(), {allowOversizedSources: true});
    next.select(projectSelect.value);
    setEditorSource(next.source, next.project.root, next.snapshot());
  } catch (error) { renderProject(); projectError(error); }
});
for (const [id, operation] of [['addProjectFileButton', 'add'], ['renameProjectFileButton', 'rename']]) {
  document.querySelector(`#${id}`).addEventListener('click', () => {
    try {
      const next = new ProjectFiles(projectSnapshot() ?? {
        root: work.state.name, files: [{path: work.state.name, source: editor.value}]
      }, {allowOversizedSources: true});
      next[operation](document.querySelector('#projectPath').value);
      setEditorSource(next.source, next.project.root, next.snapshot());
    } catch (error) { projectError(error); }
  });
}
document.querySelector('#downloadProjectButton').addEventListener('click', () => {
  try {
    saveSource();
    const project = projectSnapshot() ?? {root: work.state.name, files: [{path: work.state.name, source: editor.value}]};
    const url = URL.createObjectURL(new Blob([serializeProjectArchive(project)], {type: 'application/json'}));
    const link = document.createElement('a');
    link.href = url;
    link.download = 'homework.ctea-project';
    document.body.append(link);
    link.click();
    link.remove();
    window.setTimeout(() => URL.revokeObjectURL(url), 1000);
  } catch (error) { projectError(error); }
});

document.querySelector('#openAssignmentButton').addEventListener('click', () => document.querySelector('#assignmentInput').click());
document.querySelector('#assignmentInput').addEventListener('change', async event => {
  const file = event.target.files[0];
  event.target.value = '';
  if (!file) return;
  assignmentStatus.closest('details').open = true;
  const version = revision;
  const sequence = ++assignmentLoadSequence;
  const validator = new CheckerClient();
  try {
    const assignment = await readAssignmentArchive(file);
    const project = projectSnapshot() ?? {root: work.state.name, files: [{path: work.state.name, source: editor.value}]};
    // Rust validates the manifest and the entire pinned dependency set before selection.
    await validator.run('project', [project, 'check', {assignment}]);
    if (sequence !== assignmentLoadSequence) return;
    if (version !== revision) throw new Error('Work changed while opening the assignment. Open it again when ready.');
    work.checkpoint(editor.value, fileNameInput.value, projectSnapshot(), currentAssignment);
    renderRecovery();
    currentAssignment = {...assignment, archiveName: file.name};
    document.querySelector('#clearAssignmentButton').disabled = false;
    editor.dispatchEvent(new Event('input'));
  } catch (error) {
    if (sequence === assignmentLoadSequence) {
      assignmentStatus.textContent = `${error.message} Assignment selection is unchanged.`;
      assignmentStatus.classList.add('error');
    }
  } finally { validator.stop(); }
});
document.querySelector('#clearAssignmentButton').addEventListener('click', event => {
  const hadFocus = document.activeElement === event.currentTarget;
  assignmentLoadSequence += 1;
  work.checkpoint(editor.value, fileNameInput.value, projectSnapshot(), currentAssignment);
  renderRecovery();
  currentAssignment = null;
  document.querySelector('#clearAssignmentButton').disabled = true;
  if (hadFocus) document.querySelector('#openAssignmentButton').focus();
  editor.dispatchEvent(new Event('input'));
});
function renderAssignment(result = null) {
  document.querySelector('#clearAssignmentButton').disabled = !currentAssignment;
  assignmentStatus.classList.remove('error');
  assignmentViolations.replaceChildren();
  if (!currentAssignment) { assignmentStatus.textContent = 'No assignment selected.'; return; }
  assignmentStatus.textContent = `${currentAssignment.archiveName} (${currentAssignment.path}): ${result ? (result.accepted ? 'Assignment satisfied.' : 'Assignment not satisfied.') : 'Awaiting check.'}`;
  assignmentStatus.classList.toggle('error', Boolean(result && !result.accepted));
  for (const violation of result?.violations ?? []) {
    const item = document.createElement('li');
    item.textContent = `${violation.declaration}: ${violation.message}`;
    assignmentViolations.append(item);
  }
}

function projectError(error) {
  saveStatus.textContent = `${error.message} Current work is unchanged. ${work.error}`.trim();
  saveStatus.classList.add('error');
}
function projectSnapshot() {
  if (!currentProject) return null;
  currentProject.edit(editor.value);
  return currentProject.snapshot();
}
function renderProject() {
  projectSelect.replaceChildren();
  for (const file of currentProject?.project.files ?? []) {
    projectSelect.append(new Option(file.path, file.path));
  }
  if (currentProject) projectSelect.value = currentProject.project.root;
  projectSelect.disabled = !currentProject;
  fileNameInput.readOnly = Boolean(currentProject);
}

checkButton.addEventListener("click", async () => {
  checkingEnabled = true;
  statusEl.textContent = "Checking…";
  const version = revision;
  await refreshOutline();
  if (version !== revision || !checkingEnabled) return;
  renderCheck(await callSource("cetacea_check", editor.value));
  if (version !== revision || !checkingEnabled) return;
});

resetButton.addEventListener("click", async () => {
  if (!checkingEnabled) return;
  const selected = theoremSelect.value;
  if (!selected) return;
  const theorem = currentOutline().find((item) => item.name === selected);
  const line = theorem ? theorem.line : 1;
  stepIndex = -1;
  renderGoals(await callGoalsAt(editor.value, line, 1));
});

stepButton.addEventListener("click", async () => {
  if (!checkingEnabled) return;
  const theorem = theoremSelect.value;
  if (!theorem) return;
  const result = await callRunTactic(editor.value, theorem, stepIndex + 1);
  if (!result) return;
  stepIndex = result.next_tactic_index - 1;
  renderGoals(result);
});

theoremSelect.addEventListener("change", async () => {
  stepIndex = -1;
  const theorem = currentOutline().find((item) => item.name === theoremSelect.value);
  if (theorem && checkingEnabled) {
    renderGoals(await callGoalsAt(editor.value, theorem.line, 1));
    renderExplanationForSelected();
  }
});

librarySearchEl.addEventListener("input", renderTheoremLibrary);
libraryScopeEl.addEventListener("change", renderTheoremLibrary);

exampleSelect.addEventListener("change", () => {
  const example = (window.CETACEA_EXAMPLES ?? []).find(
    (item) => item.id === exampleSelect.value,
  );
  if (!example) return;
  setEditorSource(example.source, `${example.id}.ctea`);
  statusEl.textContent = `Loaded example: ${example.label}`;
  statusEl.classList.remove("error");
});

resetSampleButton.addEventListener("click", () => {
  exampleSelect.value = "";
  setEditorSource(sampleSource);
  statusEl.textContent = "Restored the sample source";
  statusEl.classList.remove("error");
});

editor.addEventListener("input", () => {
  revision += 1;
  checker.stop();
  checkingEnabled = true;
  saveSource();
  clearCheckDisplay();
  rememberEditorSelection();
  scheduleEditDebounce();
  if (!checkingEnabled) return;
  stepIndex = -1;
  activeGoalResult = null;
  refreshOutline().then(() => renderExplanationForSelected());
  renderTactics(null);
  renderExplanation(null);
  renderSourceHighlights(null);
  renderTheoremLibrary();
  scheduleCursorSync();
});
editor.addEventListener("click", () => {
  rememberEditorSelection();
  scheduleCursorSync({ announce: true });
});
editor.addEventListener("keyup", (event) => {
  rememberEditorSelection();
  const navigationKeys = [
    "ArrowUp",
    "ArrowDown",
    "ArrowLeft",
    "ArrowRight",
    "Home",
    "End",
    "PageUp",
    "PageDown",
  ];
  scheduleCursorSync({ announce: navigationKeys.includes(event.key) });
});
editor.addEventListener("select", () => {
  rememberEditorSelection();
  scheduleCursorSync();
});
editor.addEventListener("scroll", syncHighlightScroll);

async function loadWasm() {
  setControls(true);
  const version = revision;
  await refreshOutline();
  if (version !== revision || !checkingEnabled) return;
  renderCheck(await callSource("cetacea_check", editor.value));
  if (version !== revision || !checkingEnabled) return;
  const first = currentOutline()[0];
  if (first && checkingEnabled) renderGoals(await callGoalsAt(editor.value, first.line, 1));
}

function setControls(enabled) {
  for (const button of [checkButton, resetButton, stepButton]) {
    button.disabled = !enabled;
  }
  theoremSelect.disabled = !enabled;
}

function renderSaveStatus() {
  saveStatus.textContent = work.error || (work.saving ? "Saving work…" : "Autosave ready on this browser. Download a copy to keep or submit.");
  saveStatus.classList.toggle("error", Boolean(work.error));
  document.querySelector('#downloadSavedDataButton').hidden = work.recoveryData === null;
  document.querySelector('#resumeAutosaveButton').hidden = !work.readOnly || work.conflict || work.recoveryData === null;
}

function saveSource() {
  const saving = work.save(editor.value, fileNameInput.value, projectSnapshot(), currentAssignment);
  fileNameInput.value = work.state.name;
  renderSaveStatus();
  return saving;
}

function renderRecovery() {
  recoverySelect.replaceChildren(new Option("Choose a checkpoint…", ""));
  for (const [index, entry] of work.state.history.entries()) {
    recoverySelect.append(new Option(`${entry.name} — ${new Date(entry.savedAt).toLocaleString()}`, String(index)));
  }
  document.querySelector("#restoreWorkButton").disabled = work.state.history.length === 0;
}

function clearCheckDisplay() {
  lastCheckResult = null;
  renderAssignment();
  theoremLibraryItems = [];
  diagnosticLineMarks = new Map();
  acceptedEl.replaceChildren(empty("Checking current source…"));
  renderDiagnostics([]);
  renderTheoremLibrary();
  statusEl.textContent = "Checking…";
  statusEl.classList.remove("error");
}

function scheduleEditDebounce() {
  window.clearTimeout(editDebounceTimer);
  editDebounceTimer = window.setTimeout(async () => {
    saveSource();
    if (checkingEnabled) renderCheck(await callSource("cetacea_check", editor.value));
  }, 500);
}

function populateExampleSelect() {
  for (const example of window.CETACEA_EXAMPLES ?? []) {
    const option = document.createElement("option");
    option.value = example.id;
    option.textContent = example.label;
    exampleSelect.append(option);
  }
}

async function setEditorSource(source, name = "proof.ctea", project = null, assignment = currentAssignment) {
  const nextProject = project ? new ProjectFiles(project, {allowOversizedSources: true}) : null;
  work.checkpoint(editor.value, fileNameInput.value, projectSnapshot(), currentAssignment);
  renderRecovery();
  revision += 1;
  checker.stop();
  checkingEnabled = true;
  window.clearTimeout(editDebounceTimer);
  editor.value = source;
  currentProject = nextProject;
  currentAssignment = assignment;
  fileNameInput.value = name;
  renderProject();
  editor.setSelectionRange(0, 0);
  rememberEditorSelection();
  saveSource();
  clearCheckDisplay();
  stepIndex = -1;
  activeGoalResult = null;
  diagnosticLineMarks = new Map();
  if (!checkingEnabled) {
    renderSourceHighlights(null);
    return;
  }
  const version = revision;
  await refreshOutline();
  if (version !== revision || !checkingEnabled) return;
  renderCheck(await callSource("cetacea_check", editor.value));
  if (version !== revision || !checkingEnabled) return;
  renderTactics(null);
  renderExplanationForSelected();
  renderSourceHighlights(null);
  const first = currentOutline()[0];
  if (first) {
    renderGoals(await callGoalsAt(editor.value, first.line, 1));
  } else {
    goalMetaEl.textContent = "";
    goalsEl.replaceChildren(empty("No goals"));
  }
}

async function refreshOutline() {
  const result = await callSource("cetacea_outline", editor.value);
  if (!result) return;
  const previous = theoremSelect.value;
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

async function requestCheck(method, args, channel) {
  if (!checkingEnabled) return null;
  const source = editor.value;
  const version = revision;
  const sequence = (requestVersions.get(channel) ?? 0) + 1;
  requestVersions.set(channel, sequence);
  try {
    if (currentProject || currentAssignment) {
      const project = currentProject?.snapshot() ?? {root: work.state.name, files: [{path: work.state.name, source: editor.value}]};
      const analysisSource = method === 'source' ? args[1] : args[0];
      project.files.find(file => file.path === project.root).source = analysisSource;
      const operation = method === 'source' ? (args[0] === 'cetacea_outline' ? 'outline' : 'check') : method;
      const options = method === 'goals' ? {line: args[1], column: args[2]}
        : {theorem: method === 'source' ? '' : args[1], tacticIndex: args[2] ?? 0};
      if (currentAssignment) options.assignment = currentAssignment;
      method = 'project';
      args = [project, operation, options];
    }
    const result = await checker.run(method, args, channel);
    if (version !== revision || source !== editor.value || requestVersions.get(channel) !== sequence) return null;
    return result;
  } catch (error) {
    if (version === revision) {
      checkingEnabled = false;
      statusEl.textContent = error.message;
      statusEl.classList.add("error");
    }
    return null;
  }
}
function callSource(exportName, source) { return requestCheck("source", [exportName, source], exportName); }
function callGoalsAt(source, line, column) { return requestCheck("goals", [source, line, column], "goals"); }
function callRunTactic(source, theorem, index) { return requestCheck("tactic", [source, theorem, index], "goals"); }
function callExplainTheorem(source, theorem) { return requestCheck("explain", [source, theorem], "explain"); }

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

async function syncCursorGoals(options = {}) {
  if (!checkingEnabled) return;
  window.clearTimeout(cursorSyncTimer);
  if (document.activeElement === editor) rememberEditorSelection();
  const position = cursorPositionFromOffset(editor.value, currentEditorOffset());
  const result = await callGoalsAt(editor.value, position.line, position.column);
  if (!result) return;
  stepIndex = result.next_tactic_index - 1;
  renderGoals(result, { position, announce: options.announce });
}

function scheduleCursorSync(options = {}) {
  if (!checkingEnabled) return;
  window.clearTimeout(cursorSyncTimer);
  cursorSyncTimer = window.setTimeout(() => syncCursorGoals(options), 120);
}

function renderCheck(result) {
  if (!result) return;
  lastCheckResult = result;
  renderAssignment(result.assignment);
  renderDiagnostics(result.diagnostics ?? []);
  const packages = result.imported_packages ?? [];
  if (result.hol_certified) {
    statusEl.textContent = packages.length
      ? `HOL certified · ${packages.join(", ")}`
      : "HOL certified";
    statusEl.classList.remove("error");
  } else if (!result.ok) {
    statusEl.textContent = "Check failed";
    statusEl.classList.add("error");
  }
  const theorems = result.theorems ?? [];
  theoremLibraryItems = [...theorems, ...(result.package_theorems ?? [])];
  renderTheoremLibrary();
  acceptedEl.replaceChildren();
  if (theorems.length === 0) {
    acceptedEl.append(empty("No accepted declarations"));
  } else {
    for (const theorem of theorems.filter((item) => !item.is_imported)) {
      const item = document.createElement("div");
      item.className = "accepted-item";
      const head = document.createElement("div");
      head.textContent = `${theorem.is_axiom ? "axiom" : "theorem"} ${theorem.name} (${theoremDisplayLabel(theorem)})`;
      if (theoremUsesSorry(theorem)) {
        const incomplete = document.createElement("span");
        incomplete.className = "incomplete-flag";
        incomplete.textContent = " (incomplete)";
        incomplete.title = "This proof uses sorry and is not finished.";
        head.append(incomplete);
      }
      item.append(head);
      const axioms = theoremAxiomDeps(theorem);
      if (axioms.length) {
        const deps = document.createElement("div");
        deps.className = "accepted-axioms";
        deps.textContent = `axioms: ${axioms.join(", ")}`;
        item.append(deps);
      }
      acceptedEl.append(item);
    }
  }
  for (const outcome of result.theorem_outcomes ?? []) {
    if (outcome.is_imported || ["accepted", "incomplete", "trusted_axiom"].includes(outcome.status)) continue;
    const item = document.createElement("div");
    item.className = "accepted-item";
    const label = outcome.status.replaceAll("_", " ");
    item.textContent = `${label}: ${outcome.name} (line ${outcome.line})`;
    acceptedEl.append(item);
  }
  renderExplanationForSelected();
}

async function renderExplanationForSelected() {
  if (!checkingEnabled || !theoremSelect.value) {
    renderExplanation(null);
    return;
  }
  const selected = theoremSelect.value;
  const result = await callExplainTheorem(editor.value, selected);
  if (result && selected === theoremSelect.value) renderExplanation(result);
}

function renderGoals(result, options = {}) {
  if (!result) return;
  const diagnostics = (result.diagnostics ?? []).filter(d =>
    result.theorem || d.message !== "no theorem contains the requested position");
  activeGoalResult = result;
  if (result.theorem) {
    theoremSelect.value = result.theorem;
    if (proofExplanationEl.dataset.theorem !== result.theorem) {
      proofExplanationEl.replaceChildren(empty("Loading explanation…"));
      renderExplanationForSelected();
    }
  }
  renderDiagnostics(diagnostics);
  renderTactics(result);
  renderSourceHighlights(result);
  goalsEl.replaceChildren();
  const fragment = result.statement_fragment ? ` · ${result.statement_fragment}` : "";
  if (result.theorem) {
    goalMetaEl.textContent = `${result.theorem} - ${result.next_tactic_index}/${result.tactic_count}${fragment}`;
  } else if (options.position) {
    goalMetaEl.textContent = `Cursor line ${options.position.line}, column ${options.position.column}`;
  } else {
    goalMetaEl.textContent = "";
  }
  const hasErrors = diagnostics.some(d => d.severity === "error");
  if (options.announce) {
    const cursorText = options.position
      ? `line ${options.position.line}, column ${options.position.column}`
      : "the selected cursor position";
    const goalCount = (result.goals ?? []).length;
    if (hasErrors) {
      statusEl.textContent = "Proof failed; see diagnostics.";
    } else if (result.theorem && result.completed) {
      statusEl.textContent = `${result.theorem}: proof complete at ${cursorText}${certificationSuffix()}`;
    } else if (result.theorem) {
      statusEl.textContent = `${result.theorem}: ${goalCount} goal${goalCount === 1 ? "" : "s"} at ${cursorText}${certificationSuffix()}`;
    } else {
      statusEl.textContent = `No theorem at ${cursorText}`;
    }
    statusEl.classList.toggle("error", hasErrors);
  }
  stepButton.disabled =
    !checkingEnabled ||
    !result.theorem ||
    result.completed ||
    result.next_tactic_index >= result.tactic_count;

  if ((result.goals ?? []).length === 0) {
    goalsEl.append(empty(hasErrors ? "Proof failed; see diagnostics" : !result.theorem
      ? "Move the cursor into a theorem to see its goals"
      : result.completed ? "Complete" : "No goals"));
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
    if (goal.computed_target) {
      const computation = document.createElement("div");
      computation.className = "goal-computation";
      computation.append(pre(`Computes to: ${goal.computed_target}`));
      computation.title = "After transparent definitions and built-in computation. The written goal remains above.";
      target.append(computation);
    }
    item.append(context, target, renderGoalHints(goal.hints ?? []));
    goalsEl.append(item);
  }
  renderTheoremLibrary();
}

function certificationSuffix() {
  return lastCheckResult?.hol_certified ? " · HOL certified" : "";
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
  proofExplanationEl.dataset.theorem = result?.theorem ?? "";
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
  const fragment = result.statement_fragment ? ` · ${result.statement_fragment}` : "";
  const hasErrors = (result.diagnostics ?? []).some(d => d.severity === "error");
  meta.textContent = hasErrors ? `${result.theorem} (failed)${fragment}` : result.completed
    ? `${result.theorem} (${result.mode})${fragment}`
    : `${result.theorem} (incomplete)${fragment}`;
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
    if (step.before.computed_target) before.textContent += `\nComputes to: ${step.before.computed_target}`;

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
      ? `After:\n${afterGoals.map((goal, idx) => `${idx + 1}. |- ${goal.target}${goal.computed_target ? `\n   Computes to: ${goal.computed_target}` : ""}`).join("\n")}`
      : "After: current goal closed";

    item.append(head, before, body, after);
    proofExplanationEl.append(item);
  }

  if (result.diagnostics?.length) {
    const note = document.createElement("div");
    note.className = "explain-warning";
    note.textContent = hasErrors
      ? "This proof was not accepted. See diagnostics for the reason."
      : "See diagnostics for notes about this proof.";
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
    if (diagnosticLineMarks.has(lineNumber)) {
      element.classList.add("is-error");
      const span = clampSpan(diagnosticLineMarks.get(lineNumber), line);
      if (span && line) {
        element.append(
          document.createTextNode(line.slice(0, span.start)),
          errorToken(line.slice(span.start, span.end) || " "),
          document.createTextNode(line.slice(span.end)),
        );
      } else {
        element.textContent = line || " ";
      }
    } else {
      element.textContent = line || " ";
    }
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

function errorToken(text) {
  const element = document.createElement("span");
  element.className = "error-token";
  element.textContent = text;
  return element;
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
  updateDiagnosticLineMarks(diagnostics);
  diagnosticsEl.replaceChildren();
  if (!diagnostics.length) {
    diagnosticsEl.append(empty("No diagnostics"));
    return;
  }
  const editorLines = editor.value.split("\n");
  for (const diagnostic of diagnostics) {
    const item = document.createElement("div");
    item.className = "diagnostic";
    const title = document.createElement("div");
    title.className = "diagnostic-title";
    const location = diagnostic.location ? `${diagnostic.location.path ? diagnostic.location.path + ": " : ""}line ${diagnostic.location.line}: ` : "";
    title.textContent = `${location}${diagnostic.message}`;
    item.append(title);
    if (diagnosticInEditor(diagnostic)) {
      const jump = document.createElement('button');
      jump.type = 'button';
      jump.className = 'diagnostic-jump';
      jump.textContent = `Go to line ${diagnostic.location.line}`;
      jump.addEventListener('click', () => moveCursorToLineEnd(diagnostic.location.line));
      item.append(jump);
    }
    const marker = diagnosticSourceMarker(diagnostic, editorLines);
    if (marker) item.append(marker);
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

function diagnosticInEditor(diagnostic) {
  const line = diagnostic.location?.line;
  const path = diagnostic.location?.path;
  const root = currentProject?.project.root ?? (currentAssignment ? work.state.name : null);
  return Number.isInteger(line) && line > 0 && line <= editor.value.split('\n').length
    && (!path || path === root);
}

function updateDiagnosticLineMarks(diagnostics) {
  diagnosticLineMarks = new Map();
  for (const diagnostic of diagnostics) {
    if (!diagnosticInEditor(diagnostic)) continue;
    const line = diagnostic.location.line;
    // Keep the first span reported for a line so the caret stays stable.
    if (!diagnosticLineMarks.has(line) || !diagnosticLineMarks.get(line)) {
      diagnosticLineMarks.set(line, diagnostic.span ?? null);
    }
  }
  renderSourceHighlights();
}

function diagnosticSourceMarker(diagnostic, editorLines) {
  if (!diagnosticInEditor(diagnostic)) return null;
  const lineText = editorLines[diagnostic.location.line - 1];
  if (lineText === undefined) return null;
  const marker = document.createElement("pre");
  marker.className = "diagnostic-source";
  const codeLine = document.createElement("span");
  codeLine.textContent = lineText;
  marker.append(codeLine, document.createTextNode("\n"));
  const caretLine = document.createElement("span");
  caretLine.className = "diagnostic-caret";
  const span = clampSpan(diagnostic.span, lineText);
  if (span) {
    caretLine.textContent =
      " ".repeat(span.start) + "^" + "~".repeat(Math.max(0, span.end - span.start - 1));
  } else {
    caretLine.textContent = "^".padStart(lineText.search(/\S/) + 1 || 1);
  }
  marker.append(caretLine);
  return marker;
}

function clampSpan(span, lineText) {
  if (!span || typeof span.start !== "number" || typeof span.end !== "number") return null;
  const start = Math.max(0, Math.min(span.start, lineText.length));
  const end = Math.max(start, Math.min(span.end, lineText.length + 1));
  return { start, end };
}

function renderTheoremLibrary() {
  const focusedName = theoremLibraryEl.contains(document.activeElement)
    ? document.activeElement.textContent : null;
  const restoreFocus = () => {
    if (focusedName === null) return;
    const replacement = [...theoremLibraryEl.querySelectorAll('button')]
      .find(button => button.textContent === focusedName);
    (replacement ?? librarySearchEl).focus({preventScroll: true});
  };
  theoremLibraryEl.replaceChildren();
  const query = librarySearchEl.value.trim().toLowerCase();
  const scope = libraryScopeEl.value;
  const suggested = suggestedTheoremNames();

  const items = libraryEntries(theoremLibraryItems, query, scope, suggested);

  if (!items.length) {
    theoremLibraryEl.append(empty(theoremLibraryItems.length ? "No matching theorems" : "Run Check to load theorems"));
    restoreFocus();
    return;
  }

  for (const theorem of items.slice(0, 80)) {
    const item = document.createElement("div");
    item.className = "library-item";
    if (theorem.suggested) item.classList.add("is-suggested");

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
      badge(theoremDisplayLabel(theorem)),
      badge(theorem.is_imported ? "imported" : "local"),
    );
    if (theorem.hol_status) badges.append(badge(theorem.hol_status));
    if (theoremUsesSorry(theorem)) badges.append(badge("incomplete", "badge-warn"));
    if (theorem.suggested) badges.append(badge("suggested"));
    head.append(name, badges);

    const statement = document.createElement("pre");
    statement.className = "library-statement";
    statement.textContent = theorem.statement ?? "";
    item.append(head, statement);
    if (theorem.aliases.length > 1) {
      const aliases = document.createElement("div");
      aliases.className = "library-aliases";
      aliases.textContent = `Also available as: ${theorem.aliases.filter(alias => alias !== theorem.name).join(", ")}`;
      item.append(aliases);
    }
    theoremLibraryEl.append(item);
  }

  if (items.length > 80) {
    theoremLibraryEl.append(empty(`Showing 80 of ${items.length} matches`));
  }
  restoreFocus();
}

function suggestedTheoremNames() {
  const known = new Set(theoremLibraryItems.map((theorem) => theorem.name));
  const suggested = new Set();
  for (const goal of activeGoalResult?.goals ?? []) {
    for (const hint of goal.hints ?? []) {
      const match = /^(?:apply|exact)\s+([A-Za-z_][A-Za-z0-9_.]*)/.exec(hint.tactic);
      if (match && known.has(match[1])) suggested.add(match[1]);
    }
  }
  return suggested;
}

function badge(text, extraClass) {
  const element = document.createElement("span");
  element.className = "badge";
  if (extraClass) element.classList.add(extraClass);
  element.textContent = text;
  return element;
}

function theoremDisplayLabel(theorem) {
  return theorem.is_axiom ? "trusted" : (theorem.required_fragment ?? theorem.mode);
}

// The wasm may serialize these per-theorem fields as snake_case (Rust side)
// or camelCase; older builds omit them entirely, so treat them as optional.
function theoremUsesSorry(theorem) {
  return Boolean(theorem.uses_sorry ?? theorem.usesSorry);
}

function theoremAxiomDeps(theorem) {
  const deps = theorem.axiom_deps ?? theorem.axiomDeps;
  return Array.isArray(deps) ? deps : [];
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
  const insertion = tacticInsertion(value, start, tactic);
  editor.setRangeText(insertion.text, insertion.offset, insertion.offset, "end");
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
