import { encodeProjectRequest } from './project-request.mjs';
const wasmPaths = ["./pkg/cetacea_wasm.wasm", "../target/wasm32-unknown-unknown/release/cetacea_wasm.wasm"];
const encoder = new TextEncoder();
const decoder = new TextDecoder();
let wasm;
let loading;
async function initialize() {
  let lastError;
  for (const path of wasmPaths) {
    try {
      const response = await fetch(path);
      if (!response.ok) throw new Error(`${response.status} ${response.statusText}`);
      const instance = await WebAssembly.instantiate(await response.arrayBuffer(), {});
      wasm = instance.instance.exports;
      return true;
    } catch (error) { lastError = error; }
  }
  const error = new Error(`Could not load the checker: ${lastError?.message}. This build may be unavailable. Download your source or project before reloading the page.`);
  error.name = 'CheckerLoadError';
  throw error;
}
self.onmessage = async ({ data }) => {
  try {
    loading ??= initialize();
    await loading;
    const methods = { source: callSource, goals: callGoalsAt, tactic: callRunTactic, explain: callExplainTheorem, project: callProject };
    if (!Object.hasOwn(methods, data.method)) throw new Error('Unknown checker operation');
    const result = methods[data.method](...data.args);
    self.postMessage({ id: data.id, result });
  } catch (error) {
    self.postMessage({ id: data.id, error: error.name === 'CheckerLoadError' ? error.message : `Checker error: ${error.message}. Your source is preserved; press Check to retry.` });
  }
};

function callProject(project, operation, options) {
  const bytes = encodeProjectRequest(project, operation, options);
  const ptr = wasm.cetacea_alloc(bytes.length);
  let result;
  try {
    new Uint8Array(wasm.memory.buffer, ptr, bytes.length).set(bytes);
    result = readResponse(wasm.cetacea_project(ptr, bytes.length));
  } finally {
    wasm.cetacea_free(ptr, bytes.length);
  }
  if (result.error) throw new Error(result.error);
  return result;
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
