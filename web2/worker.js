// The checker runs here, off the main thread, so typing never stalls.
// Messages: { id, kind: "analyze" | "hints", source, options, line }.

const WASM_CANDIDATES = [
  "./pkg/hol_wasm.wasm",
  "../target/wasm32-unknown-unknown/release/hol_wasm.wasm",
  "../target/wasm32-unknown-unknown/debug/hol_wasm.wasm",
];

const encoder = new TextEncoder();
const decoder = new TextDecoder();
let wasm = null;

async function load() {
  for (const url of WASM_CANDIDATES) {
    try {
      const response = await fetch(url);
      if (!response.ok) continue;
      const bytes = await response.arrayBuffer();
      const { instance } = await WebAssembly.instantiate(bytes, {});
      wasm = instance.exports;
      return url;
    } catch (error) {
      console.warn(`cetacea: could not load ${url}`, error);
    }
  }
  throw new Error("the checker (hol_wasm.wasm) could not be loaded");
}

function writeString(value) {
  const bytes = encoder.encode(value);
  const ptr = wasm.c2_alloc(bytes.length);
  new Uint8Array(wasm.memory.buffer, ptr, bytes.length).set(bytes);
  return { ptr, len: bytes.length };
}

function readResponse(ptr) {
  const view = new DataView(wasm.memory.buffer);
  const len = view.getUint32(ptr, true);
  const bytes = new Uint8Array(wasm.memory.buffer, ptr + 4, len).slice();
  wasm.c2_free(ptr, len + 4);
  return JSON.parse(decoder.decode(bytes));
}

function call(name, source, options, extra = []) {
  const src = writeString(source);
  const opts = writeString(JSON.stringify(options || {}));
  let ptr;
  try {
    ptr = wasm[name](src.ptr, src.len, opts.ptr, opts.len, ...extra);
  } finally {
    wasm.c2_free(src.ptr, src.len);
    wasm.c2_free(opts.ptr, opts.len);
  }
  return readResponse(ptr);
}

const ready = load();

self.onmessage = async (event) => {
  const { id, kind, source, options, line } = event.data;
  try {
    const url = await ready;
    if (kind === "ping") {
      self.postMessage({ id, result: { url } });
      return;
    }
    const result =
      kind === "hints"
        ? call("c2_hints", source, options, [line >>> 0])
        : call("c2_analyze", source, options);
    self.postMessage({ id, result });
  } catch (error) {
    self.postMessage({ id, error: String(error && error.message ? error.message : error) });
  }
};
