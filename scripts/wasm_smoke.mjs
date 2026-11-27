// Smoke test for the browser checker: loads the real hol_wasm.wasm the
// way web2/worker.js does and checks the behaviours that only exist in
// the Wasm build or that it must not get wrong: course sections, hints,
// kernel rules per step, and the resource limits (the Wasm stack is
// small, and overflowing it kills the worker).
//
//   cargo build -p hol_wasm --target wasm32-unknown-unknown --release
//   node scripts/wasm_smoke.mjs
//
// Optional arguments: the .wasm path and the course file.

import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..");
const wasmPath =
  process.argv[2] || join(root, "target/wasm32-unknown-unknown/release/hol_wasm.wasm");
const coursePath = process.argv[3] || join(root, "courses/proofs-checked.json");
const bytes = readFileSync(wasmPath);
const course = JSON.parse(readFileSync(coursePath, "utf8"));
const enc = new TextEncoder(), dec = new TextDecoder();
async function fresh() { return (await WebAssembly.instantiate(bytes, {})).instance.exports; }
function call(w, name, source, options, extra = []) {
  const put = (s) => { const b = enc.encode(s); const p = w.c2_alloc(b.length); new Uint8Array(w.memory.buffer, p, b.length).set(b); return [p, b.length]; };
  const [sp, sl] = put(source), [op, ol] = put(JSON.stringify(options));
  const ptr = w[name](sp, sl, op, ol, ...extra);
  w.c2_free(sp, sl); w.c2_free(op, ol);
  const len = new DataView(w.memory.buffer).getUint32(ptr, true);
  const out = JSON.parse(dec.decode(new Uint8Array(w.memory.buffer, ptr + 4, len).slice()));
  w.c2_free(ptr, len + 4);
  return out;
}
let failures = 0;
async function run(label, source, options, check, fn = "c2_analyze", extra = []) {
  const w = await fresh();
  const t = Date.now();
  try {
    const r = call(w, fn, source, options, extra);
    const verdict = check(r);
    if (verdict !== true) failures++;
    console.log(`${verdict === true ? "ok  " : "FAIL"} ${label} (${Date.now() - t} ms)${verdict === true ? "" : " -> " + verdict}`);
  } catch (e) { failures++; console.log(`TRAP ${label}: ${e.message}`); }
}
const firstErr = (r) => (r.diagnostics || []).find((d) => d.severity === "error")?.message || "";
const hw = "import std/prelude.ctea\n\ntheorem swap (P Q : Prop) : P /\\ Q -> Q /\\ P := by\n  intro h\n  exact and_comm h\n\ntheorem two (A B : Prop) : A /\\ B -> B /\\ A := by\n  intro h\n  simp\n  sorry\n";
await run("no section: accepted", hw, { path: "web/main.ctea" }, (r) => !r.rules && r.declarations.some((d) => d.name === "swap" && d.status === "accepted") || JSON.stringify(r).slice(0, 300));
await run("section ch02: rules reported at lines", hw, { path: "web/main.ctea", course, section: "ch02" }, (r) => {
  const errs = r.diagnostics.filter((d) => d.severity === "error").map((d) => `${d.line}:${d.message}`);
  return (r.rules?.section === "Chapter 2: Natural deduction" && errs.some((e) => e.startsWith("5:the theorem `and_comm` is not available")) && errs.some((e) => e.startsWith("9:`simp` is not available")) && r.library.find((e) => e.name === "and_comm")?.allowed === false && r.tier === "fol") || JSON.stringify({ rules: r.rules, errs, tier: r.tier });
});
await run("section ch06 allows simp and set library", "import std/prelude.ctea\n\ntheorem t (T : Type) (A : Set T) : A subset A := by\n  exact subset_refl\n", { path: "web/main.ctea", course, section: "ch06" }, (r) => r.ok === true || firstErr(r));
await run("counting library: pigeonhole is citable", "logic hol\nimport std/prelude.ctea\n\ntheorem t (A : Type) (S : Set A) (n m : Nat) : HasCard(S, n) -> HasCard(S, m) -> n = m := by\n  intro hn\n  intro hm\n  exact card_unique hn hm\n", { path: "web/main.ctea" }, (r) => (r.ok === true && r.library.some((e) => e.name === "pigeonhole")) || firstErr(r));
await run("decide evaluates and names the false part", "logic hol\ndata Color\n| red\n| green\n| blue\n\ntheorem yes : forall c : Color, c = red \\/ c = green \\/ c = blue := by\n  decide\n\ntheorem no : forall c : Color, c = red \\/ c = green := by\n  decide\n", {}, (r) => { const d = r.diagnostics.find((x) => x.severity === "error"); return (r.declarations.find((x) => x.name === "yes")?.status === "accepted" && d?.line === 11 && (d.notes || []).includes("it fails when c = blue")) || JSON.stringify(r.diagnostics).slice(0, 300); });
await run("graph library imports on request", "logic hol\nimport std/prelude.ctea\nimport std/graph.ctea\n\ndata V\n| p\n| q\n\ndef E (x y : V) : Prop := x = p /\\ y = q\n\ntheorem t : Reachable(E, p, q) := by\n  unfold Reachable\n  exists cons(q, nil)\n  decide\n\ntheorem u : Undirected(E) := by\n  unfold Undirected\n  decide\n", { path: "web/main.ctea" }, (r) => { const d = r.diagnostics.find((x) => x.severity === "error"); return (r.declarations.find((x) => x.name === "t")?.status === "accepted" && d?.line === 18 && (d.notes || []).includes("it fails when x = p, y = q")) || JSON.stringify(r.diagnostics).slice(0, 300); });
await run("unknown section is an error object", hw, { course, section: "nope" }, (r) => (r.error || "").includes("there is no section `nope`") || JSON.stringify(r).slice(0, 200));
await run("hints respect the section", "theorem t (A B : Prop) : A /\\ B -> B /\\ A := by\n  intro h\n  sorry\n", { path: "web/main.ctea", course, section: "ch01" }, (r) => (Array.isArray(r) && !r.some((h) => h.tactic.startsWith("cases"))) || JSON.stringify(r).slice(0, 300), "c2_hints", [2]);
await run("kernel rules shown per step", "theorem t (P Q : Prop) : P -> Q -> P /\\ Q := by\n  intro hp hq\n  split\n  exact hp\n  exact hq\n", {}, (r) => { const s = r.theorems[0].steps; return (s[0].rules.join() === "imp_intro ×2" && s[1].rules.join() === "and_intro") || JSON.stringify(s.map((x) => x.rules)); });
await run("did you mean", "theorem t (P : Prop) : P -> P := by\n  intro h\n  exatc h\n", {}, (r) => firstErr(r).includes("did you mean `exact`?") || firstErr(r));
await run("20000 nested parens refused", "theorem d : " + "(".repeat(20000) + "True" + ")".repeat(20000) + " := by\n  trivial\n", {}, (r) => firstErr(r).includes("nested too deeply") || firstErr(r));
await run("50 nested parens fine", "theorem d : " + "(".repeat(45) + "True" + ")".repeat(45) + " := by\n  trivial\n", {}, (r) => r.ok === true || firstErr(r));
await run("chain of 240 implications", "theorem d (P : Prop) : " + "P -> ".repeat(240) + "P := by\n  sorry\n", {}, (r) => firstErr(r) === "" || firstErr(r));
await run("numeral 500", "logic fol_nat\ntheorem t : 500 = 500 := by\n  refl\n", {}, (r) => r.ok === true || firstErr(r));
await run("numeral 501 refused", "logic fol_nat\ntheorem t : 501 = 501 := by\n  refl\n", {}, (r) => firstErr(r).includes("too large to check") || firstErr(r));
await run("20 * 20 = 400 by refl", "logic fol_nat\ntheorem t : 20 * 20 = 400 := by\n  refl\n", {}, (r) => r.ok === true || firstErr(r));
await run("22 * 22 = 484 by simp", "logic fol_nat\ntheorem t : 22 * 22 = 484 := by\n  simp\n  refl\n", {}, (r) => r.ok === true || firstErr(r));
await run("30 * 30 computed (over depth cap)", "logic fol_nat\ntheorem t : 30 * 30 = 30 * 30 := by\n  simp\n  refl\n", {}, (r) => typeof r.ok === "boolean" || "no result");
process.exit(failures ? 1 : 0);
