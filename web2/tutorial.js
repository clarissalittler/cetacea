// The tutorial page: each complete sample gets a link that opens it in
// the editor.

function base64urlEncode(bytes) {
  let binary = "";
  for (const b of bytes) binary += String.fromCharCode(b);
  return btoa(binary).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

// The same encoding the editor's Share button uses.
async function compressText(text) {
  const stream = new Blob([text]).stream().pipeThrough(new CompressionStream("deflate-raw"));
  const bytes = new Uint8Array(await new Response(stream).arrayBuffer());
  return base64urlEncode(bytes);
}

const VERDICTS = {
  accepted: ["ok", "The checker accepts this."],
  failed: ["bad", "The checker rejects this — on purpose."],
  incomplete: ["partial", "Checks, but marked incomplete."],
};

for (const pre of document.querySelectorAll("pre[data-name]")) {
  const bar = document.createElement("div");
  bar.className = "sample-bar";
  const verdict = document.createElement("span");
  const [kind, text] = VERDICTS[pre.dataset.expect] || ["", ""];
  verdict.className = `verdict ${kind}`;
  verdict.textContent = text;
  bar.appendChild(verdict);
  pre.parentElement.appendChild(bar);
  if (typeof CompressionStream === "undefined") continue;
  compressText(pre.textContent).then((encoded) => {
    const params = new URLSearchParams();
    params.set("src", encoded);
    // Always say which section, even if none, so a sample is checked
    // under its own rules and not the ones the reader last picked.
    params.set("section", pre.dataset.section || "");
    const link = document.createElement("a");
    link.href = `./index.html#${params.toString()}`;
    link.target = "_blank";
    link.rel = "noopener";
    link.textContent = "Open in the editor ↗";
    bar.appendChild(link);
  });
}
