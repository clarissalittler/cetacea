// CTP1/CTP2: little-endian u32 fields and length-prefixed UTF-8 strings.
const encoder = new TextEncoder();
export function encodeProjectRequest(project, operation, options = {}) {
  const operations = {check: 0, outline: 1, goals: 2, tactic: 3, explain: 4};
  if (!Object.hasOwn(operations, operation)) throw new Error('Unknown project operation');
  if (!Array.isArray(project.files) || project.files.length > 64) throw new Error('A project may contain at most 64 source files');
  const assignment = options.assignment;
  if (assignment != null && (typeof assignment !== 'object' || !Array.isArray(assignment.files) || assignment.files.length + project.files.length > 64)) {
    throw new Error('Assignment and project may contain at most 64 source files together');
  }
  const chunks = [];
  let size = 0;
  function number(value) {
    if (!Number.isInteger(value) || value < 0 || value > 0xffffffff) throw new Error('Invalid project request number');
    const bytes = new Uint8Array(4);
    new DataView(bytes.buffer).setUint32(0, value, true);
    chunks.push(bytes); size += 4;
  }
  function string(value, limit) {
    if (typeof value !== 'string' || value.length > limit) throw new Error('Invalid or oversized project request field');
    const bytes = encoder.encode(value);
    if (bytes.length > limit) throw new Error('Project request field exceeds its size limit');
    number(bytes.length); chunks.push(bytes); size += bytes.length;
  }
  number(assignment ? 0x32505443 : 0x31505443);
  number(operations[operation]);
  number(operation === 'goals' ? options.line ?? 1 : options.tacticIndex ?? 0);
  number(options.column ?? 1);
  string(project.root, 512);
  string(options.theorem ?? '', 4096);
  number(project.files.length);
  let sourceBytes = 0;
  function files(entries) {
    for (const file of entries) {
      string(file.path, 512);
      const before = size;
      string(file.source, 1024 * 1024);
      sourceBytes += size - before - 4;
      if (sourceBytes > 8 * 1024 * 1024) throw new Error('Project sources exceed 8 MiB');
    }
  }
  files(project.files);
  if (assignment) {
    string(assignment.path, 512);
    string(assignment.source, 64 * 1024);
    number(assignment.files.length);
    files(assignment.files);
  }
  const packet = new Uint8Array(size);
  let offset = 0;
  for (const chunk of chunks) { packet.set(chunk, offset); offset += chunk.length; }
  return packet;
}
