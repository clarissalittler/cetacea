// Project archives contain source text only. Acceptance is always recomputed.
const encoder = new TextEncoder();
const MAX_ARCHIVE_BYTES = 50 * 1024 * 1024;
const ownKeys = (value, keys) => Object.keys(value).every(key => keys.includes(key));

export function validateProject(value, {allowOversizedSources = false} = {}) {
  if (!value || typeof value !== 'object' || Array.isArray(value)
      || !ownKeys(value, ['root', 'files']) || typeof value.root !== 'string'
      || !Array.isArray(value.files) || value.files.length === 0 || value.files.length > 64) {
    throw new Error('A project needs an active file and between 1 and 64 source files.');
  }
  const paths = new Set();
  let size = 0;
  const files = value.files.map(file => {
    if (!file || typeof file !== 'object' || !ownKeys(file, ['path', 'source'])
        || typeof file.path !== 'string' || typeof file.source !== 'string') {
      throw new Error('Each project file must contain only a path and source text.');
    }
    const path = file.path;
    if (!path.isWellFormed() || !file.source.isWellFormed()) {
      throw new Error('Project paths and sources must contain valid Unicode text.');
    }
    if (!path.endsWith('.ctea') || encoder.encode(path).length > 512
        || path.startsWith('std/') || /[\\:\u0000-\u001f\u007f-\u009f]/u.test(path)
        || path.split('/').some(part => ['', '.', '..'].includes(part))) {
      throw new Error(`Invalid project source path: ${path}`);
    }
    if (paths.has(path)) throw new Error(`Duplicate project source path: ${path}`);
    paths.add(path);
    const length = encoder.encode(file.source).length;
    if (!allowOversizedSources && length > 1024 * 1024) throw new Error(`Source ${path} exceeds 1 MiB.`);
    size += length;
    if (!allowOversizedSources && size > 8 * 1024 * 1024) throw new Error('Project sources exceed 8 MiB.');
    return {path, source: file.source};
  });
  if (!paths.has(value.root)) throw new Error('The active project file is missing.');
  return {root: value.root, files};
}

export function parseProjectArchive(text) {
  if (typeof text !== 'string' || encoder.encode(text).length > MAX_ARCHIVE_BYTES) {
    throw new Error('Project archive exceeds 50 MiB.');
  }
  let value;
  try { value = JSON.parse(text); } catch { throw new Error('This is not a valid project JSON archive.'); }
  if (!value || value.format !== 'cetacea-project' || value.version !== 1
      || !ownKeys(value, ['format', 'version', 'root', 'files'])) {
    throw new Error('Unsupported project archive format or fields.');
  }
  return validateProject({root: value.root, files: value.files});
}

export function serializeProjectArchive(project) {
  return JSON.stringify({format: 'cetacea-project', version: 1, ...validateProject(project)}, null, 2) + '\n';
}

export async function readProjectArchive(file) {
  if (file.size > MAX_ARCHIVE_BYTES) throw new Error('Project archive exceeds 50 MiB.');
  const bytes = await file.arrayBuffer();
  if (bytes.byteLength > MAX_ARCHIVE_BYTES) throw new Error('Project archive exceeds 50 MiB.');
  let text;
  try { text = new TextDecoder('utf-8', {fatal: true}).decode(bytes); }
  catch { throw new Error('Project archives must use UTF-8 text.'); }
  return parseProjectArchive(text);
}

export class ProjectFiles {
  constructor(project, options) { this.project = validateProject(project, options); }
  get source() { return this.project.files.find(file => file.path === this.project.root).source; }
  // Preserve an edit even when it exceeds checker limits: downloading the file
  // must remain possible. Validation happens before checking/exporting archives.
  edit(source) {
    if (typeof source !== 'string') throw new Error('Source must be text.');
    this.project.files.find(file => file.path === this.project.root).source = source;
  }
  select(path) {
    if (!this.project.files.some(file => file.path === path)) throw new Error('Project file is missing.');
    this.project.root = path;
  }
  add(path, source = '') {
    const next = validateProject({root: path, files: [...this.project.files, {path, source}]});
    this.project = next;
  }
  rename(path) {
    const next = validateProject({root: path, files: this.project.files.map(file =>
      file.path === this.project.root ? {path, source: file.source} : file)});
    this.project = next;
  }
  snapshot() { return structuredClone(this.project); }
}
