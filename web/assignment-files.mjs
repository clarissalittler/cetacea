import {validateProject} from './project-files.mjs';
const encoder = new TextEncoder();
const limit = 50 * 1024 * 1024;
const keys = (value, allowed) => Object.keys(value).every(key => allowed.includes(key));
export function parseAssignmentArchive(text) {
  if (typeof text !== 'string' || encoder.encode(text).length > limit) throw new Error('Assignment archive exceeds 50 MiB.');
  let value;
  try { value = JSON.parse(text); } catch { throw new Error('This is not a valid assignment JSON archive.'); }
  if (!value || value.format !== 'cetacea-assignment' || value.version !== 1
      || !keys(value, ['format', 'version', 'path', 'source', 'files'])
      || typeof value.path !== 'string' || typeof value.source !== 'string' || !Array.isArray(value.files)) {
    throw new Error('Unsupported assignment archive format or fields.');
  }
  if (!value.path.isWellFormed() || !value.source.isWellFormed()
      || !value.path.endsWith('.ctea-assignment') || encoder.encode(value.path).length > 512
      || /[\\:\u0000-\u001f\u007f-\u009f]/u.test(value.path)
      || value.path.split('/').some(part => ['', '.', '..'].includes(part))) throw new Error('Invalid assignment path or Unicode text.');
  if (encoder.encode(value.source).length > 64 * 1024) throw new Error('Assignment manifest exceeds 64 KiB.');
  const files = value.files.length ? validateProject({root: value.files[0]?.path, files: value.files}).files : [];
  return {path: value.path, source: value.source, files};
}
export async function readAssignmentArchive(file) {
  if (file.size > limit) throw new Error('Assignment archive exceeds 50 MiB.');
  const bytes = await file.arrayBuffer();
  if (bytes.byteLength > limit) throw new Error('Assignment archive exceeds 50 MiB.');
  let text;
  try { text = new TextDecoder('utf-8', {fatal: true}).decode(bytes); }
  catch { throw new Error('Assignment archives must use UTF-8 text.'); }
  return parseAssignmentArchive(text);
}

// Saved selections carry their import filename, never cached grading results.
export function validateSavedAssignment(value) {
  if (!value || !keys(value, ['path', 'source', 'files', 'archiveName'])
      || typeof value.archiveName !== 'string' || value.archiveName.length > 1024) {
    throw new Error('Invalid saved assignment selection.');
  }
  const context = parseAssignmentArchive(JSON.stringify({format: 'cetacea-assignment', version: 1,
    path: value.path, source: value.source, files: value.files}));
  return {...context, archiveName: value.archiveName};
}
