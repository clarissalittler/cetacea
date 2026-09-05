import {validateSavedAssignment} from './assignment-files.mjs?v=2';
import {validateProject} from './project-files.mjs';
export const WORK_KEY = 'cetacea.web.work.v1';
const LEGACY_KEY = 'cetacea.web.editor';
export const MAX_SOURCE_BYTES = 1024 * 1024;

export function fileName(name) {
  const base = String(name).split(/[\\/]/).pop().replace(/[\u0000-\u001f]/g, '').trim();
  return base.endsWith('.ctea') ? base : `${base || 'proof'}.ctea`;
}

export async function readProofFile(file) {
  if (file.size > MAX_SOURCE_BYTES) throw new Error('This file exceeds the 1 MiB source limit.');
  const bytes = await file.arrayBuffer();
  if (bytes.byteLength > MAX_SOURCE_BYTES) throw new Error('This file exceeds the 1 MiB source limit.');
  let source;
  try { source = new TextDecoder('utf-8', {fatal: true}).decode(bytes); }
  catch { throw new Error('Open a UTF-8 text .ctea file.'); }
  if (source.includes('\0')) throw new Error('This appears to be a binary file. Open a text .ctea file.');
  return {source, name: fileName(file.name)};
}

function savedEntry(entry, checkpoint = false) {
  if (!entry || typeof entry.source !== 'string' || typeof entry.name !== 'string'
      || (checkpoint && typeof entry.savedAt !== 'string')) throw new Error('Invalid saved work');
  const result = {source: entry.source, name: entry.name, project: null};
  if (entry.assignment != null) result.assignment = validateSavedAssignment(entry.assignment);
  if (checkpoint) result.savedAt = entry.savedAt;
  if (entry.project != null) {
    result.project = validateProject(entry.project, {allowOversizedSources: true});
    if (result.project.files.find(file => file.path === result.project.root).source !== entry.source) {
      throw new Error('Saved project and active source disagree');
    }
  }
  return result;
}

export class StudentWork {
  constructor(storage, fallback, {withLock = callback => callback(), onStatus = () => {}} = {}) {
    this.storage = storage;
    this.withLock = withLock;
    this.onStatus = onStatus;
    this.pending = null;
    this.generation = 0;
    this.persistedGeneration = 0;
    this.expectedRaw = null;
    this.conflict = false;
    this.state = {version: 1, source: fallback, name: 'proof.ctea', history: []};
    this.error = '';
    this.readOnly = false;
    this.recoveryData = null;
    let parsed;
    let foundSavedData = false;
    try {
      const raw = storage().getItem(WORK_KEY);
      this.expectedRaw = raw;
      if (raw !== null) {
        foundSavedData = true;
        this.recoveryData = raw;
        parsed = JSON.parse(raw);
        if (parsed?.version !== 1 || !Array.isArray(parsed.history)
            || parsed.history.length > 10 || (parsed.recoveryData != null && typeof parsed.recoveryData !== 'string')) {
          throw new Error('Invalid saved work');
        }
        this.state = {version: 1, ...savedEntry(parsed), history: parsed.history.map(entry => savedEntry(entry, true))};
        this.recoveryData = parsed.recoveryData ?? null;
        if (this.recoveryData !== null) this.state.recoveryData = this.recoveryData;
      } else {
        this.state.source = storage().getItem(LEGACY_KEY) ?? fallback;
      }
    } catch {
      this.readOnly = true;
      if (parsed?.version === 1) {
        try { Object.assign(this.state, savedEntry(parsed)); } catch { /* Keep the fallback editor. */ }
        if (Array.isArray(parsed.history)) {
          this.state.history = parsed.history.slice(0, 10).flatMap(entry => {
            try { return [savedEntry(entry, true)]; } catch { return []; }
          });
        }
      }
      this.error = foundSavedData
        ? 'Saved work could not be read completely. Autosave is paused. Download saved data to keep the original, or restore an available checkpoint.'
        : 'Browser storage could not be read. Download your work before reloading; existing saved work will not be overwritten.';
    }
  }
  get saving() { return this.pending !== null; }
  pauseForConflict() {
    this.conflict = true;
    this.readOnly = true;
    this.error = 'Saved data changed in another tab. Autosave is paused. Download this tab’s work before reloading; the other tab’s save was not overwritten.';
  }
  observeStorageChange() {
    if (this.readOnly) return;
    try {
      if (this.storage().getItem(WORK_KEY) !== this.expectedRaw) this.pauseForConflict();
    } catch {
      this.error = 'Browser storage could not be read. Download your work before closing this page.';
    }
    this.onStatus();
  }
  async resumeAutosave() {
    if (!this.readOnly || this.conflict || this.recoveryData === null) return false;
    return this.write(true);
  }
  async save(source, name = this.state.name, project = null, assignment = this.state.assignment ?? null) {
    const nextAssignment = assignment == null ? null : validateSavedAssignment(assignment);
    this.state.assignment = nextAssignment;
    this.state.source = source;
    this.state.name = fileName(name);
    this.state.project = project == null ? null : structuredClone(project);
    this.generation += 1;
    if (this.readOnly) return false;
    return this.write();
  }
  write(resume = false) {
    if (this.pending) return this.pending;
    const attempt = Promise.resolve().then(() => this.withLock(() => {
      if (this.readOnly && !resume) return false;
      if (this.storage().getItem(WORK_KEY) !== this.expectedRaw) {
        this.pauseForConflict();
        return false;
      }
      const next = resume ? {...this.state, recoveryData: this.recoveryData} : this.state;
      const raw = JSON.stringify(next);
      // The browser supplies a shared exclusive lock. Compare and write occur
      // inside that lock, with no await between them.
      this.storage().setItem(WORK_KEY, raw);
      this.expectedRaw = raw;
      this.state = next;
      this.persistedGeneration = this.generation;
      this.readOnly = false;
      this.error = '';
      return true;
    })).catch(() => {
      this.error = resume
        ? 'Could not resume autosave. The original saved data is unchanged; download your work before closing this page.'
        : 'Autosave failed or safe browser storage is unavailable. Your work is still here; download it before closing this page.';
      return false;
    });
    this.pending = attempt.then(result => {
      this.pending = null;
      if (result && this.persistedGeneration !== this.generation) return this.write();
      this.onStatus();
      return result;
    });
    this.onStatus();
    return this.pending;
  }
  checkpoint(source, name = this.state.name, project = null, assignment = this.state.assignment ?? null) {
    const nextAssignment = assignment == null ? null : validateSavedAssignment(assignment);
    const latest = this.state.history[0];
    if (!latest || latest.source !== source || latest.name !== name
        || JSON.stringify(latest.project ?? null) !== JSON.stringify(project)
        || JSON.stringify(latest.assignment ?? null) !== JSON.stringify(nextAssignment)) {
      this.state.history.unshift({assignment: nextAssignment, source, name: fileName(name), project: structuredClone(project), savedAt: new Date().toISOString()});
      this.state.history.length = Math.min(this.state.history.length, 10);
    }
    return this.save(source, name, project, nextAssignment);
  }
}
