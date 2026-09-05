import test from 'node:test';
import assert from 'node:assert/strict';
import {parseAssignmentArchive, readAssignmentArchive} from '../assignment-files.mjs';
const task = {format: 'cetacea-assignment', version: 1, path: 'lesson/task.ctea-assignment', source: "version = 1\nprofile = 'prop'\n", files: []};
const parse = value => parseAssignmentArchive(JSON.stringify(value));
test('assignment archives preserve a separate manifest and pinned Unicode sources', async () => {
  const value = {...task, files: [{path: 'lesson/helper.ctea', source: '-- ∀\ntheorem helper : True := by\n  trivial\n'}]};
  const result = await readAssignmentArchive(new Blob([JSON.stringify(value)]));
  assert.deepEqual(result, {path: value.path, source: value.source, files: value.files});
  assert.deepEqual(parse(task).files, []);
});
test('assignment archives reject policy extras, invalid paths, duplicate libraries and excessive manifests', () => {
  assert.throws(() => parse({...task, accepted: true}), /Unsupported/);
  for (const path of ['../task.ctea-assignment', '/task.ctea-assignment', 'a\\task.ctea-assignment']) assert.throws(() => parse({...task, path}), /Invalid/);
  assert.throws(() => parse({...task, source: 'x'.repeat(65537)}), /64 KiB/);
  const file = {path: 'a.ctea', source: ''};
  assert.throws(() => parse({...task, files: [file, file]}), /Duplicate/);
  assert.throws(() => parse({...task, files: [{...file, path: 'std/a.ctea'}]}), /Invalid/);
});
test('assignment input rejects invalid UTF-8 before parsing', async () => {
  await assert.rejects(readAssignmentArchive(new Blob([new Uint8Array([255])])), /UTF-8/);
});
