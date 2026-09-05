import test from 'node:test';
import assert from 'node:assert/strict';
import {encodeProjectRequest} from '../project-request.mjs';
const project = {root: 'x.ctea', files: [{path: 'x.ctea', source: '∀'}]};
test('project packet lengths count UTF-8 bytes and preserve operation coordinates', () => {
  const bytes = encodeProjectRequest(project, 'goals', {line: 7, column: 9});
  const view = new DataView(bytes.buffer);
  let offset = 0;
  const number = () => { const n = view.getUint32(offset, true); offset += 4; return n; };
  const string = () => { const len = number(); const s = new TextDecoder().decode(bytes.subarray(offset, offset + len)); offset += len; return s; };
  assert.equal(number(), 0x31505443);
  assert.equal(number(), 2);
  assert.equal(number(), 7);
  assert.equal(number(), 9);
  assert.equal(string(), 'x.ctea');
  assert.equal(string(), '');
  assert.equal(number(), 1);
  assert.equal(string(), 'x.ctea');
  assert.equal(number(), 3);
  assert.equal(new TextDecoder().decode(bytes.subarray(offset)), '∀');
});
test('project transport rejects excessive fields, files, and invalid coordinates before allocation', () => {
  assert.throws(() => encodeProjectRequest(project, 'unknown'), /Unknown/);
  assert.throws(() => encodeProjectRequest(project, 'goals', {line: -1}), /number/);
  assert.throws(() => encodeProjectRequest({...project, files: Array(65).fill(project.files[0])}, 'check'), /64/);
  assert.throws(() => encodeProjectRequest({...project, root: 'é'.repeat(300)}, 'check'), /size limit/);
  assert.throws(() => encodeProjectRequest({root: 'x.ctea', files: [{path: 'x.ctea', source: 'a'.repeat(1024 * 1024 + 1)}]}, 'check'), /oversized/);
});
test('assignment requests use a distinct version and enforce combined file and manifest limits', () => {
  const assignment = {path: 'task.ctea-assignment', source: "version = 1\nprofile = 'prop'\n", files: []};
  const bytes = encodeProjectRequest(project, 'check', {assignment});
  assert.equal(new DataView(bytes.buffer).getUint32(0, true), 0x32505443);
  assert.throws(() => encodeProjectRequest(project, 'check', {assignment: false}), /Assignment/);
  assert.throws(() => encodeProjectRequest(project, 'check', {assignment: {...assignment, files: Array(64).fill(project.files[0])}}), /64/);
  assert.throws(() => encodeProjectRequest(project, 'check', {assignment: {...assignment, source: 'x'.repeat(64 * 1024 + 1)}}), /oversized/);
});
