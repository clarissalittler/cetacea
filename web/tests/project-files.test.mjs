import test from 'node:test';
import assert from 'node:assert/strict';
import {ProjectFiles, parseProjectArchive, serializeProjectArchive, readProjectArchive, validateProject} from '../project-files.mjs';
const initial = () => ({root: 'lesson/main.ctea', files: [
  {path: 'lesson/main.ctea', source: 'import ../lib/helper.ctea\n'},
  {path: 'lib/helper.ctea', source: '-- ∀\r\n'}
]});
test('archives preserve nested paths, active file, Unicode and line endings without proof receipts', async () => {
  const project = initial();
  const text = serializeProjectArchive(project);
  assert.deepEqual(parseProjectArchive(text), project);
  assert.deepEqual(await readProjectArchive(new File([text], 'homework.ctea-project')), project);
  assert.throws(() => parseProjectArchive(JSON.stringify({...JSON.parse(text), hol_certified: true})), /Unsupported/);
});
test('editing and switching retain every file; snapshots do not alias live state', () => {
  const input = initial();
  const workspace = new ProjectFiles(input);
  const saved = workspace.snapshot();
  workspace.edit('edited');
  workspace.select('lib/helper.ctea');
  assert.equal(workspace.source, '-- ∀\r\n');
  workspace.edit('helper edit');
  workspace.select('lesson/main.ctea');
  assert.equal(workspace.source, 'edited');
  assert.deepEqual(saved, input);
  workspace.add('lesson/extra.ctea', 'new');
  assert.equal(workspace.source, 'new');
  workspace.rename('lesson/renamed.ctea');
  assert.equal(workspace.source, 'new');
});
test('invalid additions, renames and selections are atomic', () => {
  const workspace = new ProjectFiles(initial());
  const before = workspace.snapshot();
  for (const action of [() => workspace.add('lib/helper.ctea'), () => workspace.rename('lib/helper.ctea'),
    () => workspace.add('../escape.ctea'), () => workspace.select('missing.ctea')]) {
    assert.throws(action);
    assert.deepEqual(workspace.snapshot(), before);
  }
});
test('project imports reject ambiguous and reserved paths, wrong versions, invalid files and unknown fields', () => {
  for (const path of ['../a.ctea', '/a.ctea', 'a//b.ctea', 'a/./b.ctea', 'std/nat.ctea', 'builtin:std/nat.ctea', 'a\\b.ctea', 'a\0.ctea']) {
    assert.throws(() => validateProject({root: path, files: [{path, source: ''}]}));
  }
  assert.throws(() => validateProject({...initial(), files: [...initial().files, initial().files[0]]}), /Duplicate/);
  assert.throws(() => validateProject({...initial(), root: 'missing.ctea'}), /missing/);
  assert.throws(() => parseProjectArchive('{broken'), /valid/);
  assert.throws(() => parseProjectArchive('{"format":"cetacea-project","version":2}'), /Unsupported/);
});
test('oversized edits remain recoverable as source, while project checking/export validation rejects them', () => {
  const workspace = new ProjectFiles(initial());
  const source = 'x'.repeat(1024 * 1024 + 1);
  workspace.edit(source);
  assert.equal(workspace.source, source);
  assert.throws(() => serializeProjectArchive(workspace.snapshot()), /1 MiB/);
  workspace.edit('repaired');
  assert.equal(parseProjectArchive(serializeProjectArchive(workspace.snapshot())).files[0].source, 'repaired');
});
test('archive limits and invalid Unicode are rejected before replacing a project', async () => {
  const file = {path: 'a.ctea', source: ''};
  assert.throws(() => validateProject({root: file.path, files: Array(65).fill(file)}), /64/);
  assert.throws(() => validateProject({root: file.path, files: [{...file, source: '\ud800'}]}), /Unicode/);
  assert.throws(() => validateProject({root: '0.ctea', files: Array.from({length: 9}, (_, n) =>
    ({path: `${n}.ctea`, source: ' '.repeat(1024 * 1024)}))}), /8 MiB/);
  await assert.rejects(readProjectArchive({size: 50 * 1024 * 1024 + 1}), /50 MiB/);
  await assert.rejects(readProjectArchive(new File([new Uint8Array([255])], 'bad.ctea-project')), /UTF-8/);
});
