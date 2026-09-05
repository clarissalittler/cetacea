import test from 'node:test';
import assert from 'node:assert/strict';
import {StudentWork, WORK_KEY, readProofFile, MAX_SOURCE_BYTES} from '../student-work.mjs';
function storage(entries = []) {
  const data = new Map(entries);
  return {data, getItem: key => data.get(key) ?? null, setItem: (key, value) => data.set(key, value)};
}
test('legacy source including empty work migrates without losing bytes; checkpoints survive reload', async () => {
  const disk = storage([['cetacea.web.editor', '']]);
  const work = new StudentWork(() => disk, 'sample');
  assert.equal(work.state.source, '');
  await work.checkpoint('∀ x\r\n', 'first.ctea');
  await work.save('second', 'next');
  const loaded = new StudentWork(() => disk, 'sample');
  assert.equal(loaded.state.source, 'second');
  assert.equal(loaded.state.name, 'next.ctea');
  assert.equal(loaded.state.history[0].source, '∀ x\r\n');
  for (let i = 0; i < 20; i++) await loaded.checkpoint(String(i));
  assert.equal(loaded.state.history.length, 10);
  assert.equal(loaded.state.history[9].source, '10');
});
test('quota failure retains current work and checkpoints in memory and permits retry', async () => {
  const disk = storage();
  const work = new StudentWork(() => disk, 'sample');
  disk.setItem = () => { throw new Error('quota'); };
  assert.equal(await work.checkpoint('valuable', 'proof.ctea'), false);
  assert.match(work.error, /Autosave failed/);
  assert.equal(work.state.source, 'valuable');
  assert.equal(work.state.history[0].source, 'valuable');
  disk.setItem = (key, value) => disk.data.set(key, value);
  assert.equal(await work.save('new work'), true);
  assert.equal(work.error, '');
  assert.equal(new StudentWork(() => disk, '').state.history[0].source, 'valuable');
});
test('damaged and future-version saved data is preserved rather than overwritten', async () => {
  for (const raw of ['{broken', '{"version":2}', '{"version":1,"source":"x","name":"x","history":[null]}']) {
    const disk = storage([[WORK_KEY, raw]]);
    const work = new StudentWork(() => disk, 'sample');
    assert.match(work.error, /could not be read/);
    assert.equal(await work.save('replacement'), false);
    assert.equal(disk.getItem(WORK_KEY), raw);
  }
});
test('initially unreadable storage cannot overwrite unseen saved work when it returns', async () => {
  const disk = storage([[WORK_KEY, 'existing work']]);
  let unavailable = true;
  const work = new StudentWork(() => {
    if (unavailable) throw new Error('storage disabled');
    return disk;
  }, 'sample');
  assert.match(work.error, /storage could not be read/);
  unavailable = false;
  assert.equal(await work.save('new work'), false);
  assert.equal(disk.getItem(WORK_KEY), 'existing work');
});
test('opening UTF-8 preserves source and rejects binary, invalid encoding and excessive files', async () => {
  const source = '-- ∀\r\ntheorem x : True := by\r\n  trivial\r\n';
  assert.deepEqual(await readProofFile(new File([source], 'homework.ctea')), {source, name: 'homework.ctea'});
  await assert.rejects(readProofFile(new File(['a\0b'], 'bad.ctea')), /binary/);
  await assert.rejects(readProofFile(new File([new Uint8Array([255])], 'bad.ctea')), /UTF-8/);
  await assert.rejects(readProofFile({size: MAX_SOURCE_BYTES + 1}), /1 MiB/);
});
test('project checkpoints and autosave retain supporting files and oversized drafts on reload', async () => {
  const disk = storage();
  const work = new StudentWork(() => disk, 'sample');
  const project = {root: 'main.ctea', files: [{path: 'main.ctea', source: 'draft'}, {path: 'helper.ctea', source: 'helper'}]};
  await work.checkpoint('draft', 'main.ctea', project);
  project.files[1].source = 'changed';
  await work.save('draft', 'main.ctea', project);
  const reloaded = new StudentWork(() => disk, 'sample');
  assert.equal(reloaded.state.project.files[1].source, 'changed');
  assert.equal(reloaded.state.history[0].project.files[1].source, 'helper');
  project.files[0].source = 'x'.repeat(1024 * 1024 + 1);
  await work.save(project.files[0].source, 'main.ctea', project);
  assert.equal(new StudentWork(() => disk, '').state.source, project.files[0].source);
});
test('damaged active work exposes intact checkpoints and resumes without discarding original data', async () => {
  const raw = JSON.stringify({version: 1, source: 42, name: 'broken.ctea', history: [null,
    {source: 'valuable', name: 'saved.ctea', savedAt: '2026-09-04T00:00:00Z'}]});
  const disk = storage([[WORK_KEY, raw]]);
  const work = new StudentWork(() => disk, 'sample');
  assert.equal(work.recoveryData, raw);
  assert.equal(work.state.history.length, 1);
  assert.equal(work.state.history[0].source, 'valuable');
  await work.save('valuable', 'saved.ctea');
  assert.equal(disk.getItem(WORK_KEY), raw);
  assert.equal(await work.resumeAutosave(), true);
  const loaded = new StudentWork(() => disk, 'sample');
  assert.equal(loaded.state.source, 'valuable');
  assert.equal(loaded.recoveryData, raw);
  await loaded.save('continued');
  assert.equal(new StudentWork(() => disk, '').recoveryData, raw);
});
test('failed recovery writes and a changed save slot preserve the original or newer data', async () => {
  const disk = storage([[WORK_KEY, '{damaged']]);
  const work = new StudentWork(() => disk, 'sample');
  await work.save('recovered');
  disk.setItem = () => { throw new Error('quota'); };
  assert.equal(await work.resumeAutosave(), false);
  assert.equal(disk.getItem(WORK_KEY), '{damaged');
  assert.equal(work.readOnly, true);
  disk.data.set(WORK_KEY, 'newer work');
  assert.equal(await work.resumeAutosave(), false);
  assert.match(work.error, /another tab/);
  assert.equal(disk.getItem(WORK_KEY), 'newer work');
});
test('an invalid checkpoint does not hide a valid active project, while unknown versions stay opaque', async () => {
  const disk = storage([[WORK_KEY, JSON.stringify({version: 1, source: 'current', name: 'proof.ctea', history: [null]})]]);
  assert.equal(new StudentWork(() => disk, 'sample').state.source, 'current');
  const future = JSON.stringify({version: 2, source: 'future', name: 'proof.ctea', history: [{source: 'not ours', name: 'proof.ctea', savedAt: ''}]});
  disk.data.set(WORK_KEY, future);
  const work = new StudentWork(() => disk, 'sample');
  assert.equal(work.state.source, 'sample');
  assert.equal(work.state.history.length, 0);
  assert.equal(work.recoveryData, future);
});
test('concurrent saves serialize comparison and write, preserving both tabs in memory', async () => {
  const disk = storage();
  let queue = Promise.resolve();
  const withLock = callback => { const next = queue.then(callback); queue = next.catch(() => {}); return next; };
  const first = new StudentWork(() => disk, 'sample', {withLock});
  const second = new StudentWork(() => disk, 'sample', {withLock});
  const results = await Promise.all([first.save('first tab'), second.save('second tab')]);
  assert.deepEqual(results, [true, false]);
  assert.equal(JSON.parse(disk.getItem(WORK_KEY)).source, 'first tab');
  assert.equal(second.state.source, 'second tab');
  assert.equal(second.conflict, true);
  assert.equal(await second.save('still editable'), false);
  assert.equal(JSON.parse(disk.getItem(WORK_KEY)).source, 'first tab');
});
test('queued saves coalesce to the latest project snapshot and storage notifications preserve drafts', async () => {
  const disk = storage();
  let release;
  const gate = new Promise(resolve => { release = resolve; });
  const work = new StudentWork(() => disk, '', {withLock: async callback => { await gate; return callback(); }});
  const old = work.save('old');
  const latest = work.save('latest');
  assert.equal(work.saving, true);
  release();
  await Promise.all([old, latest]);
  assert.equal(work.saving, false);
  assert.equal(JSON.parse(disk.getItem(WORK_KEY)).source, 'latest');
  // An old storage event is harmless when the actual current slot is ours.
  work.observeStorageChange();
  assert.equal(work.conflict, false);
  disk.data.set(WORK_KEY, 'another tab');
  work.observeStorageChange();
  assert.equal(work.conflict, true);
  assert.equal(work.state.source, 'latest');
});
test('unavailable browser locking cannot silently fall back to uncoordinated writes', async () => {
  const disk = storage();
  const work = new StudentWork(() => disk, '', {withLock: () => { throw new Error('unavailable'); }});
  assert.equal(await work.save('valuable'), false);
  assert.equal(disk.getItem(WORK_KEY), null);
  assert.equal(work.state.source, 'valuable');
  assert.match(work.error, /safe browser storage/);
});
test('assignment selections and distinct assignment checkpoints survive reload without cached acceptance', async () => {
  const disk = storage();
  const work = new StudentWork(() => disk, 'sample');
  const assignment = {path: 'task.ctea-assignment', source: "version = 1\nprofile = 'prop'\n", files: [], archiveName: 'lesson.ctea-task'};
  await work.checkpoint('proof', 'proof.ctea', null, assignment);
  await work.checkpoint('proof', 'proof.ctea', null, {...assignment, source: "version = 1\nprofile = 'fol'\n"});
  const loaded = new StudentWork(() => disk, 'sample');
  assert.equal(loaded.state.history.length, 2);
  assert.equal(loaded.state.assignment.archiveName, 'lesson.ctea-task');
  assert.match(loaded.state.assignment.source, /fol/);
  assert.deepEqual(loaded.state.history[1].assignment, assignment);
  await loaded.save('proof', 'proof.ctea', null, null);
  assert.equal(new StudentWork(() => disk, 'sample').state.assignment, undefined);
  await assert.rejects(work.save('proof', 'proof.ctea', null, {...assignment, accepted: true}), /Invalid saved assignment/);
});
test('damaged saved assignment preserves original storage and intact checkpoints', async () => {
  const disk = storage();
  const work = new StudentWork(() => disk, 'sample');
  await work.checkpoint('valuable');
  const value = JSON.parse(disk.getItem(WORK_KEY));
  value.assignment = {accepted: true};
  const original = JSON.stringify(value);
  disk.setItem(WORK_KEY, original);
  const loaded = new StudentWork(() => disk, 'sample');
  assert.equal(loaded.readOnly, true);
  assert.equal(loaded.state.history[0].source, 'valuable');
  assert.equal(await loaded.save('draft'), false);
  assert.equal(disk.getItem(WORK_KEY), original);
});
