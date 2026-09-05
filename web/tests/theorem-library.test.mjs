import test from 'node:test';
import assert from 'node:assert/strict';
import { libraryEntries } from '../theorem-library.mjs';
const theorem = (name, receipt_id, is_imported = true) => ({name, receipt_id, is_imported, statement: 'P -> P'});
test('aliases share one search entry with a usable matching name', () => {
  const entries = [theorem('L.identity', 4), theorem('R.identity', 4)];
  assert.equal(libraryEntries(entries).length, 1);
  const [right] = libraryEntries(entries, 'R.identity');
  assert.equal(right.name, 'R.identity');
  assert.deepEqual(right.aliases, ['L.identity', 'R.identity']);
  assert.equal(libraryEntries(entries, 'missing').length, 0);
});
test('identical propositions and uncertified entries are kept separate', () => {
  const entries = [theorem('one', 1), theorem('two', 2), theorem('three', null), theorem('four', null), theorem('local', 1, false)];
  assert.equal(libraryEntries(entries).length, 5);
  assert.equal(libraryEntries(entries, '', 'imported').length, 4);
  assert.deepEqual(libraryEntries(entries, '', 'local').map(t => t.name), ['local']);
});
test('a suggested alias promotes the group without hiding other lookups', () => {
  const entries = [theorem('L.identity', 4), theorem('R.identity', 4), theorem('A.other', 5)];
  const suggested = new Set(['R.identity']);
  const [first] = libraryEntries(entries, '', 'all', suggested);
  assert.equal(first.name, 'R.identity');
  assert.equal(first.suggested, true);
  assert.equal(libraryEntries(entries, 'L.identity', 'all', suggested)[0].name, 'L.identity');
});
