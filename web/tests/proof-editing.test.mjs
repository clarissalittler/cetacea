import test from 'node:test';
import assert from 'node:assert/strict';
import {tacticInsertion} from '../proof-editing.mjs';
test('first tactics and branch tactics receive a proof-body indent', () => {
  for (const [source, expected] of [
    ['theorem answer : True := by', '\n  trivial'],
    ['theorem answer : True := by -- start here', '\n  trivial'],
    ['  | zero =>', '\n    trivial'],
    ['    | left h => -- branch', '\n      trivial'],
  ]) assert.deepEqual(tacticInsertion(source, source.length, 'trivial'), {offset: source.length, text: expected});
});
test('insertion preserves existing indentation and inserts after the saved cursor line', () => {
  const source = 'theorem example : True := by\n  trivial\n-- following';
  const cursor = source.indexOf('trivial');
  assert.deepEqual(tacticInsertion(source, cursor, 'exact h'), {offset: source.indexOf('\n--'), text: '\n  exact h'});
  assert.equal(tacticInsertion('    exact h', 8, 'refl').text, '\n    refl');
});
test('blank lines follow proof indentation without changing unrelated source', () => {
  assert.equal(tacticInsertion('theorem answer : True := by\n', 100, 'trivial').text, '\n  trivial');
  assert.equal(tacticInsertion('  intro h\n\n', 100, 'exact h').text, '\n  exact h');
  assert.equal(tacticInsertion('    ', 4, 'trivial').text, '\n    trivial');
});
