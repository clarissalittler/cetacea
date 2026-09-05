import test from 'node:test';
import assert from 'node:assert/strict';
import { CheckerClient } from '../checker-client.mjs';
function setup(timeoutMs = 1000) {
  const workers = [];
  const client = new CheckerClient({ timeoutMs, createWorker: () => {
    const worker = { messages: [], postMessage(message) { this.messages.push(message); }, terminate() { this.terminated = true; } };
    workers.push(worker);
    return worker;
  } });
  return { client, workers };
}
test('cancellation terminates work and ignores stale responses after restart', async () => {
  const { client, workers } = setup();
  const old = client.run('source', ['old']);
  const previous = workers[0];
  client.stop();
  assert.equal(await old, null);
  assert.equal(previous.terminated, true);
  const fresh = client.run('source', ['fresh']);
  previous.onmessage({ data: { id: 1, result: 'stale' } });
  workers[1].onmessage({ data: { id: 2, result: 'current' } });
  assert.equal(await fresh, 'current');
  client.stop();
});
test('queued cursor work is replaced with the latest position', async () => {
  const { client, workers } = setup();
  const check = client.run('source', ['source'], 'check');
  const old = client.run('goals', [1], 'goals');
  const latest = client.run('goals', [2], 'goals');
  assert.equal(await old, null);
  workers[0].onmessage({ data: { id: 1, result: 'checked' } });
  assert.deepEqual(workers[0].messages[1].args, [2]);
  workers[0].onmessage({ data: { id: 3, result: 'new goals' } });
  assert.equal(await latest, 'new goals');
  assert.equal(await check, 'checked');
  client.stop();
});
test('a stalled worker times out, terminates, and can be replaced', async () => {
  const { client, workers } = setup(20);
  await assert.rejects(client.run('source', ['stalled']), /too long/);
  assert.equal(workers[0].terminated, true);
  const retry = client.run('source', ['retry']);
  workers[1].onmessage({ data: { id: 2, result: 'ok' } });
  assert.equal(await retry, 'ok');
  client.stop();
});
test('worker traps reject queued requests and permit a clean retry', async () => {
  const { client, workers } = setup();
  const active = client.run('source', []);
  const queued = client.run('goals', []);
  const failures = [assert.rejects(active, /trap/), assert.rejects(queued, /trap/)];
  workers[0].onmessage({ data: { id: 1, error: 'trap' } });
  await Promise.all(failures);
  assert.equal(workers[0].terminated, true);
  client.stop();
});
