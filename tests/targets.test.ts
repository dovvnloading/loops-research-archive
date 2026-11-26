import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { test } from 'node:test';
import { AGENT_LINE, openTargets } from '../src/research/targets.ts';

const read = (path: string) =>
  JSON.parse(readFileSync(new URL(`../${path}`, import.meta.url), 'utf8'));

test('the ready list shown in the app is the one the repository publishes', () => {
  const published = read('results/open_targets.json');
  const computed = openTargets(read('ledger.json').obligations);
  assert.equal(computed.open, published.counts.open);
  assert.deepEqual(
    computed.ready.map(({ id, downstream }) => [id, downstream]),
    published.ready.map((row: { id: string; downstream: number }) => [row.id, row.downstream]),
  );
});

test('the line people copy points at the briefing that exists in the repository', () => {
  assert.match(AGENT_LINE, /\/main\/AGENTS\.md and follow it\.$/);
  assert.ok(
    readFileSync(new URL('../AGENTS.md', import.meta.url), 'utf8').startsWith(
      '# Briefing for AI agents',
    ),
  );
});
