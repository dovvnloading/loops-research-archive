import assert from 'node:assert/strict';
import { test } from 'node:test';
import { DEFAULT_STATE } from '../src/presets.ts';
import { createSnapshotURL, decodeSnapshot, encodeSnapshot, journalCSV, mergeImportedEntries, parseJournalArchive, readSharedSnapshot, serializeJournal, validateJournalEntry, validateJournalPayload } from '../src/journal/codec.ts';
import type { JournalEntry, JournalPayload } from '../src/journal/types.ts';

function payload(): JournalPayload {
  return {
    engine: { ...structuredClone(DEFAULT_STATE), scene: 'mandelbrot', center: [-0.743643887037151, 0.13182590420533], scale: 1e-7, iterations: 4096 },
    exact: { family: 'mandelbrot', center: { re: '-0.7436438870371510079237964411000000000000000000000000000000000000000123456789', im: '0.13182590420533000000000000000000000000000000000000000000000000000000987654321' }, span: '1.2500e-80', julia: { re: '-0.7454300', im: '0.1130100' }, iterations: 12000, palette: 'aurora' },
    sourceRevision: '073634f4d1727cc1b5261a439c0e08d80b9092c8',
  };
}

function entry(id = 'observation-a', parentId: string | null = null): JournalEntry {
  return { version: 2, id, parentId, title: 'A very small spiral', notes: 'A question about the boundary, not a proof.', tags: ['spirals', 'follow-up'], createdAt: '2026-11-25T15:00:00.000Z', updatedAt: '2026-11-25T15:00:00.000Z', payload: payload() };
}

test('journal exports and imports exact coordinate strings without dropping a single digit', () => {
  const original = entry();
  original.payload.experiment = { format: 'loops-experiment', estimate: 27, decimalBoundary: '123456789012345678901234567890' };
  const restored = parseJournalArchive(serializeJournal([original])).entries[0];
  assert.deepEqual(restored, original);
  assert.equal(restored.payload.exact.center.re, original.payload.exact.center.re);
  assert.equal(restored.payload.exact.span, '1.2500e-80');
  assert.equal(restored.payload.exact.julia.re, '-0.7454300');
  assert.equal(restored.payload.exact.iterations, 12000);
});

test('snapshot links retain project subpaths and exact state without leaking notes or experiments', () => {
  const original = payload(); original.experiment = { privateNotes: 'π / private observations 👁' };
  const url = createSnapshotURL(original, 'https://example.test/some/project/?outdated=1#archive');
  const parsed = new URL(url);
  assert.equal(parsed.pathname, '/some/project/');
  assert.equal(parsed.hash, '');
  assert.deepEqual([...parsed.searchParams.keys()], ['s']);
  const restored = readSharedSnapshot(url)!;
  assert.equal(restored.experiment, undefined);
  assert.deepEqual(restored.exact, original.exact);
  assert.deepEqual(restored.engine, original.engine);
  assert.equal(restored.sourceRevision, original.sourceRevision);
  assert.equal(readSharedSnapshot('https://example.test/'), null);
});

test('malformed shared payloads, unsupported versions and excessive links are rejected', () => {
  for (const value of ['!!!', 'a'.repeat(40_001), btoa('null'), btoa(JSON.stringify({ v: 99, ...payload() }))]) assert.throws(() => decodeSnapshot(value));
  const checked = decodeSnapshot(encodeSnapshot(payload()));
  assert.equal(checked.exact.family, 'mandelbrot');
  assert.throws(() => validateJournalPayload({ engine: {}, exact: payload().exact }), /unsupported fractal family/);
});

test('snapshot validation rejects numerical coordinate substitution and unsafe finite budgets', () => {
  for (const exactPatch of [
    { center: { re: -0.74, im: '0' } },
    { center: { re: 'Infinity', im: '0' } },
    { span: '1e-300' },
    { span: '-1' },
    { iterations: 20001 },
    { iterations: 128.5 },
    { family: 'unknown-family' },
  ]) assert.throws(() => validateJournalPayload({ ...payload(), exact: { ...payload().exact, ...exactPatch } }));
  assert.throws(() => validateJournalPayload({ ...payload(), experiment: { result: Infinity } }), /finite JSON/);
  assert.throws(() => validateJournalPayload({ ...payload(), experiment: JSON.parse('{"__proto__":{"polluted":true}}') }), /unsupported object key/);
  assert.equal(({} as { polluted?: boolean }).polluted, undefined);
});

test('imports reject duplicate IDs, unsupported files and parent cycles before changing storage', () => {
  assert.throws(() => parseJournalArchive('{broken json'), /not valid JSON/);
  assert.throws(() => parseJournalArchive(JSON.stringify({ entries: [] })), /LOOPS journal/);
  assert.throws(() => parseJournalArchive(serializeJournal([entry(), entry()])), /duplicate/);
  assert.throws(() => parseJournalArchive(serializeJournal([entry('a', 'b'), entry('b', 'a')])), /cycle/);
  assert.throws(() => validateJournalEntry(entry('a', 'a')), /own parent/);
  assert.equal(parseJournalArchive(serializeJournal([entry('a', 'an-external-parent')])).entries[0].parentId, 'an-external-parent');
});

test('reimporting identical observations is idempotent', () => {
  const original = entry();
  const merged = mergeImportedEntries([original], [structuredClone(original)], () => 'new-id');
  assert.equal(merged.added, 0);
  assert.equal(merged.skipped, 1);
  assert.deepEqual(merged.entries, [original]);
});

test('conflicting imports preserve existing records and remap descendant branch identities', () => {
  const parent = entry('parent');
  const child = entry('child', 'parent');
  const grandchild = entry('grandchild', 'child');
  const incoming = { ...parent, notes: 'A different observation with the same identifier.' };
  let nextId = 0;
  const merged = mergeImportedEntries([parent, child, grandchild], [incoming, structuredClone(child), structuredClone(grandchild)], () => `import-${++nextId}`);
  assert.equal(merged.added, 3);
  assert.equal(merged.skipped, 0);
  assert.equal(merged.entries[0], parent);
  assert.equal(merged.entries[3].id, 'import-1');
  assert.equal(merged.entries[4].parentId, 'import-1');
  assert.equal(merged.entries[5].parentId, 'import-2');
  assert.equal(merged.entries[3].notes, incoming.notes);
  assert.equal(parent.notes, 'A question about the boundary, not a proof.');
});

test('duplicate import ID generators fail safely instead of hanging forever', () => {
  const original = entry('same');
  assert.throws(() => mergeImportedEntries([original], [{ ...original, title: 'Changed' }], () => 'same'), /unique observation identifier/);
});

test('thumbnails only allow bounded bitmap data, never active SVG content', () => {
  assert.throws(() => validateJournalEntry({ ...entry(), thumbnail: 'data:image/svg+xml;base64,PHN2Zz4=' }), /thumbnail/i);
  assert.throws(() => validateJournalEntry({ ...entry(), thumbnail: 'https://tracker.example/image.png' }), /thumbnail/i);
  assert.throws(() => validateJournalEntry({ ...entry(), thumbnail: `data:image/png;base64,${'A'.repeat(2 * 1024 * 1024)}` }), /thumbnail/i);
  assert.equal(validateJournalEntry({ ...entry(), thumbnail: 'data:image/png;base64,AQID' }).thumbnail, 'data:image/png;base64,AQID');
});

test('CSV quotes embedded delimiters, line breaks and coordinates without numeric conversion', () => {
  const original = entry(); original.title = 'Spiral, "blue"'; original.notes = 'Line one\nLine two';
  const csv = journalCSV([original]);
  assert.ok(csv.includes('"Spiral, ""blue"""'));
  assert.ok(csv.includes('"Line one\nLine two"'));
  assert.ok(csv.includes(`"${original.payload.exact.center.re}"`));
  assert.ok(csv.includes('"1.2500e-80"'));
});

test('validated payloads own their nested settings and cannot mutate saved input', () => {
  const original = payload();
  const checked = validateJournalPayload(original);
  checked.exact.center.re = '0';
  checked.engine.center[0] = 0;
  checked.engine.controls.fov = 20;
  assert.notEqual(original.exact.center.re, '0');
  assert.equal(original.engine.center[0], -0.743643887037151);
  assert.equal(original.engine.controls.fov, DEFAULT_STATE.controls.fov);
});

test('local fallback serializes concurrent saves, restores deletions, and keeps prior data on quota failures', async () => {
  const previousStorage = Object.getOwnPropertyDescriptor(globalThis, 'localStorage');
  const previousIndexedDB = Object.getOwnPropertyDescriptor(globalThis, 'indexedDB');
  const storage = new Map<string, string>(); let full = false;
  Object.defineProperty(globalThis, 'indexedDB', { configurable: true, value: undefined });
  Object.defineProperty(globalThis, 'localStorage', { configurable: true, value: {
    getItem: (key: string) => storage.get(key) ?? null,
    setItem: (key: string, value: string) => { if (full) throw new DOMException('Quota exceeded', 'QuotaExceededError'); storage.set(key, value); },
    removeItem: (key: string) => { storage.delete(key); },
  } });
  try {
    const store = await import('../src/journal/store.ts');
    await store.initializeJournal();
    assert.equal(store.getJournalState().mode, 'local');
    const [first, second] = await Promise.all([
      store.saveEntry({ title: 'First', payload: payload() }),
      store.saveEntry({ title: 'Second', payload: payload() }),
    ]);
    assert.equal(store.getJournalState().entries.length, 2);
    assert.equal(parseJournalArchive(storage.get('loops.journal.v2')!).entries.length, 2);
    await store.updateEntry(first.id, { title: 'First, revised', notes: 'Persisted notes', tags: ['BOUNDARY'] });
    assert.equal(store.getJournalState().entries.find(item => item.id === first.id)?.notes, 'Persisted notes');
    assert.deepEqual(store.getJournalState().entries.find(item => item.id === first.id)?.tags, ['boundary']);
    const removed = await store.removeEntry(second.id);
    assert.equal(store.getJournalState().entries.length, 1);
    await store.restoreEntry(removed!);
    assert.equal(store.getJournalState().entries.length, 2);
    const beforeQuota = storage.get('loops.journal.v2');
    full = true;
    await assert.rejects(store.saveEntry({ title: 'Could not fit', payload: payload() }), /storage is full/);
    assert.equal(store.getJournalState().entries.length, 2);
    assert.equal(storage.get('loops.journal.v2'), beforeQuota);
    assert.match(store.getJournalState().error!, /previous observations are safe/);
    full = false;
    const imported = await store.importJournal(serializeJournal(store.getJournalState().entries));
    assert.equal(imported.added, 0);
    assert.equal(imported.skipped, 2);
  } finally {
    if (previousStorage) Object.defineProperty(globalThis, 'localStorage', previousStorage); else Reflect.deleteProperty(globalThis, 'localStorage');
    if (previousIndexedDB) Object.defineProperty(globalThis, 'indexedDB', previousIndexedDB); else Reflect.deleteProperty(globalThis, 'indexedDB');
  }
});
