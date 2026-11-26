import assert from 'node:assert/strict';
import { test } from 'node:test';
import { inflateSync } from 'node:zlib';
import { pngWithMetadata } from '../src/studio/png.ts';
import { parseJournalArchive, serializeJournal, validateJournalEntry } from '../src/journal/codec.ts';
import { DEFAULT_STATE } from '../src/presets.ts';
import type { JournalEntry } from '../src/journal/types.ts';

// Real RGBA PNGs, encoded with PNG filter 0 and zlib compression.
const PIXEL = Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGPg8V/wHwADYQH7xqB7zgAAAABJRU5ErkJggg==', 'base64');
const PATTERN = Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAIAAAACCAYAAABytg0kAAAAFklEQVR4nGP4z8DwHwwZGP7//w9kAABHygj4/BTyWgAAAABJRU5ErkJggg==', 'base64');
const SIGNATURE = Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]);

// Independent table-based CRC verification, rather than copying the writer's
// bit-at-a-time implementation.
const crcTable = Uint32Array.from({ length: 256 }, (_, byte) => {
  let crc = byte;
  for (let bit = 0; bit < 8; bit++) crc = crc & 1 ? 0xedb88320 ^ (crc >>> 1) : crc >>> 1;
  return crc >>> 0;
});
function crc32(bytes: Uint8Array) {
  let crc = 0xffffffff;
  for (const byte of bytes) crc = crcTable[(crc ^ byte) & 0xff] ^ (crc >>> 8);
  return (crc ^ 0xffffffff) >>> 0;
}
interface Chunk { type: string; data: Buffer; bytes: Buffer }
function readPNG(raw: Uint8Array): Chunk[] {
  const png = Buffer.from(raw);
  assert.deepEqual(png.subarray(0, 8), SIGNATURE);
  const chunks: Chunk[] = [];
  let offset = 8;
  while (offset < png.length) {
    assert.ok(offset + 12 <= png.length, 'Complete chunk header and CRC');
    const length = png.readUInt32BE(offset), end = offset + 12 + length;
    assert.ok(end <= png.length, 'Complete chunk payload');
    const type = png.toString('ascii', offset + 4, offset + 8);
    const actual = png.readUInt32BE(end - 4);
    assert.equal(actual, crc32(png.subarray(offset + 4, end - 4)), `Valid ${type} CRC`);
    chunks.push({ type, data: png.subarray(offset + 8, end - 4), bytes: png.subarray(offset, end) });
    offset = end;
    if (type === 'IEND') break;
  }
  assert.equal(chunks.at(-1)?.type, 'IEND');
  assert.equal(offset, png.length);
  return chunks;
}

function decodeITXt(chunk: Chunk) {
  assert.equal(chunk.type, 'iTXt');
  const data = chunk.data;
  const keywordEnd = data.indexOf(0);
  assert.ok(keywordEnd > 0 && keywordEnd <= 79, 'PNG keyword is 1–79 bytes');
  const keyword = data.toString('latin1', 0, keywordEnd);
  const flag = data[keywordEnd + 1], method = data[keywordEnd + 2];
  assert.equal(flag, 0, 'Text is uncompressed');
  assert.equal(method, 0, 'PNG compression method field is zero');
  const languageEnd = data.indexOf(0, keywordEnd + 3);
  const translatedEnd = data.indexOf(0, languageEnd + 1);
  assert.ok(languageEnd >= keywordEnd + 3 && translatedEnd > languageEnd);
  const language = data.toString('ascii', keywordEnd + 3, languageEnd);
  const translatedKeyword = new TextDecoder('utf-8', { fatal: true }).decode(data.subarray(languageEnd + 1, translatedEnd));
  const text = new TextDecoder('utf-8', { fatal: true }).decode(data.subarray(translatedEnd + 1));
  return { keyword, language, translatedKeyword, metadata: JSON.parse(text) as unknown };
}
function imageData(chunks: Chunk[]) { return inflateSync(Buffer.concat(chunks.filter(chunk => chunk.type === 'IDAT').map(chunk => chunk.data))); }

test('PNG provenance is a valid UTF-8 iTXt chunk placed before IEND with a valid CRC', () => {
  const metadata = { format: 'loops-image', version: 2, title: 'A spiral · π · 星', exact: { re: '-0.74364388703715100792379644112031847500000000001', im: '0.131825904205311970493132056385139818', span: '1e-80' }, notes: 'A numerical observation, not a proof.' };
  const chunks = readPNG(pngWithMetadata(PIXEL, metadata));
  assert.deepEqual(chunks.map(chunk => chunk.type), ['IHDR', 'IDAT', 'iTXt', 'IEND']);
  const parsed = decodeITXt(chunks[2]);
  assert.equal(parsed.keyword, 'LOOPS');
  assert.equal(parsed.language, '');
  assert.equal(parsed.translatedKeyword, '');
  assert.deepEqual(parsed.metadata, metadata);
});

test('writing metadata preserves every original image chunk and the decoded RGBA pixel', () => {
  const original = readPNG(PIXEL), annotated = readPNG(pngWithMetadata(PIXEL, { width: 1, height: 1 }));
  assert.deepEqual(annotated.filter(chunk => chunk.type !== 'iTXt').map(chunk => chunk.bytes), original.map(chunk => chunk.bytes));
  assert.deepEqual(imageData(annotated), Buffer.from([0, 12, 79, 160, 255]));
  assert.deepEqual(imageData(annotated), imageData(original));
  assert.deepEqual(PIXEL, Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGPg8V/wHwADYQH7xqB7zgAAAABJRU5ErkJggg==', 'base64'));
});

test('PNG metadata accepts a typed-array view with a nonzero underlying byte offset', () => {
  const backing = new Uint8Array(PIXEL.length + 19); backing.fill(255); backing.set(PIXEL, 11);
  const result = pngWithMetadata(backing.subarray(11, 11 + PIXEL.length), { sourceRevision: '073634f4d1727cc1b5261a439c0e08d80b9092c8' });
  const chunks = readPNG(result);
  assert.equal((decodeITXt(chunks.find(chunk => chunk.type === 'iTXt')!).metadata as { sourceRevision: string }).sourceRevision, '073634f4d1727cc1b5261a439c0e08d80b9092c8');
  assert.equal(backing[0], 255); assert.equal(backing.at(-1), 255);
});

test('every truncation of the fixture is rejected without producing a corrupt export', () => {
  for (let cut = 0; cut < PIXEL.length; cut++) assert.throws(() => pngWithMetadata(PIXEL.subarray(0, cut), {}), /PNG|chunk|end marker/, `Cut at byte ${cut}`);
  const oversizedChunk = Buffer.from(PIXEL); oversizedChunk.writeUInt32BE(0xffffffff, 8);
  assert.throws(() => pngWithMetadata(oversizedChunk, {}), /truncated chunk/);
  assert.throws(() => pngWithMetadata(new Uint8Array(80), {}), /valid PNG/);
});

test('the four-color thumbnail pattern survives journal validation, branching and JSON round trips unchanged', () => {
  const thumbnail = `data:image/png;base64,${PATTERN.toString('base64')}`;
  const parent: JournalEntry = { version: 2, id: 'pattern-parent', title: 'A reproducible pattern', notes: '', tags: ['test'], parentId: null, createdAt: '2026-11-25T15:00:00.000Z', updatedAt: '2026-11-25T15:00:00.000Z', thumbnail, payload: { engine: structuredClone(DEFAULT_STATE), exact: { family: 'mandelbrot', center: { re: '-0.5', im: '0' }, span: '3.2', julia: { re: '-0.74543', im: '0.11301' }, iterations: 768, palette: 'glacier' } } };
  const branch = validateJournalEntry({ ...parent, id: 'pattern-branch', parentId: parent.id, title: 'Pattern branch' });
  const restored = parseJournalArchive(serializeJournal([validateJournalEntry(parent), branch]));
  for (const entry of restored.entries) {
    assert.equal(entry.thumbnail, thumbnail);
    const bytes = Buffer.from(entry.thumbnail!.split(',')[1], 'base64');
    assert.deepEqual(bytes, PATTERN);
    assert.deepEqual(imageData(readPNG(bytes)), Buffer.from([0, 255, 0, 0, 255, 0, 255, 0, 255, 0, 0, 0, 255, 255, 255, 255, 0, 255]));
  }
  assert.equal(restored.entries[1].parentId, parent.id);
});
