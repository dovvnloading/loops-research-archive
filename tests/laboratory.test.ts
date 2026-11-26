import test from 'node:test';
import assert from 'node:assert/strict';
import { analyzeOrbit, compareFields, refineCenter, regionRow, sampleParameter, validateComparisonSettings, validateScanSettings } from '../src/laboratory/math.ts';
import { decodeSurveyPixels, encodeSurveyPixels, prepareExperimentReplay, restoreComparisonResult, restoreSurveyResult, stableExperimentKey, validateOrbitSettings } from '../src/laboratory/replay.ts';

test('orbit instrument distinguishes known attracting periods, escape, and repelling repetition', () => {
  assert.equal(analyzeOrbit({ re: 0, im: 0 }).period, 1);
  assert.equal(analyzeOrbit({ re: -1, im: 0 }).period, 2);
  assert.equal(analyzeOrbit({ re: -1.7548776662466927, im: 0 }).period, 3);
  const escaping = analyzeOrbit({ re: 1, im: 0 });
  assert.equal(escaping.disposition, 'escaped');
  assert.equal(escaping.escapeIteration, 3);
  const repelling = analyzeOrbit({ re: -2, im: 0 });
  assert.equal(repelling.disposition, 'unresolved');
  assert.equal(repelling.period, null, 'exact floating-point repetition on a repelling cycle must not be labeled attracting');
  for (const c of [{ re: 0, im: 0 }, { re: 16, im: 0 }, { re: -2, im: 0 }, { re: -.75, im: .1 }]) {
    const result = analyzeOrbit(c);
    const json = JSON.stringify(result, (_key, value) => { if (typeof value === 'number') assert.ok(Number.isFinite(value), 'all exported numbers must be finite'); return value; });
    assert.deepEqual(JSON.parse(json), result, 'orbit records are lossless JSON, including null logarithmic singularities');
  }
});

test('center refinement converges numerically and rejects lower-period roots', () => {
  const answer = refineCenter({ re: -1.75, im: .001 }, 3);
  assert.equal(answer.refined, true);
  assert.ok(Math.abs(answer.center.re + 1.7548776662466927) < 1e-12);
  assert.ok(Math.abs(answer.center.im) < 1e-12);
  assert.ok(answer.residual < 1e-13);
  assert.equal(refineCenter({ re: 0, im: 0 }, 2).refined, false);
});

test('survey settings bound computation and reject numerically unresolvable windows', () => {
  const settings = { reMin: -2, reMax: 1, imMin: -1, imMax: 1, resolution: 48, iterations: 512, maxPeriod: 32 };
  assert.deepEqual(validateScanSettings(settings), settings);
  const first = sampleParameter(settings, 0, 0);
  assert.equal(first.re, -2 + 3 / 96);
  assert.equal(first.im, 1 - 2 / 96);
  assert.throws(() => validateScanSettings({ ...settings, resolution: 10000 }), /grid/);
  assert.throws(() => validateScanSettings({ ...settings, reMin: 1, reMax: 1 + Number.EPSILON }), /float64/);
  assert.throws(() => validateScanSettings({ ...settings, imMin: NaN }), /finite/);
});

test('comparison detects self-equality and conjugation with the same numerical conditions', () => {
  const n = 48, a = new Float32Array(n * n), b = new Float32Array(n * n);
  const region = { re: '-.7435', im: '.1314', span: '.006' };
  for (let row = 0; row < n; row++) {
    regionRow(region, n, 256, row, a);
    regionRow({ ...region, im: '-.1314' }, n, 256, row, b);
  }
  const self = compareFields(a, a, n, true);
  assert.equal(self.alignment, 'identity');
  assert.equal(self.meanAbsoluteDifference, 0);
  assert.ok(Math.abs((self.correlation ?? 0) - 1) < 1e-12);
  const symmetry = compareFields(a, b, n, true);
  assert.equal(symmetry.alignment, 'reflect-vertical');
  assert.ok(symmetry.meanAbsoluteDifference < 1e-6);
  assert.ok(compareFields(a, b, n, false).meanAbsoluteDifference > .001);
});

test('constant fields do not fabricate correlation or nonescape overlap', () => {
  const values = new Float32Array(16).fill(.25), result = compareFields(values, values, 4, false);
  assert.equal(result.correlation, null);
  assert.equal(result.finiteNonescapeJaccard, null);
  assert.equal(result.meanAbsoluteDifference, 0);
});

test('comparison preserves coordinate strings while rejecting precision loss and empty values', () => {
  const settings = { a: { re: '-0.743500', im: '0.1314', span: '.006' }, b: { re: '-.7435', im: '-.1314', span: '.006' }, resolution: 96, iterations: 512, align: true };
  assert.equal(validateComparisonSettings(settings).a.re, '-0.743500');
  assert.throws(() => validateComparisonSettings({ ...settings, a: { ...settings.a, span: '1e-30' } }), /float64/);
  assert.throws(() => validateComparisonSettings({ ...settings, a: { ...settings.a, re: '' } }), /coordinates/);
});

const replayBase = { schema: 'loops-laboratory-v1', method: 'loops-quadratic-instruments-1', precision: 'IEEE-754 binary64', createdAt: '2026-11-26T00:00:00.000Z', claim: 'Numerical experiment; not certified.' };

test('journal replay validates algorithm and preserves the original coordinate spelling', () => {
  const input = { ...replayBase, instrument: 'orbit', settings: { re: '-1.000', im: '0e0', iterations: 2048, maxPeriod: 64, tolerance: 1e-9, initial: { re: 0, im: 0 } } };
  const restored = prepareExperimentReplay(input);
  assert.deepEqual(restored.manifest, input);
  assert.equal(validateOrbitSettings(restored.manifest.settings).re, '-1.000');
  assert.throws(() => prepareExperimentReplay({ ...input, precision: 'binary32' }), /unsupported method or numerical precision/);
  assert.throws(() => prepareExperimentReplay({ ...input, settings: { ...input.settings, initial: { re: 1, im: 0 } } }), /critical orbit/);
  assert.throws(() => prepareExperimentReplay({ ...input, settings: { ...input.settings, tolerance: 1e-4 } }), /tolerance/);
});

test('equivalent replay objects have one semantic identity', () => {
  assert.equal(stableExperimentKey({ b: [2, 3], a: { x: 1, y: '1.000' } }), stableExperimentKey({ a: { y: '1.000', x: 1 }, b: [2, 3] }));
  assert.notEqual(stableExperimentKey({ coordinate: '1.00' }), stableExperimentKey({ coordinate: '1' }), 'original decimal spelling is part of the reproducible record');
  assert.throws(() => stableExperimentKey({ invalid: Infinity }), /non-finite/);
});

test('survey replay restores previews losslessly and rejects inconsistent accounting', () => {
  const settings = { reMin: -2, reMax: 1, imMin: -1, imMax: 1, resolution: 16, iterations: 512, maxPeriod: 32 };
  const pixels = Uint8ClampedArray.from({ length: 16 * 16 * 4 }, (_, index) => index % 256);
  const record = { processed: 256, total: 256, escaped: 230, attracting: 20, unresolved: 6, periods: { '1': 20 }, candidates: [], elapsed: 24, pixelsBase64: encodeSurveyPixels(pixels) };
  const restored = restoreSurveyResult(record, settings);
  assert.deepEqual(restored?.pixels, pixels);
  assert.equal(restored?.processed, 256);
  assert.throws(() => restoreSurveyResult({ ...record, unresolved: 20 }, settings), /sample counts/);
  assert.throws(() => restoreSurveyResult({ ...record, periods: { '1': 21 } }, settings), /period counts/);
  assert.throws(() => decodeSurveyPixels(record.pixelsBase64, 32), /dimensions/);
  const withoutImage = { ...record }; delete (withoutImage as Partial<typeof record>).pixelsBase64;
  assert.equal(restoreSurveyResult(withoutImage, settings)?.pixels, undefined, 'legacy records restore their catalog without fabricating an image');
});

test('comparison replay recalculates metrics from the saved fields', () => {
  const settings = { a: { re: '-.5', im: '0', span: '3.2' }, b: { re: '-.5', im: '0', span: '3.2' }, resolution: 32, iterations: 256, align: true };
  const a = Array.from({ length: 1024 }, (_, i) => (i % 32) / 32);
  const result = restoreComparisonResult({ a, b: [...a], metrics: { meanAbsoluteDifference: 999 }, elapsed: 1 }, settings);
  assert.equal(result?.metrics.meanAbsoluteDifference, 0);
  assert.equal(result?.metrics.alignment, 'identity');
  assert.throws(() => restoreComparisonResult({ a: [1], b: [1], elapsed: 1 }, settings), /dimensions/);
  assert.throws(() => restoreComparisonResult({ a: a.map(() => NaN), b: a, elapsed: 1 }, settings), /dimensions or values/);
});
