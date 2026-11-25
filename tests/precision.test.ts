import assert from 'node:assert/strict';
import { test } from 'node:test';
import { decimalToFixed, fixedMandelbrot, precisionBits, precisionCoordinate, preparePrecisionFrame, roundDivide } from '../src/lib/precision.ts';

test('plain decimal coordinates round from exact rationals without Number conversion', () => {
  const unit = 1n << 128n;
  assert.equal(decimalToFixed('-.125', 128), -unit / 8n);
  assert.equal(decimalToFixed('+0.5', 128), unit / 2n);
  assert.equal(decimalToFixed('0.1', 128), (unit + 5n) / 10n);
  assert.equal(roundDivide(-5n, 2n), -3n);
  assert.equal(roundDivide(5n, 2n), 3n);
});

test('coordinates separated below float64 resolution remain distinct in a deep window', () => {
  const a = '1.' + '0'.repeat(59) + '1';
  const b = '1.' + '0'.repeat(59) + '2';
  assert.equal(Number(a), Number(b));
  const bits = precisionBits(60);
  assert.ok(decimalToFixed(b, bits) > decimalToFixed(a, bits));
  const frame = preparePrecisionFrame({ centerRe: a, centerIm: '0', zoomExponent: 60, iterations: 128, width: 256 });
  const left = precisionCoordinate(frame, 127, 96);
  const right = precisionCoordinate(frame, 128, 96);
  assert.ok(right[0] > left[0], 'Adjacent pixels must not collapse at the supported zoom limit.');
  assert.equal(left[0] + right[0], 2n * frame.re);
});

test('pixel placement respects aspect ratio and complex-plane orientation', () => {
  const frame = preparePrecisionFrame({ centerRe: '0', centerIm: '0', zoomExponent: 0, iterations: 128, width: 128 });
  assert.equal(frame.height, 96);
  const topLeft = precisionCoordinate(frame, 0, 0);
  const bottomRight = precisionCoordinate(frame, 127, 95);
  assert.ok(topLeft[0] < 0n && topLeft[1] > 0n);
  assert.equal(topLeft[0], -bottomRight[0]);
  assert.equal(topLeft[1], -bottomRight[1]);
});

test('fixed-point recurrence matches known exact fixed, periodic and escaping orbits', () => {
  const bits = 128;
  const unit = 1n << BigInt(bits);
  assert.equal(fixedMandelbrot(0n, 0n, bits, 128).escaped, false);
  assert.equal(fixedMandelbrot(-unit, 0n, bits, 128).escaped, false);
  assert.equal(fixedMandelbrot(unit, 0n, bits, 128).iteration, 3);
  assert.equal(fixedMandelbrot(unit, 0n, bits, 128).magnitudeSquared, 25n * unit);
  assert.equal(fixedMandelbrot(2n * unit, 0n, bits, 128).iteration, 2);
});

test('bounded validation rejects oversized, nonfinite and ambiguous inputs', () => {
  for (const value of ['1e-20', 'NaN', 'Infinity', '4.0001', '--.2', '0.' + '1'.repeat(101)]) {
    assert.throws(() => decimalToFixed(value, 128));
  }
  for (const exponent of [-1, 61, NaN, Infinity, 2.5]) assert.throws(() => precisionBits(exponent));
  assert.throws(() => preparePrecisionFrame({ centerRe: '0', centerIm: '0', zoomExponent: 0, iterations: 100000, width: 256 }));
  assert.throws(() => preparePrecisionFrame({ centerRe: '0', centerIm: '0', zoomExponent: 0, iterations: 128, width: 8192 }));
});
