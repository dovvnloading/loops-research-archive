import assert from 'node:assert/strict';
import { test } from 'node:test';
import { DEFAULT_EXACT_VIEW, decimalToFixed, fixedToNumber, normalizeDecimal, panExactView, pointAtPixel, precisionBits, validateExactView, zoomExactView } from '../src/precision/coordinates.ts';
import { buildReference, fixedEscape, fixedPixel, floatEscape, prepareKernel } from '../src/precision/kernel.ts';
import { colorTile } from '../src/precision/palette.ts';
import type { ExactView } from '../src/precision/types.ts';

test('exact coordinates accept scientific notation without losing significant digits', () => {
  assert.equal(normalizeDecimal('+1.20000e-4'), '0.00012');
  assert.equal(normalizeDecimal('-0e-200'), '0');
  const a = '-1.' + '9'.repeat(199) + '8';
  const b = '-1.' + '9'.repeat(199) + '9';
  assert.equal(Number(a), Number(b));
  const bits = precisionBits('1e-200');
  assert.ok(bits >= 780);
  assert.notEqual(decimalToFixed(a, bits), decimalToFixed(b, bits));
  assert.equal(fixedToNumber(1n << 2048n, 2048), 1);
});

test('deep navigation keeps neighboring points distinct and anchors stable', () => {
  const view: ExactView = { ...DEFAULT_EXACT_VIEW, center: { re: '-2', im: '0' }, span: '1e-200' };
  const a = pointAtPixel(view, 0.499, 0.5);
  const b = pointAtPixel(view, 0.501, 0.5);
  assert.equal(Number(a.re), Number(b.re));
  assert.notEqual(a.re, b.re);
  const navigable = { ...view, span: '1e-150' };
  const anchor = pointAtPixel(navigable, 0.25, 0.75, 1.5);
  const zoomed = zoomExactView(navigable, 0.25, 0.25, 0.75, 1.5);
  const anchorAfter = pointAtPixel(zoomed, 0.25, 0.75, 1.5);
  const bits = precisionBits(zoomed.span);
  const anchorError = decimalToFixed(anchor.re, bits) - decimalToFixed(anchorAfter.re, bits);
  assert.ok((anchorError < 0n ? -anchorError : anchorError) < 4n);
  assert.equal(Number(zoomed.span), 2.5e-151);
  const deepBits = precisionBits(view.span);
  assert.ok(decimalToFixed(panExactView(view, 0.1, 0).center.re, deepBits) < decimalToFixed(view.center.re, deepBits));
  assert.ok(Number(panExactView(view, 0, 0.1).center.im) > 0);
  assert.equal(Number(zoomExactView(view, 0.1).span), 1e-200, 'The supported depth limit is enforced.');
});

test('exact view validation rejects ambiguous, unbounded and lossy inputs', () => {
  for (const bad of [
    { ...DEFAULT_EXACT_VIEW, center: { re: -0.5, im: '0' } },
    { ...DEFAULT_EXACT_VIEW, span: '1e-201' },
    { ...DEFAULT_EXACT_VIEW, span: '-1' },
    { ...DEFAULT_EXACT_VIEW, span: '33' },
    { ...DEFAULT_EXACT_VIEW, iterations: 100000 },
    { ...DEFAULT_EXACT_VIEW, center: { re: 'NaN', im: '0' } },
    { ...DEFAULT_EXACT_VIEW, center: { re: '1e100000000', im: '0' } },
    { ...DEFAULT_EXACT_VIEW, palette: 'unknown' },
  ]) assert.throws(() => validateExactView(bad));
  assert.deepEqual(validateExactView(DEFAULT_EXACT_VIEW), DEFAULT_EXACT_VIEW);
});

test('rounded independent kernels reproduce simple exact escaping and periodic orbits', () => {
  const bits = 192, unit = 1n << BigInt(bits);
  assert.equal(fixedEscape(0n, 0n, 0n, 0n, bits, 128).escaped, false);
  assert.equal(fixedEscape(-unit, 0n, 0n, 0n, bits, 128).escaped, false);
  assert.equal(fixedEscape(unit, 0n, 0n, 0n, bits, 128).iteration, 3);
  assert.equal(fixedEscape(2n * unit, 0n, 0n, 0n, bits, 128).iteration, 2);
  assert.equal(floatEscape(1, 0, 0, 0, 128).iteration, 3);
});

test('Mandelbrot perturbation agrees with independent BigInt pixels at 20, 60 and 200 decimal depth', () => {
  for (const depth of [20, 60, 200]) {
    const view: ExactView = { ...DEFAULT_EXACT_VIEW, center: { re: '-2', im: '0' }, span: `1e-${depth}`, iterations: 1024 };
    const kernel = prepareKernel(view);
    assert.equal(kernel.mode, 'perturbation');
    const reference = buildReference(view, kernel.bits + 80);
    for (let y = 0; y < 3; y++) for (let x = 0; x < 6; x++) {
      const sample = kernel.sample(x, y, 6, 3);
      const [re, im] = fixedPixel(reference, x, y, 6, 3);
      const control = fixedEscape(re, im, 0n, 0n, reference.bits, view.iterations);
      assert.equal(sample.escaped, control.escaped, `depth ${depth}, (${x},${y}) escape classification`);
      assert.equal(sample.iteration, control.iteration, `depth ${depth}, (${x},${y}) escape iteration`);
      assert.ok(Math.abs(sample.smooth - control.smooth) < 1e-7, `depth ${depth}, (${x},${y}) smooth escape`);
    }
  }
});

test('deep Julia perturbation agrees with independent BigInt starting points', () => {
  const view: ExactView = { ...DEFAULT_EXACT_VIEW, family: 'julia', center: { re: '2', im: '0' }, julia: { re: '-2', im: '0' }, span: '1e-100', iterations: 512 };
  const kernel = prepareKernel(view), reference = buildReference(view, kernel.bits + 80);
  for (let y = 0; y < 3; y++) for (let x = 0; x < 4; x++) {
    const sample = kernel.sample(x, y, 4, 3), [re, im] = fixedPixel(reference, x, y, 4, 3);
    const control = fixedEscape(reference.juliaRe, reference.juliaIm, re, im, reference.bits, view.iterations);
    assert.equal(sample.escaped, control.escaped);
    assert.equal(sample.iteration, control.iteration);
    assert.ok(Math.abs(sample.smooth - control.smooth) < 1e-7);
  }
});

test('complex-boundary perturbation is checked against a higher precision recurrence', () => {
  const view: ExactView = { ...DEFAULT_EXACT_VIEW, center: { re: '-0.743643887037151', im: '0.13182590420533' }, span: '1e-12', iterations: 4096 };
  const kernel = prepareKernel(view), reference = buildReference(view, kernel.bits + 96);
  for (const [x, y] of [[0, 0], [2, 0], [1, 1], [0, 2], [2, 2]]) {
    const sample = kernel.sample(x, y, 3, 3), [re, im] = fixedPixel(reference, x, y, 3, 3);
    const control = fixedEscape(re, im, 0n, 0n, reference.bits, view.iterations);
    assert.equal(sample.escaped, control.escaped);
    assert.equal(sample.iteration, control.iteration);
    assert.ok(Math.abs(sample.smooth - control.smooth) < 1e-4);
  }
});

test('the exact imaginary gateway remains numerically resolved at 120 decimal depth', () => {
  const view: ExactView = { ...DEFAULT_EXACT_VIEW, center: { re: '0', im: '1' }, span: '1e-120', iterations: 2048 };
  const kernel = prepareKernel(view), reference = buildReference(view, kernel.bits + 96);
  const escapedAt = new Set<number>();
  for (const [x, y] of [[0, 0], [2, 0], [1, 1], [0, 2], [2, 2]]) {
    const sample = kernel.sample(x, y, 3, 3), [re, im] = fixedPixel(reference, x, y, 3, 3);
    const control = fixedEscape(re, im, 0n, 0n, reference.bits, view.iterations);
    assert.equal(sample.escaped, control.escaped);
    assert.equal(sample.iteration, control.iteration);
    assert.ok(Math.abs(sample.smooth - control.smooth) < 1e-6);
    escapedAt.add(sample.iteration);
  }
  assert.ok(escapedAt.size > 1, 'The deep image must resolve different orbits, not collapse to one floating point coordinate.');
});

test('palette changes preserve escape samples and create opaque deterministic pixels', () => {
  const samples = new Float32Array([-1, 3.5, 32.125, 100.5]);
  const before = [...samples];
  const first = colorTile(samples, 'glacier', 1), second = colorTile(samples, 'aurora', 1);
  assert.deepEqual([...samples], before);
  assert.notDeepEqual(first, second);
  assert.deepEqual(first, colorTile(samples, 'glacier', 1));
  for (let i = 3; i < first.length; i += 4) assert.equal(first[i], 255);
});
