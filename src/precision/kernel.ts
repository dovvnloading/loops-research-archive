import {
  decimalToFixed,
  fixedToNumber,
  precisionBits,
  roundDivide,
  validateExactView,
} from './coordinates.ts';
import type { ExactView } from './types.ts';

export interface EscapeSample {
  escaped: boolean;
  iteration: number;
  smooth: number;
  repaired: boolean;
}
export interface ReferenceOrbit {
  re: Float64Array;
  im: Float64Array;
  length: number;
  bits: number;
  centerRe: bigint;
  centerIm: bigint;
  span: bigint;
  juliaRe: bigint;
  juliaIm: bigint;
}
export interface PreparedKernel {
  view: ExactView;
  bits: number;
  mode: 'float64' | 'perturbation';
  reference?: ReferenceOrbit;
  sample(x: number, y: number, width: number, height: number): EscapeSample;
}
const bounded = (iteration: number, repaired = false): EscapeSample => ({
  escaped: false,
  iteration,
  smooth: -1,
  repaired,
});
function escaped(iteration: number, re: number, im: number, repaired = false): EscapeSample {
  const magnitude = Math.hypot(re, im);
  return {
    escaped: true,
    iteration,
    smooth: Math.max(0, iteration + 1 - Math.log2(Math.log2(Math.max(1.000001, magnitude)))),
    repaired,
  };
}
function radius(view: ExactView): number {
  return view.family === 'julia'
    ? Math.max(4, Math.hypot(Number(view.julia.re), Number(view.julia.im)) + 1)
    : 4;
}

/** A finite, rounded BigInt recurrence. This is an independent repair/reference path, not a proof of membership. */
export function fixedEscape(
  cr: bigint,
  ci: bigint,
  zr: bigint,
  zi: bigint,
  bits: number,
  iterations: number,
  escapeRadius = 4,
): EscapeSample {
  const unit = 1n << BigInt(bits);
  const limit = BigInt(Math.ceil(escapeRadius * escapeRadius)) * unit * unit;
  let checkpointRe = zr,
    checkpointIm = zi,
    checkpoint = 16;
  if (zr * zr + zi * zi > limit)
    return escaped(0, fixedToNumber(zr, bits), fixedToNumber(zi, bits), true);
  for (let n = 1; n <= iterations; n++) {
    const nr = roundDivide(zr * zr - zi * zi, unit) + cr;
    zi = roundDivide(2n * zr * zi, unit) + ci;
    zr = nr;
    if (zr * zr + zi * zi > limit)
      return escaped(n, fixedToNumber(zr, bits), fixedToNumber(zi, bits), true);
    if (zr === checkpointRe && zi === checkpointIm) return bounded(iterations, true);
    if (n === checkpoint) {
      checkpointRe = zr;
      checkpointIm = zi;
      checkpoint *= 2;
    }
  }
  return bounded(iterations, true);
}

export function floatEscape(
  cr: number,
  ci: number,
  zr: number,
  zi: number,
  iterations: number,
  escapeRadius = 4,
): EscapeSample {
  const limit = escapeRadius * escapeRadius;
  if (zr * zr + zi * zi > limit) return escaped(0, zr, zi);
  let checkpointRe = zr,
    checkpointIm = zi,
    checkpoint = 16;
  for (let n = 1; n <= iterations; n++) {
    const nr = zr * zr - zi * zi + cr;
    zi = 2 * zr * zi + ci;
    zr = nr;
    if (zr * zr + zi * zi > limit) return escaped(n, zr, zi);
    if (zr === checkpointRe && zi === checkpointIm) return bounded(iterations);
    if (n === checkpoint) {
      checkpointRe = zr;
      checkpointIm = zi;
      checkpoint *= 2;
    }
  }
  return bounded(iterations);
}

export function buildReference(view: ExactView, bits = precisionBits(view.span)): ReferenceOrbit {
  const unit = 1n << BigInt(bits);
  const centerRe = decimalToFixed(view.center.re, bits),
    centerIm = decimalToFixed(view.center.im, bits);
  const juliaRe = decimalToFixed(view.julia.re, bits),
    juliaIm = decimalToFixed(view.julia.im, bits);
  const cr = view.family === 'mandelbrot' ? centerRe : juliaRe;
  const ci = view.family === 'mandelbrot' ? centerIm : juliaIm;
  let zr = view.family === 'mandelbrot' ? 0n : centerRe;
  let zi = view.family === 'mandelbrot' ? 0n : centerIm;
  const re = new Float64Array(view.iterations + 1),
    im = new Float64Array(view.iterations + 1);
  re[0] = fixedToNumber(zr, bits);
  im[0] = fixedToNumber(zi, bits);
  let length = 1;
  const escapeRadius = radius(view);
  const limit = BigInt(Math.ceil(escapeRadius * escapeRadius * 4)) * unit * unit;
  for (let n = 1; n <= view.iterations; n++) {
    const nr = roundDivide(zr * zr - zi * zi, unit) + cr;
    zi = roundDivide(2n * zr * zi, unit) + ci;
    zr = nr;
    re[n] = fixedToNumber(zr, bits);
    im[n] = fixedToNumber(zi, bits);
    length++;
    if (zr * zr + zi * zi > limit) break;
  }
  return {
    re,
    im,
    length,
    bits,
    centerRe,
    centerIm,
    span: decimalToFixed(view.span, bits),
    juliaRe,
    juliaIm,
  };
}

/** Pixel centers are formed as exact rational offsets before the BigInt recurrence. */
export function fixedPixel(
  reference: ReferenceOrbit,
  x: number,
  y: number,
  width: number,
  height: number,
): [bigint, bigint] {
  const divisor = BigInt(2 * height);
  return [
    reference.centerRe + roundDivide(reference.span * BigInt(2 * x + 1 - width), divisor),
    reference.centerIm + roundDivide(reference.span * BigInt(height - 2 * y - 1), divisor),
  ];
}

export function prepareKernel(
  input: ExactView,
  forceMode?: 'float64' | 'perturbation',
): PreparedKernel {
  const view = validateExactView(input);
  const mode = forceMode ?? (Number(view.span) < 1e-8 ? 'perturbation' : 'float64');
  const bits = mode === 'perturbation' ? precisionBits(view.span) : 53;
  const scale = Number(view.span),
    centerRe = Number(view.center.re),
    centerIm = Number(view.center.im);
  const juliaRe = Number(view.julia.re),
    juliaIm = Number(view.julia.im),
    escapeRadius = radius(view);
  const reference = mode === 'perturbation' ? buildReference(view, bits) : undefined;
  const limit = escapeRadius * escapeRadius;

  function repair(x: number, y: number, width: number, height: number) {
    const ref = reference!;
    const [pr, pi] = fixedPixel(ref, x, y, width, height);
    return view.family === 'mandelbrot'
      ? fixedEscape(pr, pi, 0n, 0n, bits, view.iterations, escapeRadius)
      : fixedEscape(ref.juliaRe, ref.juliaIm, pr, pi, bits, view.iterations, escapeRadius);
  }
  function sample(x: number, y: number, width: number, height: number): EscapeSample {
    const offsetRe = (scale * (2 * x + 1 - width)) / (2 * height);
    const offsetIm = (scale * (height - 2 * y - 1)) / (2 * height);
    if (!reference) {
      const pr = centerRe + offsetRe,
        pi = centerIm + offsetIm;
      if (view.family === 'mandelbrot') {
        // Strict margins avoid declaring a rounded boundary point interior.
        const q = (pr - 0.25) ** 2 + pi * pi;
        if (
          q * (q + pr - 0.25) < 0.25 * pi * pi - 1e-15 ||
          (pr + 1) ** 2 + pi * pi < 0.0625 - 1e-15
        )
          return bounded(view.iterations);
        return floatEscape(pr, pi, 0, 0, view.iterations, escapeRadius);
      }
      return floatEscape(juliaRe, juliaIm, pr, pi, view.iterations, escapeRadius);
    }
    let dr = view.family === 'julia' ? offsetRe : 0;
    let di = view.family === 'julia' ? offsetIm : 0;
    const dcr = view.family === 'mandelbrot' ? offsetRe : 0;
    const dci = view.family === 'mandelbrot' ? offsetIm : 0;
    let m = 0;
    if (
      view.family === 'julia' &&
      (reference.re[0] + dr) ** 2 + (reference.im[0] + di) ** 2 > limit
    )
      return escaped(0, reference.re[0] + dr, reference.im[0] + di);
    for (let n = 1; n <= view.iterations; n++) {
      if (m + 1 >= reference.length) return repair(x, y, width, height);
      const rr = reference.re[m],
        ri = reference.im[m];
      const nr = 2 * (rr * dr - ri * di) + dr * dr - di * di + dcr;
      di = 2 * (rr * di + ri * dr) + 2 * dr * di + dci;
      dr = nr;
      m++;
      const r = reference.re[m] + dr,
        i = reference.im[m] + di;
      const magnitude = r * r + i * i;
      const referenceMagnitude = reference.re[m] ** 2 + reference.im[m] ** 2;
      // Pauldelbrot's criterion is a numerical warning, not an error enclosure.
      if (
        !Number.isFinite(magnitude) ||
        (referenceMagnitude > 0 && magnitude < 1e-7 * referenceMagnitude)
      )
        return repair(x, y, width, height);
      if (magnitude > limit) return escaped(n, r, i);
      // Mandelbrot has its critical point at zero; rebasing keeps deltas small.
      // Julia reference orbits start at the viewport center and cannot use this reset.
      if (
        view.family === 'mandelbrot' &&
        (magnitude < dr * dr + di * di || m + 1 >= reference.length)
      ) {
        dr = r;
        di = i;
        m = 0;
      }
    }
    return bounded(view.iterations);
  }
  return { view, bits, mode, reference, sample };
}
