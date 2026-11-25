/**
 * Rounded fixed-point exploration, deliberately separate from exact certificates.
 * Decimal coordinates never pass through Number. Floating-point values are used
 * only for input limits, timing, and the final color of an escaped pixel.
 */
export interface PrecisionSettings {
  centerRe: string;
  centerIm: string;
  zoomExponent: number;
  iterations: number;
  width: number;
}

export interface PrecisionFrame extends PrecisionSettings {
  height: number;
  bits: number;
  decimalDigits: number;
  centerDigits: [number, number];
  unit: bigint;
  re: bigint;
  im: bigint;
  planeWidth: bigint;
}

export interface PrecisionPixel { escaped: boolean; iteration: number; magnitudeSquared: bigint }
export type PrecisionRequest = { type: 'render'; id: number; settings: PrecisionSettings };
export type PrecisionMessage =
  | { type: 'strip'; id: number; y: number; rows: number; width: number; height: number; bits: number; elapsedMs: number; buffer: ArrayBuffer }
  | { type: 'complete'; id: number; elapsedMs: number; escapedPixels: number; totalPixels: number; bits: number }
  | { type: 'error'; id: number; message: string };

const ITERATIONS = [128, 256, 512, 1024, 2048];
const WIDTHS = [128, 192, 256];

export function precisionBits(zoomExponent: number): number {
  if (!Number.isSafeInteger(zoomExponent) || zoomExponent < 0 || zoomExponent > 60) {
    throw new RangeError('The zoom exponent must be an integer from 0 to 60.');
  }
  return Math.min(512, Math.max(128, Math.ceil((zoomExponent + 20) * Math.log2(10))));
}

/** Nearest integer division; exact ties round away from zero. */
export function roundDivide(numerator: bigint, denominator: bigint): bigint {
  if (denominator <= 0n) throw new RangeError('A positive denominator is required.');
  return numerator < 0n ? -((-numerator + denominator / 2n) / denominator) : (numerator + denominator / 2n) / denominator;
}

function decimalParts(value: string): { numerator: bigint; denominator: bigint; digits: number } {
  if (typeof value !== 'string' || value.length > 112) throw new RangeError('Use a decimal coordinate of at most 112 characters.');
  const cleaned = value.trim();
  if (!/^[+-]?(?:\d+(?:\.\d*)?|\.\d+)$/.test(cleaned)) {
    throw new TypeError('Use plain decimal coordinates, for example -0.743643887037151. Scientific notation is not accepted.');
  }
  const negative = cleaned.startsWith('-');
  const unsigned = cleaned.replace(/^[+-]/, '');
  const [whole = '0', fractional = ''] = unsigned.split('.');
  if (fractional.length > 100) throw new RangeError('Use at most 100 fractional decimal digits.');
  const numerator = BigInt((whole || '0') + fractional) * (negative ? -1n : 1n);
  const denominator = 10n ** BigInt(fractional.length);
  if (numerator > 4n * denominator || numerator < -4n * denominator) {
    throw new RangeError('Each coordinate must lie between -4 and 4.');
  }
  return { numerator, denominator, digits: fractional.length };
}

/** Parse exactly as a decimal rational, then round once to the fixed-point grid. */
export function decimalToFixed(value: string, bits: number): bigint {
  if (!Number.isSafeInteger(bits) || bits < 32 || bits > 512) throw new RangeError('Fixed-point precision must be 32–512 bits.');
  const parsed = decimalParts(value);
  return roundDivide(parsed.numerator * (1n << BigInt(bits)), parsed.denominator);
}

export function preparePrecisionFrame(input: PrecisionSettings): PrecisionFrame {
  const bits = precisionBits(input.zoomExponent);
  if (!ITERATIONS.includes(input.iterations)) throw new RangeError('Choose 128, 256, 512, 1024, or 2048 iterations.');
  if (!WIDTHS.includes(input.width)) throw new RangeError('Choose a render width of 128, 192, or 256 pixels.');
  const real = decimalParts(input.centerRe);
  const imaginary = decimalParts(input.centerIm);
  const unit = 1n << BigInt(bits);
  return {
    ...input,
    centerRe: input.centerRe.trim(), centerIm: input.centerIm.trim(),
    height: input.width * 3 / 4, bits, decimalDigits: Math.floor(bits * Math.log10(2)),
    centerDigits: [real.digits, imaginary.digits], unit,
    re: roundDivide(real.numerator * unit, real.denominator),
    im: roundDivide(imaginary.numerator * unit, imaginary.denominator),
    planeWidth: roundDivide(unit, 10n ** BigInt(input.zoomExponent)),
  };
}

/** Pixel centers, with imaginary coordinates increasing toward the top. */
export function precisionCoordinate(frame: PrecisionFrame, x: number, y: number): [bigint, bigint] {
  if (!Number.isSafeInteger(x) || !Number.isSafeInteger(y) || x < 0 || y < 0 || x >= frame.width || y >= frame.height) {
    throw new RangeError('Pixel coordinates are outside this render.');
  }
  const divisor = BigInt(2 * frame.width);
  return [
    frame.re + roundDivide(frame.planeWidth * BigInt(2 * x + 1 - frame.width), divisor),
    frame.im - roundDivide(frame.planeWidth * BigInt(2 * y + 1 - frame.height), divisor),
  ];
}

/** Finite rounded recurrence. Non-escape at the budget is not set membership. */
export function fixedMandelbrot(cr: bigint, ci: bigint, bits: number, iterations: number): PrecisionPixel {
  if (!Number.isSafeInteger(bits) || bits < 32 || bits > 512) throw new RangeError('Invalid arithmetic precision.');
  if (!Number.isSafeInteger(iterations) || iterations < 1 || iterations > 2048) throw new RangeError('Invalid iteration budget.');
  const shift = BigInt(bits);
  const half = 1n << BigInt(bits - 1);
  const bailout = 4n << shift;
  let re = 0n, im = 0n, re2 = 0n, im2 = 0n;
  let checkRe = 0n, checkIm = 0n;
  for (let index = 1; index <= iterations; index++) {
    const product = 2n * re * im;
    im = (product < 0n ? -((-product + half) >> shift) : (product + half) >> shift) + ci;
    re = re2 - im2 + cr;
    re2 = (re * re + half) >> shift;
    im2 = (im * im + half) >> shift;
    const magnitudeSquared = re2 + im2;
    if (magnitudeSquared > bailout) return { escaped: true, iteration: index, magnitudeSquared };
    // An exact repeat of the rounded machine state can safely skip the remainder
    // of this finite machine computation. It is not an analytic periodicity proof.
    if (index % 32 === 0) {
      if (re === checkRe && im === checkIm) return { escaped: false, iteration: iterations, magnitudeSquared };
      checkRe = re; checkIm = im;
    }
  }
  return { escaped: false, iteration: iterations, magnitudeSquared: re2 + im2 };
}

export function precisionColor(pixel: PrecisionPixel, unit: bigint): [number, number, number, number] {
  if (!pixel.escaped) return [5, 11, 9, 255];
  // Conversion happens after escape and affects only the display palette.
  const magnitude = Math.sqrt(Number(pixel.magnitudeSquared) / Number(unit));
  const smooth = pixel.iteration + 1 - Math.log2(Math.max(1e-9, Math.log2(magnitude)));
  const t = smooth * 0.018;
  const light = 0.55 + 0.45 * Math.cos(6.28318530718 * (t * 0.17));
  return [
    Math.round(30 + (0.5 + 0.5 * Math.cos(6.28318530718 * (t + 0.03))) * 190 * light),
    Math.round(45 + (0.5 + 0.5 * Math.cos(6.28318530718 * (t + 0.17))) * 201 * light),
    Math.round(40 + (0.5 + 0.5 * Math.cos(6.28318530718 * (t + 0.30))) * 170 * light),
    255,
  ];
}
