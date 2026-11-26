import type { ExactComplex, ExactView, PrecisionPalette } from './types.ts';

export const MIN_SPAN = '1e-200';
export const MAX_SPAN = '32';
export const DEFAULT_EXACT_VIEW: ExactView = {
  family: 'mandelbrot',
  center: { re: '-0.5', im: '0' },
  span: '3.2',
  julia: { re: '-0.74543', im: '0.11301' },
  iterations: 768,
  palette: 'glacier',
};
interface Decimal {
  coefficient: bigint;
  exponent: number;
}
const DECIMAL = /^([+-]?)(?:(\d+)(?:\.(\d*))?|\.(\d+))(?:e([+-]?\d+))?$/i;

function parse(value: string): Decimal {
  if (typeof value !== 'string' || value.length > 1200)
    throw new Error('Use a decimal coordinate of at most 1,200 characters.');
  const match = value.trim().match(DECIMAL);
  if (!match) throw new Error('Enter a decimal number, for example -0.7436 or 1e-30.');
  const fraction = match[3] ?? match[4] ?? '';
  const exponent = Number(match[5] ?? 0) - fraction.length;
  if (!Number.isSafeInteger(exponent) || exponent < -1200 || exponent > 100)
    throw new Error('Decimal exponent is outside the supported range.');
  let coefficient = BigInt(`${match[1] === '-' ? '-' : ''}${match[2] ?? '0'}${fraction}`);
  if (coefficient === 0n) return { coefficient: 0n, exponent: 0 };
  let normalizedExponent = exponent;
  while (coefficient % 10n === 0n) {
    coefficient /= 10n;
    normalizedExponent++;
  }
  return { coefficient, exponent: normalizedExponent };
}
function pow10(n: number) {
  return 10n ** BigInt(n);
}
function format({ coefficient, exponent }: Decimal): string {
  if (!coefficient) return '0';
  const sign = coefficient < 0n ? '-' : '';
  let digits = (coefficient < 0n ? -coefficient : coefficient).toString();
  if (exponent >= 0) return sign + digits + '0'.repeat(exponent);
  const place = digits.length + exponent;
  if (place > 0) return sign + digits.slice(0, place) + '.' + digits.slice(place);
  return sign + '0.' + '0'.repeat(-place) + digits;
}
export function normalizeDecimal(value: string): string {
  return format(parse(value));
}
export function decimalOrder(value: string): number {
  const d = parse(value);
  return d.coefficient === 0n
    ? 0
    : (d.coefficient < 0n ? -d.coefficient : d.coefficient).toString().length - 1 + d.exponent;
}
export function roundDivide(n: bigint, d: bigint): bigint {
  if (d <= 0n) throw new Error('A positive divisor is required.');
  const sign = n < 0n ? -1n : 1n;
  const abs = n < 0n ? -n : n;
  return sign * ((abs + d / 2n) / d);
}
export function decimalToFixed(value: string, bits: number): bigint {
  const d = parse(value);
  const numerator = d.coefficient << BigInt(bits);
  return d.exponent >= 0
    ? numerator * pow10(d.exponent)
    : roundDivide(numerator, pow10(-d.exponent));
}
export function fixedToDecimal(value: bigint, bits: number, places = 240): string {
  return normalizeDecimal(
    format({
      coefficient: roundDivide(value * pow10(places), 1n << BigInt(bits)),
      exponent: -places,
    }),
  );
}
/** Convert a fixed-point value without overflowing Number for large BigInts. */
export function fixedToNumber(value: bigint, bits: number): number {
  if (!value) return 0;
  const negative = value < 0n;
  const abs = negative ? -value : value;
  const shift = Math.max(0, abs.toString(2).length - 53);
  const result = Number(abs >> BigInt(shift)) * 2 ** (shift - bits);
  return negative ? -result : result;
}
export function precisionBits(span: string): number {
  return Math.max(128, Math.ceil((Math.max(0, -decimalOrder(span)) + 36) * Math.LOG2E * Math.LN10));
}
export function validateExactView(input: unknown): ExactView {
  if (!input || typeof input !== 'object') throw new Error('An exploration view is required.');
  const v = input as Record<string, unknown>;
  if (v.family !== 'mandelbrot' && v.family !== 'julia')
    throw new Error('Choose the Mandelbrot or Julia family.');
  function complex(value: unknown, label: string): ExactComplex {
    if (!value || typeof value !== 'object')
      throw new Error(`${label} needs real and imaginary coordinates.`);
    const c = value as Record<string, unknown>;
    if (typeof c.re !== 'string' || typeof c.im !== 'string')
      throw new Error('Exact coordinates must be decimal strings.');
    const result = { re: normalizeDecimal(c.re), im: normalizeDecimal(c.im) };
    if (Math.abs(Number(result.re)) > 1e6 || Math.abs(Number(result.im)) > 1e6)
      throw new Error('Coordinates must lie between −1,000,000 and 1,000,000.');
    return result;
  }
  const center = complex(v.center, 'The center');
  const julia = complex(v.julia, 'The Julia parameter');
  if (typeof v.span !== 'string') throw new Error('The span must be a decimal string.');
  const span = normalizeDecimal(v.span);
  if (!(Number(span) >= 1e-200 && Number(span) <= 32))
    throw new Error('The vertical span must be between 1e-200 and 32.');
  if (
    typeof v.iterations !== 'number' ||
    !Number.isInteger(v.iterations) ||
    v.iterations < 64 ||
    v.iterations > 20000
  )
    throw new Error('Choose an iteration budget from 64 to 20,000.');
  const palettes: PrecisionPalette[] = ['glacier', 'ember', 'violet', 'mono', 'aurora'];
  if (!palettes.includes(v.palette as PrecisionPalette)) throw new Error('Unknown color palette.');
  return {
    family: v.family,
    center,
    span,
    julia,
    iterations: v.iterations,
    palette: v.palette as PrecisionPalette,
  };
}
function decimalMultiply(a: string, b: string, significant = 18): string {
  const da = parse(a),
    db = parse(b);
  let coefficient = da.coefficient * db.coefficient;
  let exponent = da.exponent + db.exponent;
  const length = (coefficient < 0n ? -coefficient : coefficient).toString().length;
  if (length > significant) {
    coefficient = roundDivide(coefficient, pow10(length - significant));
    exponent += length - significant;
  }
  return normalizeDecimal(format({ coefficient, exponent }));
}
/** x and y are normalized screen coordinates: top-left (0,0), bottom-right (1,1). */
export function pointAtPixel(view: ExactView, x: number, y: number, aspect = 1): ExactComplex {
  if (![x, y, aspect].every(Number.isFinite) || aspect <= 0)
    throw new Error('Invalid viewport coordinates.');
  const bits = precisionBits(view.span);
  const unit = 1n << BigInt(bits);
  const span = decimalToFixed(view.span, bits);
  const offsetX = decimalToFixed(String((x - 0.5) * aspect), bits);
  const offsetY = decimalToFixed(String(0.5 - y), bits);
  const places = Math.max(36, -decimalOrder(view.span) + 36);
  return {
    re: fixedToDecimal(
      decimalToFixed(view.center.re, bits) + roundDivide(span * offsetX, unit),
      bits,
      places,
    ),
    im: fixedToDecimal(
      decimalToFixed(view.center.im, bits) + roundDivide(span * offsetY, unit),
      bits,
      places,
    ),
  };
}
/** Positive multiplier zooms out; 0.5 means magnify twice, keeping the anchor fixed. */
export function zoomExactView(
  view: ExactView,
  multiplier: number,
  x = 0.5,
  y = 0.5,
  aspect = 1,
): ExactView {
  if (!Number.isFinite(multiplier) || multiplier <= 0) return view;
  let span = decimalMultiply(view.span, String(multiplier));
  if (Number(span) < 1e-200) span = normalizeDecimal(MIN_SPAN);
  if (Number(span) > 32) span = MAX_SPAN;
  if (span === view.span) return view;
  const anchor = pointAtPixel(view, x, y, aspect);
  const next = { ...view, span };
  const displacedAnchor = pointAtPixel({ ...next, center: { re: '0', im: '0' } }, x, y, aspect);
  const bits = Math.max(precisionBits(span), precisionBits(view.span));
  const places = Math.max(36, -decimalOrder(span) + 36);
  return {
    ...next,
    center: {
      re: fixedToDecimal(
        decimalToFixed(anchor.re, bits) - decimalToFixed(displacedAnchor.re, bits),
        bits,
        places,
      ),
      im: fixedToDecimal(
        decimalToFixed(anchor.im, bits) - decimalToFixed(displacedAnchor.im, bits),
        bits,
        places,
      ),
    },
  };
}
/** Pan distances are fractions of viewport height; drag right moves the world right. */
export function panExactView(view: ExactView, dx: number, dy: number): ExactView {
  return { ...view, center: pointAtPixel(view, 0.5 - dx, 0.5 - dy) };
}
export function exactViewFromEngine(state: {
  scene: string;
  center: [number, number];
  scale: number;
  julia: [number, number];
  iterations: number;
  palette: string;
}): ExactView {
  return validateExactView({
    family: state.scene === 'julia' ? 'julia' : 'mandelbrot',
    center: { re: String(state.center[0]), im: String(state.center[1]) },
    span: String(Math.max(1e-200, Math.min(32, state.scale))),
    julia: { re: String(state.julia[0]), im: String(state.julia[1]) },
    iterations: Math.max(64, Math.min(20000, Math.round(state.iterations))),
    palette: state.palette,
  });
}
export function viewDepth(view: ExactView): number {
  return Math.max(0, -decimalOrder(view.span));
}
