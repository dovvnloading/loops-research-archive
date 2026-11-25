/** Exact angle arithmetic lives here; drawing coordinates remain numerical. */
export interface Rational { numerator: bigint; denominator: bigint }
export interface OrbitPoint { index: number; re: number; im: number; escaped: boolean }

function gcd(a: bigint, b: bigint): bigint {
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  while (b !== 0n) [a, b] = [b, a % b];
  return a;
}

export function normalizeRational(numerator: bigint, denominator: bigint): Rational {
  if (denominator === 0n) throw new RangeError('A rational denominator cannot be zero.');
  if (denominator < 0n) { numerator = -numerator; denominator = -denominator; }
  const divisor = gcd(numerator, denominator);
  return { numerator: numerator / divisor, denominator: denominator / divisor };
}

export function parseRational(value: string): Rational {
  if (!/^\s*[+-]?\d+\s*(?:\/\s*[+-]?\d+\s*)?$/.test(value)) {
    throw new TypeError('Enter an integer or rational such as 3/7.');
  }
  const [numerator, denominator = '1'] = value.split('/').map(part => part.trim());
  return normalizeRational(BigInt(numerator), BigInt(denominator));
}

export function formatRational(value: Rational): string {
  const { numerator, denominator } = normalizeRational(value.numerator, value.denominator);
  return `${numerator}/${denominator}`;
}

export function modOne(value: string | Rational): Rational {
  const parsed = typeof value === 'string' ? parseRational(value) : normalizeRational(value.numerator, value.denominator);
  return normalizeRational(((parsed.numerator % parsed.denominator) + parsed.denominator) % parsed.denominator, parsed.denominator);
}

/** The map theta -> 2^iterations theta (mod 1), evaluated with BigInt only. */
export function doubleAngle(value: string | Rational, iterations = 1): string {
  if (!Number.isSafeInteger(iterations) || iterations < 0 || iterations > 10000) {
    throw new RangeError('Choose between 0 and 10,000 angle doublings.');
  }
  const angle = modOne(value);
  return formatRational(normalizeRational((angle.numerator * (1n << BigInt(iterations))) % angle.denominator, angle.denominator));
}

/** Includes the initial angle; repeated values are retained to expose collisions. */
export function angleOrbit(value: string, length: number): string[] {
  if (!Number.isSafeInteger(length) || length < 0 || length > 10000) throw new RangeError('Invalid orbit length.');
  const result: string[] = [];
  let current = formatRational(modOne(value));
  for (let index = 0; index < length; index++) {
    result.push(current);
    current = doubleAngle(current);
  }
  return result;
}

/** Display approximation only. Never use the result in a certificate. */
export function rationalToNumber(value: string | Rational): number {
  const parsed = typeof value === 'string' ? parseRational(value) : normalizeRational(value.numerator, value.denominator);
  const direct = Number(parsed.numerator) / Number(parsed.denominator);
  if (Number.isFinite(direct)) return direct;
  const sign = parsed.numerator < 0n ? -1 : 1;
  const n = (parsed.numerator < 0n ? -parsed.numerator : parsed.numerator).toString();
  const d = parsed.denominator.toString();
  return sign * Number(n.slice(0, 16)) / Number(d.slice(0, 16)) * 10 ** ((n.length - Math.min(16, n.length)) - (d.length - Math.min(16, d.length)));
}

/** Exact eventual binary expansion with an explicit bound on exploratory output. */
export function periodicBinary(value: string | Rational, maxDigits = 128): {prefix: string; period: string; truncated: boolean} {
  if (!Number.isSafeInteger(maxDigits) || maxDigits < 1 || maxDigits > 10000) throw new RangeError('Invalid binary digit limit.');
  const { numerator, denominator } = modOne(value);
  let remainder = numerator;
  let digits = '';
  const seen = new Map<bigint, number>();
  while (remainder !== 0n && !seen.has(remainder) && digits.length < maxDigits) {
    seen.set(remainder, digits.length);
    remainder *= 2n;
    digits += remainder >= denominator ? '1' : '0';
    remainder %= denominator;
  }
  const start = seen.get(remainder);
  if (start !== undefined) return { prefix: digits.slice(0, start), period: digits.slice(start), truncated: false };
  return { prefix: digits, period: '', truncated: remainder !== 0n };
}

/** Numerical z -> z² + c critical orbit. A finite non-escape is not a proof. */
export function criticalOrbit(c: [number, number], maxIterations = 128, bailout = 2): OrbitPoint[] {
  if (!c.every(Number.isFinite) || !Number.isFinite(bailout) || bailout < 2) throw new RangeError('Finite c and bailout ≥ 2 are required.');
  if (!Number.isSafeInteger(maxIterations) || maxIterations < 0 || maxIterations > 20000) throw new RangeError('Invalid iteration count.');
  const result: OrbitPoint[] = [{ index: 0, re: 0, im: 0, escaped: false }];
  let re = 0, im = 0;
  for (let index = 1; index <= maxIterations; index++) {
    [re, im] = [re * re - im * im + c[0], 2 * re * im + c[1]];
    const escaped = re * re + im * im > bailout * bailout;
    result.push({ index, re, im, escaped });
    if (escaped) break;
  }
  return result;
}
