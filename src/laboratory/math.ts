/** Numerical instruments for z -> z² + c. These are floating-point diagnostics, not certificates. */
export interface Complex {
  re: number;
  im: number;
}
export interface OrbitSample extends Complex {
  index: number;
}
export type OrbitDisposition = 'escaped' | 'attracting-candidate' | 'unresolved';
export interface OrbitAnalysis {
  parameter: Complex;
  disposition: OrbitDisposition;
  iterations: number;
  budget: number;
  escapeIteration: number | null;
  period: number | null;
  residual: number | null;
  multiplier: Complex | null;
  multiplierModulus: number | null;
  finiteLyapunov: number | null;
  orbit: OrbitSample[];
  cycle: Complex[];
}
export interface ScanSettings {
  reMin: number;
  reMax: number;
  imMin: number;
  imMax: number;
  resolution: number;
  iterations: number;
  maxPeriod: number;
}
export interface DiscoveryCandidate {
  id: string;
  period: number;
  center: Complex;
  seed: Complex;
  residual: number;
  multiplierModulus: number;
  refined: boolean;
}
export interface ComparisonRegion {
  re: string;
  im: string;
  span: string;
}
export interface ComparisonSettings {
  a: ComparisonRegion;
  b: ComparisonRegion;
  resolution: number;
  iterations: number;
  align: boolean;
}
export type Alignment =
  | 'identity'
  | 'quarter-turn'
  | 'half-turn'
  | 'three-quarter-turn'
  | 'reflect-horizontal'
  | 'reflect-vertical';
export interface ComparisonMetrics {
  alignment: Alignment;
  meanAbsoluteDifference: number;
  correlation: number | null;
  finiteNonescapeJaccard: number | null;
  finiteNonescapeA: number;
  finiteNonescapeB: number;
  samples: number;
}

const finite = (v: number) => Number.isFinite(v);
const magnitude = (v: Complex) => Math.hypot(v.re, v.im);
function next(z: Complex, c: Complex): Complex {
  return { re: z.re * z.re - z.im * z.im + c.re, im: 2 * z.re * z.im + c.im };
}

export function validateScanSettings(input: unknown): ScanSettings {
  if (!input || typeof input !== 'object') throw new Error('Experiment settings are missing.');
  const s = input as ScanSettings;
  if (![s.reMin, s.reMax, s.imMin, s.imMax].every(finite))
    throw new Error('Enter finite coordinates for all four bounds.');
  if (s.reMin >= s.reMax || s.imMin >= s.imMax)
    throw new Error('Each lower bound must be smaller than its upper bound.');
  if ([s.reMin, s.reMax, s.imMin, s.imMax].some((v) => Math.abs(v) > 4))
    throw new Error('Keep parameter bounds between −4 and 4.');
  if (!Number.isInteger(s.resolution) || s.resolution < 16 || s.resolution > 192)
    throw new Error('Choose a grid between 16 and 192 samples per side.');
  if (!Number.isInteger(s.iterations) || s.iterations < 128 || s.iterations > 8192)
    throw new Error('Choose an iteration budget between 128 and 8,192.');
  if (
    !Number.isInteger(s.maxPeriod) ||
    s.maxPeriod < 1 ||
    s.maxPeriod > 64 ||
    s.iterations < s.maxPeriod * 4
  )
    throw new Error('Choose a maximum period up to 64 and at least four times as many iterations.');
  const spacing = Math.min(s.reMax - s.reMin, s.imMax - s.imMin) / s.resolution;
  if (
    spacing <
    Number.EPSILON *
      32 *
      Math.max(1, Math.abs(s.reMin), Math.abs(s.reMax), Math.abs(s.imMin), Math.abs(s.imMax))
  )
    throw new Error(
      'This window is too small for this float64 experiment. Use the precision explorer.',
    );
  return {
    reMin: s.reMin,
    reMax: s.reMax,
    imMin: s.imMin,
    imMax: s.imMax,
    resolution: s.resolution,
    iterations: s.iterations,
    maxPeriod: s.maxPeriod,
  };
}

/** Requires three observed returns and a strictly attracting numerical multiplier. */
export function analyzeOrbit(
  parameter: Complex,
  budget = 2048,
  maxPeriod = 64,
  tolerance = 1e-9,
  keepOrbit = true,
): OrbitAnalysis {
  if (![parameter.re, parameter.im].every(finite) || magnitude(parameter) > 16)
    throw new Error('Enter a finite parameter with magnitude at most 16.');
  if (!Number.isInteger(budget) || budget < 128 || budget > 32768)
    throw new Error('Choose 128–32,768 iterations.');
  if (
    !Number.isInteger(maxPeriod) ||
    maxPeriod < 1 ||
    maxPeriod > 64 ||
    !finite(tolerance) ||
    tolerance <= 0
  )
    throw new Error('Invalid return test settings.');
  const tailLength = maxPeriod * 4 + 1;
  const tail: Complex[] = new Array(tailLength);
  const first: OrbitSample[] = [{ index: 0, re: 0, im: 0 }];
  let z: Complex = { re: 0, im: 0 },
    escapeIteration: number | null = null,
    performed = 0;
  const ending: OrbitSample[] = [];
  for (let n = 1; n <= budget; n++) {
    z = next(z, parameter);
    performed = n;
    tail[n % tailLength] = z;
    if (keepOrbit && n <= 128) first.push({ ...z, index: n });
    if (keepOrbit && n > budget - 128) ending.push({ ...z, index: n });
    if (z.re * z.re + z.im * z.im > 4) {
      escapeIteration = n;
      break;
    }
  }
  let period: number | null = null,
    residual: number | null = null,
    multiplier: Complex | null = null,
    cycle: Complex[] = [];
  if (escapeIteration === null && performed >= tailLength) {
    for (let p = 1; p <= maxPeriod; p++) {
      let error = 0;
      for (let j = 0; j < p * 3; j++) {
        const a = tail[(performed - j) % tailLength],
          b = tail[(performed - j - p) % tailLength];
        error = Math.max(error, Math.hypot(a.re - b.re, a.im - b.im));
      }
      if (error > tolerance) continue;
      let m: Complex = { re: 1, im: 0 };
      const found: Complex[] = [];
      for (let j = 0; j < p; j++) {
        const a = tail[(performed - p + 1 + j) % tailLength];
        found.push(a);
        m = { re: 2 * (m.re * a.re - m.im * a.im), im: 2 * (m.re * a.im + m.im * a.re) };
      }
      if (magnitude(m) < 1 - 1e-7) {
        period = p;
        residual = error;
        multiplier = m;
        cycle = found;
        break;
      }
    }
  }
  let finiteLyapunov: number | null = null;
  if (escapeIteration === null && performed >= tailLength) {
    let sum = 0;
    for (let j = 0; j < Math.min(128, tailLength - 1); j++)
      sum += Math.log(2 * magnitude(tail[(performed - j) % tailLength]));
    const value = sum / Math.min(128, tailLength - 1);
    finiteLyapunov = Number.isFinite(value) ? value : null;
  }
  return {
    parameter,
    disposition:
      escapeIteration !== null
        ? 'escaped'
        : period !== null
          ? 'attracting-candidate'
          : 'unresolved',
    iterations: performed,
    budget,
    escapeIteration,
    period,
    residual,
    multiplier,
    multiplierModulus: multiplier ? magnitude(multiplier) : null,
    finiteLyapunov,
    orbit: keepOrbit ? [...first, ...ending.filter((p) => p.index > 128)] : [],
    cycle,
  };
}

/** Newton iteration on f_c^p(0)=0; a small residual is numerical evidence only. */
export function refineCenter(
  seed: Complex,
  period: number,
  bounds?: ScanSettings,
): { center: Complex; residual: number; refined: boolean } {
  if (!Number.isInteger(period) || period < 1 || period > 64)
    throw new Error('Unsupported period.');
  let c = { ...seed },
    error = Infinity;
  for (let step = 0; step < 32; step++) {
    let z: Complex = { re: 0, im: 0 },
      d: Complex = { re: 0, im: 0 };
    for (let n = 0; n < period; n++) {
      d = { re: 2 * (z.re * d.re - z.im * d.im) + 1, im: 2 * (z.re * d.im + z.im * d.re) };
      z = next(z, c);
    }
    error = magnitude(z);
    if (!finite(error)) break;
    if (error < 1e-13) {
      // Reject a lower-period root reached by Newton's method.
      let q: Complex = { re: 0, im: 0 };
      for (let n = 1; n < period; n++) {
        q = next(q, c);
        if (period % n === 0 && magnitude(q) < 1e-8)
          return { center: seed, residual: error, refined: false };
      }
      if (
        bounds &&
        (c.re < bounds.reMin || c.re > bounds.reMax || c.im < bounds.imMin || c.im > bounds.imMax)
      )
        return { center: seed, residual: error, refined: false };
      return { center: c, residual: error, refined: true };
    }
    const norm = d.re * d.re + d.im * d.im;
    if (!finite(norm) || norm < 1e-24) break;
    const dr = (z.re * d.re + z.im * d.im) / norm,
      di = (z.im * d.re - z.re * d.im) / norm;
    if (Math.hypot(dr, di) > 0.5 || !finite(dr) || !finite(di)) break;
    c = { re: c.re - dr, im: c.im - di };
    if (magnitude(c) > 3) break;
  }
  return { center: seed, residual: finite(error) ? error : 1e99, refined: false };
}

export function sampleParameter(s: ScanSettings, x: number, y: number): Complex {
  return {
    re: s.reMin + ((x + 0.5) / s.resolution) * (s.reMax - s.reMin),
    im: s.imMax - ((y + 0.5) / s.resolution) * (s.imMax - s.imMin),
  };
}

export function validateComparisonSettings(input: unknown): ComparisonSettings {
  if (!input || typeof input !== 'object') throw new Error('Comparison settings are missing.');
  const s = input as ComparisonSettings;
  if (!Number.isInteger(s.resolution) || s.resolution < 32 || s.resolution > 192)
    throw new Error('Choose 32–192 samples per side.');
  if (!Number.isInteger(s.iterations) || s.iterations < 64 || s.iterations > 4096)
    throw new Error('Choose 64–4,096 iterations.');
  for (const region of [s.a, s.b]) {
    if (
      !region ||
      !['re', 'im', 'span'].every(
        (k) =>
          typeof region[k as keyof ComparisonRegion] === 'string' &&
          region[k as keyof ComparisonRegion].trim() !== '',
      )
    )
      throw new Error('Enter all six coordinates and spans.');
    const re = Number(region.re),
      im = Number(region.im),
      span = Number(region.span);
    if (![re, im, span].every(finite) || span <= 0 || span > 8 || Math.hypot(re, im) > 4)
      throw new Error('Use finite centers within radius 4 and a positive span no larger than 8.');
    if (span / s.resolution < Number.EPSILON * 32 * Math.max(1, Math.abs(re), Math.abs(im)))
      throw new Error(
        'These pixels exceed this instrument’s float64 precision. Enlarge the span or use the precision explorer.',
      );
  }
  return {
    a: { ...s.a },
    b: { ...s.b },
    resolution: s.resolution,
    iterations: s.iterations,
    align: !!s.align,
  };
}

/** A common log-normalized escape field; 1 denotes finite non-escape. */
export function escapeSample(re: number, im: number, iterations: number): number {
  let zr = 0,
    zi = 0;
  for (let n = 0; n < iterations; n++) {
    const nextRe = zr * zr - zi * zi + re;
    zi = 2 * zr * zi + im;
    zr = nextRe;
    const r2 = zr * zr + zi * zi;
    if (r2 > 4) {
      const smooth = Math.max(1, n + 2 - Math.log2(Math.log2(Math.sqrt(r2))));
      return Math.min(0.99999, Math.log1p(smooth) / Math.log1p(iterations + 1));
    }
  }
  return 1;
}

export function regionRow(
  region: ComparisonRegion,
  resolution: number,
  iterations: number,
  y: number,
  into: Float32Array,
): void {
  const re = Number(region.re),
    im = Number(region.im),
    span = Number(region.span);
  for (let x = 0; x < resolution; x++)
    into[y * resolution + x] = escapeSample(
      re + ((x + 0.5) / resolution - 0.5) * span,
      im + (0.5 - (y + 0.5) / resolution) * span,
      iterations,
    );
}

export function alignedIndex(x: number, y: number, n: number, alignment: Alignment): number {
  switch (alignment) {
    case 'quarter-turn':
      return (n - 1 - x) * n + y;
    case 'half-turn':
      return (n - 1 - y) * n + n - 1 - x;
    case 'three-quarter-turn':
      return x * n + n - 1 - y;
    case 'reflect-horizontal':
      return y * n + n - 1 - x;
    case 'reflect-vertical':
      return (n - 1 - y) * n + x;
    default:
      return y * n + x;
  }
}

export function compareFields(
  a: Float32Array,
  b: Float32Array,
  resolution: number,
  align: boolean,
): ComparisonMetrics {
  if (a.length !== resolution * resolution || b.length !== a.length)
    throw new Error('Comparison field dimensions do not agree.');
  const choices: Alignment[] = align
    ? [
        'identity',
        'quarter-turn',
        'half-turn',
        'three-quarter-turn',
        'reflect-horizontal',
        'reflect-vertical',
      ]
    : ['identity'];
  let best: ComparisonMetrics | null = null;
  for (const alignment of choices) {
    let abs = 0,
      sa = 0,
      sb = 0,
      saa = 0,
      sbb = 0,
      sab = 0,
      insideA = 0,
      insideB = 0,
      intersection = 0,
      union = 0;
    for (let y = 0; y < resolution; y++)
      for (let x = 0; x < resolution; x++) {
        const va = a[y * resolution + x],
          vb = b[alignedIndex(x, y, resolution, alignment)];
        if (!finite(va) || !finite(vb))
          throw new Error('Comparison fields contain non-finite samples.');
        abs += Math.abs(va - vb);
        sa += va;
        sb += vb;
        saa += va * va;
        sbb += vb * vb;
        sab += va * vb;
        const ia = va === 1,
          ib = vb === 1;
        insideA += +ia;
        insideB += +ib;
        intersection += +(ia && ib);
        union += +(ia || ib);
      }
    const n = a.length,
      denominator = Math.sqrt(Math.max(0, (n * saa - sa * sa) * (n * sbb - sb * sb)));
    const value: ComparisonMetrics = {
      alignment,
      meanAbsoluteDifference: abs / n,
      correlation:
        denominator > 1e-12 ? Math.min(1, Math.max(-1, (n * sab - sa * sb) / denominator)) : null,
      finiteNonescapeJaccard: union > 0 ? intersection / union : null,
      finiteNonescapeA: insideA / n,
      finiteNonescapeB: insideB / n,
      samples: n,
    };
    if (!best || value.meanAbsoluteDifference < best.meanAbsoluteDifference) best = value;
  }
  return best!;
}

export function sampleColor(
  disposition: OrbitDisposition,
  period: number | null,
  escapeIteration: number | null,
  budget: number,
): [number, number, number] {
  if (disposition === 'unresolved') return [78, 77, 70];
  if (disposition === 'escaped') {
    const v = Math.min(1, Math.log1p(escapeIteration ?? 0) / Math.log1p(budget));
    return [12 + v * 30, 12 + v * 29, 11 + v * 27].map(Math.round) as [number, number, number];
  }
  const palette = [
    [117, 199, 183],
    [137, 177, 236],
    [230, 187, 126],
    [191, 151, 227],
    [225, 138, 151],
    [142, 207, 222],
    [175, 202, 127],
  ];
  return palette[((period ?? 1) - 1) % palette.length] as [number, number, number];
}
