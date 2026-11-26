import {
  analyzeOrbit,
  compareFields,
  validateComparisonSettings,
  validateScanSettings,
} from './math.ts';
import type {
  ComparisonMetrics,
  ComparisonSettings,
  DiscoveryCandidate,
  ScanSettings,
} from './math.ts';

export type LaboratoryInstrument = 'discovery' | 'orbit' | 'comparison';
export interface LaboratoryManifest {
  schema: 'loops-laboratory-v1';
  instrument: LaboratoryInstrument;
  settings: unknown;
  result?: unknown;
  createdAt: string;
  method: 'loops-quadratic-instruments-1';
  precision: 'IEEE-754 binary64';
  claim: string;
}
export interface SurveyResult {
  processed: number;
  total: number;
  escaped: number;
  attracting: number;
  unresolved: number;
  periods: Record<string, number>;
  candidates: DiscoveryCandidate[];
  elapsed: number;
  pixels?: Uint8ClampedArray;
}
export interface ComparisonResult {
  a: Float32Array;
  b: Float32Array;
  metrics: ComparisonMetrics;
  elapsed: number;
}
export interface OrbitSettings {
  re: string;
  im: string;
  iterations: number;
  maxPeriod?: number;
  tolerance?: number;
  initial?: { re: number; im: number };
}

const object = (value: unknown): value is Record<string, unknown> =>
  !!value && typeof value === 'object' && !Array.isArray(value);
const finite = (value: unknown): value is number =>
  typeof value === 'number' && Number.isFinite(value);
const integer = (value: unknown, min: number, max: number): value is number =>
  finite(value) && Number.isInteger(value) && value >= min && value <= max;

export function encodeSurveyPixels(pixels: Uint8ClampedArray): string {
  let binary = '';
  for (let at = 0; at < pixels.length; at += 16384)
    binary += String.fromCharCode(...pixels.subarray(at, at + 16384));
  return btoa(binary);
}

export function decodeSurveyPixels(
  value: unknown,
  resolution: number,
): Uint8ClampedArray | undefined {
  if (value === undefined) return undefined;
  const expected = resolution ** 2 * 4;
  if (
    typeof value !== 'string' ||
    value.length > Math.ceil(expected / 3) * 4 ||
    !/^[A-Za-z0-9+/]*={0,2}$/.test(value)
  )
    throw new Error('The saved survey preview is invalid.');
  let binary: string;
  try {
    binary = atob(value);
  } catch {
    throw new Error('The saved survey preview could not be decoded.');
  }
  if (binary.length !== expected)
    throw new Error('The saved survey preview has the wrong dimensions.');
  return Uint8ClampedArray.from(binary, (letter) => letter.charCodeAt(0));
}

export function validateOrbitSettings(value: unknown): OrbitSettings {
  if (
    !object(value) ||
    typeof value.re !== 'string' ||
    typeof value.im !== 'string' ||
    !value.re.trim() ||
    !value.im.trim()
  )
    throw new Error('The orbit settings must include both coordinate strings.');
  if (!integer(value.iterations, 128, 32768))
    throw new Error('The saved orbit budget must be between 128 and 32,768 iterations.');
  if (value.maxPeriod !== undefined && value.maxPeriod !== 64)
    throw new Error('This orbit instrument replays a maximum period of 64.');
  if (value.tolerance !== undefined && value.tolerance !== 1e-9)
    throw new Error('This orbit instrument replays the declared 10⁻⁹ return tolerance.');
  if (
    value.initial !== undefined &&
    (!object(value.initial) || value.initial.re !== 0 || value.initial.im !== 0)
  )
    throw new Error('This instrument starts the critical orbit at z₀ = 0.');
  analyzeOrbit({ re: Number(value.re), im: Number(value.im) }, value.iterations);
  return {
    re: value.re,
    im: value.im,
    iterations: value.iterations,
    maxPeriod: 64,
    tolerance: 1e-9,
    initial: { re: 0, im: 0 },
  };
}

export function restoreSurveyResult(value: unknown, settings: ScanSettings): SurveyResult | null {
  if (value === undefined || value === null) return null;
  if (!object(value)) throw new Error('The saved survey result is malformed.');
  const total = settings.resolution ** 2;
  if (
    value.total !== total ||
    !integer(value.processed, 0, total) ||
    !integer(value.escaped, 0, total) ||
    !integer(value.attracting, 0, total) ||
    !integer(value.unresolved, 0, total) ||
    value.escaped + value.attracting + value.unresolved !== value.processed
  )
    throw new Error('The saved survey sample counts do not match its grid.');
  if (
    !finite(value.elapsed) ||
    value.elapsed < 0 ||
    !object(value.periods) ||
    !Array.isArray(value.candidates) ||
    value.candidates.length > 256
  )
    throw new Error('The saved survey catalog is malformed.');
  const periods: Record<string, number> = {};
  for (const [key, count] of Object.entries(value.periods)) {
    if (
      !/^\d+$/.test(key) ||
      !integer(Number(key), 1, settings.maxPeriod) ||
      !integer(count, 0, value.attracting)
    )
      throw new Error('The saved survey period counts are invalid.');
    periods[key] = count;
  }
  if (Object.values(periods).reduce((sum, n) => sum + n, 0) !== value.attracting)
    throw new Error('The saved survey period totals are inconsistent.');
  const candidates = value.candidates.map((candidate: unknown): DiscoveryCandidate => {
    if (
      !object(candidate) ||
      typeof candidate.id !== 'string' ||
      candidate.id.length > 200 ||
      !integer(candidate.period, 1, settings.maxPeriod) ||
      !object(candidate.center) ||
      !object(candidate.seed) ||
      !finite(candidate.center.re) ||
      !finite(candidate.center.im) ||
      !finite(candidate.seed.re) ||
      !finite(candidate.seed.im) ||
      !finite(candidate.residual) ||
      candidate.residual < 0 ||
      !finite(candidate.multiplierModulus) ||
      candidate.multiplierModulus < 0 ||
      candidate.refined !== true
    )
      throw new Error('A saved survey candidate is malformed.');
    for (const c of [candidate.center, candidate.seed])
      if (
        (c.re as number) < settings.reMin ||
        (c.re as number) > settings.reMax ||
        (c.im as number) < settings.imMin ||
        (c.im as number) > settings.imMax
      )
        throw new Error('A saved candidate lies outside the recorded survey bounds.');
    return {
      id: candidate.id,
      period: candidate.period,
      center: { re: candidate.center.re, im: candidate.center.im },
      seed: { re: candidate.seed.re, im: candidate.seed.im },
      residual: candidate.residual,
      multiplierModulus: candidate.multiplierModulus,
      refined: true,
    };
  });
  if (new Set(candidates.map((c) => c.id)).size !== candidates.length)
    throw new Error('The saved survey contains duplicate candidate identifiers.');
  return {
    processed: value.processed,
    total,
    escaped: value.escaped,
    attracting: value.attracting,
    unresolved: value.unresolved,
    periods,
    candidates,
    elapsed: value.elapsed,
    pixels: decodeSurveyPixels(value.pixelsBase64, settings.resolution),
  };
}

export function restoreComparisonResult(
  value: unknown,
  settings: ComparisonSettings,
): ComparisonResult | null {
  if (value === undefined || value === null) return null;
  if (
    !object(value) ||
    !Array.isArray(value.a) ||
    !Array.isArray(value.b) ||
    !finite(value.elapsed) ||
    value.elapsed < 0
  )
    throw new Error('The saved comparison result is malformed.');
  const n = settings.resolution ** 2;
  if (
    value.a.length !== n ||
    value.b.length !== n ||
    ![...value.a, ...value.b].every((v) => finite(v) && v >= 0 && v <= 1)
  )
    throw new Error('The saved comparison fields have invalid dimensions or values.');
  const a = Float32Array.from(value.a),
    b = Float32Array.from(value.b);
  // Recalculate metrics from saved samples; never trust a supplied score.
  return {
    a,
    b,
    metrics: compareFields(a, b, settings.resolution, settings.align),
    elapsed: value.elapsed,
  };
}

/** Deterministic key ordering prevents equivalent prop objects from resetting in-progress edits. */
export function stableExperimentKey(input: unknown): string {
  let count = 0;
  const normalize = (value: unknown, depth: number): unknown => {
    if (++count > 100000 || depth > 30)
      throw new Error('The experiment contains too many values or nested objects.');
    if (value === null || typeof value === 'string' || typeof value === 'boolean') return value;
    if (typeof value === 'number') {
      if (!Number.isFinite(value)) throw new Error('The experiment contains a non-finite number.');
      return value;
    }
    if (Array.isArray(value)) return value.map((v) => normalize(v, depth + 1));
    if (object(value))
      return Object.fromEntries(
        Object.keys(value)
          .filter((key) => value[key] !== undefined)
          .sort()
          .map((key) => [key, normalize(value[key], depth + 1)]),
      );
    throw new Error('The experiment must contain JSON values only.');
  };
  const result = JSON.stringify(normalize(input, 0));
  if (result.length > 4_000_000) throw new Error('Choose an experiment smaller than 4 MB.');
  return result;
}

export function prepareExperimentReplay(input: unknown): {
  manifest: LaboratoryManifest;
  key: string;
} {
  const key = stableExperimentKey(input);
  if (
    !object(input) ||
    input.schema !== 'loops-laboratory-v1' ||
    !['discovery', 'orbit', 'comparison'].includes(String(input.instrument))
  )
    throw new Error('Choose an exported LOOPS Laboratory v1 experiment.');
  if (input.method !== 'loops-quadratic-instruments-1' || input.precision !== 'IEEE-754 binary64')
    throw new Error('This experiment uses an unsupported method or numerical precision.');
  if (
    typeof input.createdAt !== 'string' ||
    !Number.isFinite(Date.parse(input.createdAt)) ||
    typeof input.claim !== 'string'
  )
    throw new Error('The experiment provenance is incomplete.');
  if (input.instrument === 'discovery')
    restoreSurveyResult(input.result, validateScanSettings(input.settings));
  if (input.instrument === 'comparison')
    restoreComparisonResult(input.result, validateComparisonSettings(input.settings));
  if (input.instrument === 'orbit') validateOrbitSettings(input.settings);
  // Keep the exact original settings and metadata. Validation does not silently rewrite the record.
  return { manifest: JSON.parse(key) as LaboratoryManifest, key };
}
