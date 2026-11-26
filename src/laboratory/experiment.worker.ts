/// <reference lib="webworker" />
import {
  analyzeOrbit,
  compareFields,
  refineCenter,
  regionRow,
  sampleColor,
  sampleParameter,
  validateComparisonSettings,
  validateScanSettings,
} from './math';
import type { ComparisonSettings, DiscoveryCandidate, ScanSettings } from './math';

type Command =
  | { id: number; type: 'scan'; settings: ScanSettings }
  | { id: number; type: 'compare'; settings: ComparisonSettings }
  | { id: number; type: 'pause' }
  | { id: number; type: 'resume' }
  | { id: number; type: 'cancel' };
let active = 0,
  paused = false;
const tick = () => new Promise<void>((resolve) => setTimeout(resolve, 0));
async function ready(id: number) {
  while (paused && active === id) await new Promise<void>((resolve) => setTimeout(resolve, 50));
  return active === id;
}
self.onmessage = async (event: MessageEvent<Command>) => {
  const message = event.data;
  if (message.type === 'cancel') {
    if (message.id === active) active++;
    return;
  }
  if (message.type === 'pause' || message.type === 'resume') {
    if (message.id === active) paused = message.type === 'pause';
    return;
  }
  active = message.id;
  paused = false;
  const id = message.id,
    started = performance.now();
  try {
    if (message.type === 'scan') {
      const s = validateScanSettings(message.settings),
        total = s.resolution * s.resolution;
      const pixels = new Uint8ClampedArray(total * 4),
        candidates: DiscoveryCandidate[] = [];
      const centerSeparation = Math.max(
        Number.EPSILON * 64,
        Math.min(s.reMax - s.reMin, s.imMax - s.imMin) * 1e-10,
      );
      let escaped = 0,
        attracting = 0,
        unresolved = 0;
      const periods: Record<string, number> = {};
      for (let index = 0; index < total; index++) {
        if (index % 48 === 0) {
          await tick();
          if (!(await ready(id))) return;
        }
        const parameter = sampleParameter(
          s,
          index % s.resolution,
          Math.floor(index / s.resolution),
        );
        const analysis = analyzeOrbit(parameter, s.iterations, s.maxPeriod, 1e-9, false);
        const rgb = sampleColor(
          analysis.disposition,
          analysis.period,
          analysis.escapeIteration,
          s.iterations,
        );
        pixels.set([...rgb, 255], index * 4);
        if (analysis.disposition === 'escaped') escaped++;
        else if (analysis.period !== null) {
          attracting++;
          periods[String(analysis.period)] = (periods[String(analysis.period)] ?? 0) + 1;
          const refined = refineCenter(parameter, analysis.period, s);
          // Only component centers which pass refinement become catalog candidates.
          if (
            refined.refined &&
            candidates.length < 256 &&
            !candidates.some(
              (c) =>
                c.period === analysis.period &&
                Math.hypot(c.center.re - refined.center.re, c.center.im - refined.center.im) <
                  centerSeparation,
            )
          ) {
            candidates.push({
              id: `p${analysis.period}-${refined.center.re.toPrecision(17)}-${refined.center.im.toPrecision(17)}`,
              period: analysis.period,
              center: refined.center,
              seed: parameter,
              residual: refined.residual,
              multiplierModulus: analysis.multiplierModulus ?? 0,
              refined: true,
            });
          }
        } else unresolved++;
        if ((index + 1) % (s.resolution * 2) === 0 || index === total - 1) {
          self.postMessage({
            id,
            type: 'scan-progress',
            processed: index + 1,
            total,
            escaped,
            attracting,
            unresolved,
            periods,
            candidates,
            pixels,
            elapsed: performance.now() - started,
          });
        }
      }
      self.postMessage({
        id,
        type: 'scan-complete',
        processed: total,
        total,
        escaped,
        attracting,
        unresolved,
        periods,
        candidates,
        pixels,
        elapsed: performance.now() - started,
      });
    } else {
      const s = validateComparisonSettings(message.settings),
        a = new Float32Array(s.resolution ** 2),
        b = new Float32Array(s.resolution ** 2);
      for (let y = 0; y < s.resolution; y++) {
        regionRow(s.a, s.resolution, s.iterations, y, a);
        regionRow(s.b, s.resolution, s.iterations, y, b);
        if (y % 4 === 0) {
          self.postMessage({ id, type: 'compare-progress', processed: y + 1, total: s.resolution });
          await tick();
          if (!(await ready(id))) return;
        }
      }
      if (active !== id) return;
      self.postMessage(
        {
          id,
          type: 'compare-complete',
          a,
          b,
          metrics: compareFields(a, b, s.resolution, s.align),
          elapsed: performance.now() - started,
        },
        [a.buffer, b.buffer],
      );
    }
  } catch (error) {
    if (active === id)
      self.postMessage({
        id,
        type: 'error',
        message: error instanceof Error ? error.message : 'The experiment could not finish.',
      });
  }
};
