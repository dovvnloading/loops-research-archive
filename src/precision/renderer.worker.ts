/// <reference lib="webworker" />
import { viewDepth } from './coordinates.ts';
import { prepareKernel } from './kernel.ts';
import { colorTile } from './palette.ts';
import { GpuPreview } from './gpu-preview.ts';
import type {
  PrecisionRenderRequest,
  PrecisionStats,
  PrecisionWorkerRequest,
  PrecisionWorkerResponse,
} from './types.ts';

const scope = self as unknown as DedicatedWorkerGlobalScope;
let generation = 0;
let gpu: GpuPreview | null | undefined;
let cache:
  | { key: string; width: number; height: number; samples: Float32Array; stats: PrecisionStats }
  | undefined;
const pause = () => new Promise<void>((resolve) => setTimeout(resolve, 0));
function send(message: PrecisionWorkerResponse, transfers: Transferable[] = []) {
  scope.postMessage(message, transfers);
}
function cacheKey(request: PrecisionRenderRequest) {
  const { palette: _palette, ...view } = request.view;
  return JSON.stringify([view, request.width, request.height]);
}

async function render(request: PrecisionRenderRequest, ticket: number) {
  const started = performance.now();
  const key = cacheKey(request);
  if (cache?.key === key) {
    const pixels = colorTile(cache.samples, request.view.palette, request.exposure);
    const stats: PrecisionStats = {
      ...cache.stats,
      elapsedMs: performance.now() - started,
      progress: 1,
      phase: 'complete',
    };
    send(
      {
        type: 'tile',
        id: request.id,
        x: 0,
        y: 0,
        width: cache.width,
        height: cache.height,
        frameWidth: cache.width,
        frameHeight: cache.height,
        pixels,
        stats,
      },
      [pixels.buffer],
    );
    send({ type: 'complete', id: request.id, stats });
    return;
  }
  const kernel = prepareKernel(request.view);
  const aspect = request.width / request.height;
  const finalWidth = Math.max(32, Math.min(1800, Math.round(request.width)));
  const finalHeight = Math.max(24, Math.round(finalWidth / aspect));
  let gpuPreview = false;
  if (kernel.mode === 'float64' && Number(request.view.span) >= 1e-7) {
    if (gpu === undefined) gpu = GpuPreview.create();
    const width = Math.min(400, finalWidth),
      height = Math.max(24, Math.round(width / aspect));
    const pixels = gpu?.render(request.view, width, height, request.exposure);
    if (pixels) {
      gpuPreview = true;
      send(
        {
          type: 'tile',
          id: request.id,
          x: 0,
          y: 0,
          width,
          height,
          frameWidth: width,
          frameHeight: height,
          pixels,
          stats: {
            fps: 0,
            resolution: `${width} × ${height}`,
            precision: 'Double-single preview',
            renderer: 'WebGL2 preview · Float64 refining',
            phase: 'preview',
            progress: 0,
            elapsedMs: performance.now() - started,
            referenceBits: 48,
            repairedPixels: 0,
            precisionDigits: 14,
          },
        },
        [pixels.buffer],
      );
      await pause();
      if (generation !== ticket) return;
    }
  }
  const candidateWidths = gpuPreview
    ? [Math.min(400, finalWidth), finalWidth]
    : [Math.min(160, finalWidth), Math.min(400, finalWidth), finalWidth];
  const widths = [...new Set(candidateWidths)];
  const totalPixels = widths.reduce(
    (sum, width) => sum + width * Math.max(24, Math.round(width / aspect)),
    0,
  );
  let completedPixels = 0,
    repairedPixels = 0,
    lastYield = performance.now();
  let lastStats: PrecisionStats | undefined;
  for (let pass = 0; pass < widths.length; pass++) {
    if (generation !== ticket) return;
    const width = widths[pass],
      height = Math.max(24, Math.round(width / aspect));
    const samples = new Float32Array(width * height);
    const tileHeight = kernel.mode === 'perturbation' ? 6 : 12;
    for (let y0 = 0; y0 < height; y0 += tileHeight) {
      if (generation !== ticket) return;
      const rows = Math.min(tileHeight, height - y0);
      for (let y = y0; y < y0 + rows; y++) {
        for (let x = 0; x < width; x++) {
          const sample = kernel.sample(x, y, width, height);
          samples[y * width + x] = sample.smooth;
          if (sample.repaired) repairedPixels++;
          if (x % 64 === 63 && performance.now() - lastYield > 14) {
            await pause();
            lastYield = performance.now();
            if (generation !== ticket) return;
          }
        }
      }
      completedPixels += width * rows;
      const pixels = colorTile(
        samples.subarray(y0 * width, (y0 + rows) * width),
        request.view.palette,
        request.exposure,
        y0 * width,
      );
      lastStats = {
        fps: 0,
        resolution: `${width} × ${height}`,
        precision: kernel.mode === 'perturbation' ? `${kernel.bits}-bit reference` : 'Float64',
        renderer:
          kernel.mode === 'perturbation' ? 'Perturbation · BigInt repair' : 'Float64 worker',
        phase: pass === 0 ? 'preview' : repairedPixels ? 'repairing' : 'refining',
        progress: Math.min(1, completedPixels / totalPixels),
        elapsedMs: performance.now() - started,
        referenceBits: kernel.bits,
        repairedPixels,
        precisionDigits:
          kernel.mode === 'perturbation' ? Math.floor(kernel.bits * Math.LOG10E * Math.LN2) : 15,
      };
      send(
        {
          type: 'tile',
          id: request.id,
          x: 0,
          y: y0,
          width,
          height: rows,
          frameWidth: width,
          frameHeight: height,
          pixels,
          stats: lastStats,
        },
        [pixels.buffer],
      );
      if (performance.now() - lastYield > 14) {
        await pause();
        lastYield = performance.now();
      }
    }
    if (pass === widths.length - 1 && generation === ticket && lastStats) {
      const stats: PrecisionStats = {
        ...lastStats,
        phase: 'complete',
        progress: 1,
        elapsedMs: performance.now() - started,
      };
      cache = { key, width, height, samples, stats };
      send({ type: 'complete', id: request.id, stats });
    }
    await pause();
  }
}

scope.addEventListener('message', (event: MessageEvent<PrecisionWorkerRequest>) => {
  const request = event.data;
  generation++;
  if (request.type === 'cancel') return;
  const ticket = generation;
  if (
    !Number.isFinite(request.width) ||
    !Number.isFinite(request.height) ||
    request.width < 1 ||
    request.height < 1 ||
    request.width > 1800 ||
    request.height > 1800
  ) {
    send({
      type: 'error',
      id: request.id,
      message: 'The render dimensions are outside the supported range.',
    });
    return;
  }
  // Keep the depth lookup exercised here so malformed coordinates fail before allocating a frame.
  try {
    viewDepth(request.view);
  } catch (error) {
    send({
      type: 'error',
      id: request.id,
      message: error instanceof Error ? error.message : 'Invalid coordinates.',
    });
    return;
  }
  void render(request, ticket).catch((error) => {
    if (generation === ticket)
      send({
        type: 'error',
        id: request.id,
        message:
          error instanceof Error
            ? error.message
            : 'The precision renderer could not complete this frame.',
      });
  });
});
