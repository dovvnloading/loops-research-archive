/// <reference lib="webworker" />
import { prepareKernel } from '../precision/kernel';
import { colorTile } from '../precision/palette';
import { prepareVolume } from '../engine/volume64';
import type { JournalPayload } from '../journal/types';
const scope = self as unknown as DedicatedWorkerGlobalScope;
let generation = 0;
const yieldTask = () => new Promise<void>((r) => setTimeout(r, 0));
scope.onmessage = (
  event: MessageEvent<
    | { type: 'render'; id: number; payload: JournalPayload; width: number; height: number }
    | { type: 'cancel' }
  >,
) => {
  const generationId = ++generation;
  if (event.data.type === 'cancel') return;
  const { id, payload, width, height } = event.data;
  if (
    !Number.isInteger(width) ||
    !Number.isInteger(height) ||
    width < 16 ||
    height < 16 ||
    width > 4096 ||
    height > 4096 ||
    width * height > 16_777_216
  ) {
    scope.postMessage({
      type: 'error',
      id,
      message: 'Choose an image up to 4,096 pixels per side.',
    });
    return;
  }
  const run = async () => {
    const plane = payload.engine.scene === 'mandelbrot' || payload.engine.scene === 'julia';
    const kernel = plane ? prepareKernel(payload.exact) : null;
    const volume = !plane
      ? prepareVolume({ state: payload.engine, width, height, preview: false })
      : null;
    let lastYield = performance.now();
    for (let y0 = 0; y0 < height; y0 += 4) {
      if (generation !== generationId) return;
      const rows = Math.min(4, height - y0);
      const samples = plane ? new Float32Array(width * rows) : null;
      let pixels = new Uint8ClampedArray(width * rows * 4);
      for (let y = y0; y < y0 + rows; y++)
        for (let x = 0; x < width; x++) {
          const index = (y - y0) * width + x;
          if (kernel && samples) samples[index] = kernel.sample(x, y, width, height).smooth;
          else if (volume) pixels.set(volume.pixel(x, y), index * 4);
          if (x % 32 === 31 && performance.now() - lastYield > 16) {
            await yieldTask();
            lastYield = performance.now();
            if (generation !== generationId) return;
          }
        }
      if (samples)
        pixels.set(colorTile(samples, payload.exact.palette, payload.engine.exposure, y0 * width));
      scope.postMessage(
        { type: 'tile', id, y: y0, width, height: rows, pixels, progress: (y0 + rows) / height },
        [pixels.buffer],
      );
      await yieldTask();
    }
    if (generation === generationId) scope.postMessage({ type: 'complete', id, width, height });
  };
  void run().catch((error) =>
    scope.postMessage({
      type: 'error',
      id,
      message: error instanceof Error ? error.message : 'The export could not be rendered.',
    }),
  );
};
