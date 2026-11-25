import { fixedMandelbrot, precisionColor, precisionCoordinate, preparePrecisionFrame } from '../lib/precision';
import type { PrecisionMessage, PrecisionRequest } from '../lib/precision';

const scope = self as unknown as DedicatedWorkerGlobalScope;
const send = (message: PrecisionMessage, transfer: Transferable[] = []) => scope.postMessage(message, transfer);

scope.addEventListener('message', (event: MessageEvent<PrecisionRequest>) => {
  const request = event.data;
  if (request?.type !== 'render') return;
  const id = request.id;
  try {
    const frame = preparePrecisionFrame(request.settings);
    const start = performance.now();
    let escapedPixels = 0;
    // Each strip is transferred, not copied. Terminating this worker cancels even
    // during a costly row; no main-thread recurrence or shared mutable state.
    const stripHeight = 3;
    for (let y = 0; y < frame.height; y += stripHeight) {
      const rows = Math.min(stripHeight, frame.height - y);
      const pixels = new Uint8ClampedArray(frame.width * rows * 4);
      for (let dy = 0; dy < rows; dy++) {
        for (let x = 0; x < frame.width; x++) {
          const [cr, ci] = precisionCoordinate(frame, x, y + dy);
          const point = fixedMandelbrot(cr, ci, frame.bits, frame.iterations);
          if (point.escaped) escapedPixels++;
          pixels.set(precisionColor(point, frame.unit), (dy * frame.width + x) * 4);
        }
      }
      const buffer = pixels.buffer;
      send({ type: 'strip', id, y, rows, width: frame.width, height: frame.height, bits: frame.bits, elapsedMs: performance.now() - start, buffer }, [buffer]);
    }
    send({ type: 'complete', id, elapsedMs: performance.now() - start, escapedPixels, totalPixels: frame.width * frame.height, bits: frame.bits });
  } catch (error) {
    send({ type: 'error', id, message: error instanceof Error ? error.message : 'The precision calculation failed.' });
  }
});
