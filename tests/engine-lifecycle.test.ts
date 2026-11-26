import assert from 'node:assert/strict';
import { test } from 'node:test';
import { FractalEngine } from '../src/engine/FractalEngine.ts';
import { DEFAULT_STATE } from '../src/presets.ts';

function environment(run: (env: ReturnType<typeof createEnvironment>) => void) {
  const env = createEnvironment();
  const descriptors = new Map<string, PropertyDescriptor | undefined>();
  for (const [key, value] of Object.entries(env.globals)) {
    descriptors.set(key, Object.getOwnPropertyDescriptor(globalThis, key));
    Object.defineProperty(globalThis, key, { value, configurable: true, writable: true });
  }
  try { run(env); }
  finally {
    for (const [key, descriptor] of descriptors) {
      if (descriptor) Object.defineProperty(globalThis, key, descriptor);
      else Reflect.deleteProperty(globalThis, key);
    }
  }
}

function createEnvironment() {
  let now = 0, next = 0, writes = 0;
  const frames = new Map<number, FrameRequestCallback>();
  const timers = new Map<number, { due: number; callback: () => void }>();
  const workers: FakeWorker[] = [];
  class Canvas extends EventTarget {
    width = 80; height = 60; hidden = false; style = {}; tabIndex = -1;
    throwGpu = false;
    gpu: ReturnType<typeof graphics> | null = null;
    context = { fillStyle: '',
      createImageData: (width: number, height: number) => ({ width, height, data: new Uint8ClampedArray(width * height * 4) }),
      putImageData: () => { writes++; }, fillRect: () => undefined, drawImage: () => { writes++; },
    };
    getContext(type: string) { if (type === 'webgl2') { if (this.throwGpu) throw new Error('Graphics blocked'); return this.gpu; } return this.context; }
    hasAttribute() { return false; }
    setAttribute() {}
    getBoundingClientRect() { return { left: 0, top: 0, width: 80, height: 60 }; }
    focus() {}
    setPointerCapture() {}
    toDataURL() { return 'data:image/png;base64,test'; }
  }
  function graphics() {
    let draws = 0, released = 0;
    const noop = () => undefined;
    return {
      VERTEX_SHADER: 1, FRAGMENT_SHADER: 2, COMPILE_STATUS: 3, LINK_STATUS: 4, TRIANGLES: 5,
      CULL_FACE: 6, DEPTH_TEST: 7, COLOR_BUFFER_BIT: 8, DEPTH_BUFFER_BIT: 16,
      createShader: () => ({}), shaderSource: noop, compileShader: noop, getShaderParameter: () => true,
      deleteShader: noop, createProgram: () => ({}), attachShader: noop, linkProgram: noop,
      getProgramParameter: () => true, getUniformLocation: () => ({}), deleteProgram: noop,
      createVertexArray: () => ({}), deleteVertexArray: noop, deleteBuffer: noop,
      viewport: noop, useProgram: noop, uniform2f: noop, uniform3f: noop, uniform1f: noop, uniform1i: noop,
      enable: noop, disable: noop, clearColor: noop, clear: noop, bindVertexArray: noop,
      drawArrays: () => { draws++; },
      getExtension: (name: string) => name === 'WEBGL_lose_context' ? { loseContext: () => { released++; } } : null,
      draws: () => draws, released: () => released,
    };
  }
  class FakeWorker {
    terminated = false; messages: unknown[] = []; onmessage: unknown; onerror: unknown;
    constructor() { workers.push(this); }
    postMessage(message: unknown) { this.messages.push(message); }
    terminate() { this.terminated = true; }
  }
  const document = Object.assign(new EventTarget(), { hidden: false, createElement: () => new Canvas() });
  const globals = {
    document, window: { devicePixelRatio: 1 }, performance: { now: () => now },
    ResizeObserver: class { observe() {} disconnect() {} }, IntersectionObserver: undefined,
    Worker: FakeWorker,
    requestAnimationFrame: (callback: FrameRequestCallback) => { const id = ++next; frames.set(id, callback); return id; },
    cancelAnimationFrame: (id: number) => frames.delete(id),
    setTimeout: (callback: () => void, delay = 0) => { const id = ++next; timers.set(id, { due: now + delay, callback }); return id; },
    clearTimeout: (id: number) => timers.delete(id),
  };
  function frame() {
    now += 16;
    const batch = [...frames.entries()];
    for (const [id, callback] of batch) { frames.delete(id); callback(now); }
  }
  function settle() {
    for (let n = 0; n < 100 && frames.size; n++) frame();
    assert.equal(frames.size, 0, 'A settled renderer must release its animation loop.');
  }
  function advance(ms: number) {
    now += ms;
    for (const [id, timer] of [...timers]) if(timer.due<=now){timers.delete(id);timer.callback();}
  }
  return { globals, document, Canvas, graphics, frames, timers, workers, frame, settle, advance, writes: () => writes };
}

test('a settled CPU view consumes no animation frames', () => environment(env => {
  const engine = new FractalEngine(new env.Canvas() as unknown as HTMLCanvasElement, { ...DEFAULT_STATE, scene: 'mandelbrot', iterations: 128 });
  env.settle();
  assert.ok(env.writes() > 0);
  assert.equal(env.timers.size, 0);
  engine.destroy();
}));

test('destroying a viewport invalidates and cancels progressive work', () => environment(env => {
  const engine = new FractalEngine(new env.Canvas() as unknown as HTMLCanvasElement, { ...DEFAULT_STATE, scene: 'mandelbrot', iterations: 128 });
  env.frame();
  const staleCallbacks = [...env.frames.values()];
  engine.destroy();
  const before = env.writes();
  for (const callback of staleCallbacks) callback(1000);
  assert.equal(env.writes(), before, 'Canceled work must not draw into an unmounted viewport.');
  assert.equal(env.frames.size, 0);
  assert.equal(env.timers.size, 0);
}));

test('WebGL absence preserves 3D through the Float64 worker and hidden tabs cancel it', () => environment(env => {
  const patches: Record<string, unknown>[] = [];
  const engine = new FractalEngine(new env.Canvas() as unknown as HTMLCanvasElement, DEFAULT_STATE, { onChange: patch => patches.push(patch) }, new env.Canvas() as unknown as HTMLCanvasElement);
  env.frame();
  assert.equal(env.workers.length, 1);
  assert.equal((env.workers[0].messages[0] as { state: { scene: string } }).state.scene, 'mandelbulb');
  assert.ok(patches.every(patch => patch.scene !== 'mandelbrot'));
  env.document.hidden = true; env.document.dispatchEvent(new Event('visibilitychange'));
  assert.equal(env.workers[0].terminated, true);
  assert.equal(env.frames.size, 0);
  assert.equal(env.timers.size, 0);
  env.document.hidden = false; env.document.dispatchEvent(new Event('visibilitychange')); env.frame();
  assert.equal(env.workers.length, 2, 'Restoring visibility restarts the interrupted view.');
  engine.destroy();
  assert.ok(env.workers.every(worker => worker.terminated));
}));

test('a context creation exception reports the fallback instead of crashing', () => environment(env => {
  const canvas = new env.Canvas(); canvas.throwGpu = true;
  const errors: string[] = [];
  const engine = new FractalEngine(canvas as unknown as HTMLCanvasElement, { ...DEFAULT_STATE, scene: 'mandelbrot' }, { onError: message => errors.push(message) });
  env.settle();
  assert.ok(errors.some(message => message.includes('CPU')));
  assert.ok(env.writes() > 0);
  engine.destroy();
}));

test('GPU volumes refine on timed wake-ups and then fully release the animation loop', () => environment(env => {
  const canvas = new env.Canvas(); canvas.gpu = env.graphics();
  const engine = new FractalEngine(canvas as unknown as HTMLCanvasElement, { ...DEFAULT_STATE, autoRotate: false });
  env.settle();
  assert.equal(canvas.gpu.draws(), 1);
  assert.equal(env.timers.size, 1, 'Only the next refinement deadline remains.');
  env.advance(200); env.settle();
  assert.equal(canvas.gpu.draws(), 2);
  env.advance(500); env.settle();
  assert.equal(canvas.gpu.draws(), 3);
  assert.equal(env.timers.size, 0);
  engine.destroy();
  assert.equal(canvas.gpu.released(), 1, 'Unmounting releases the browser GPU context slot.');
}));

test('context loss starts the preserved volume in a worker and restoration returns to GPU', () => environment(env => {
  const canvas = new env.Canvas(); canvas.gpu = env.graphics();
  const engine = new FractalEngine(canvas as unknown as HTMLCanvasElement, { ...DEFAULT_STATE, autoRotate: false }, {}, new env.Canvas() as unknown as HTMLCanvasElement);
  env.frame();
  const loss = new Event('webglcontextlost', { cancelable: true });
  canvas.dispatchEvent(loss); env.frame();
  assert.equal(loss.defaultPrevented, true, 'Context restoration is allowed.');
  assert.equal(env.workers.length, 1);
  assert.equal((env.workers[0].messages[0] as { state: { scene: string } }).state.scene, 'mandelbulb');
  canvas.dispatchEvent(new Event('webglcontextrestored')); env.frame();
  assert.equal(env.workers[0].terminated, true);
  assert.ok(canvas.gpu.draws() >= 2);
  engine.destroy();
}));
