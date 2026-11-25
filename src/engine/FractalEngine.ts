import type { EngineHooks, EngineState, Palette, SceneId } from '../types';
import { clearanceAt, dolly, eye, flightStep, iterationBudget, volumeScene } from './navigation';
import {
  complexFragment,
  fullscreenVertex,
  landscapeFragment,
  landscapeVertex,
  volumeFragment,
} from './shaders';

/** A deliberate floor: double-single rendering is not arbitrary precision. */
export const MIN_COMPLEX_SCALE = 1e-7;
export const MIN_LANDSCAPE_SCALE = 1e-4;

const sceneIds: Record<SceneId, number> = {
  mandelbulb: 0, mandelbox: 1, quaternion: 2, mandelbrot: 3, julia: 4, landscape: 5,
};
const paletteIds: Record<Palette, number> = { glacier: 0, ember: 1, violet: 2, mono: 3 };
const uniformNames = [
  'uResolution', 'uCamera', 'uEye', 'uScene', 'uIterations', 'uPalette', 'uPower',
  'uBailout', 'uDetail', 'uExposure', 'uSlice', 'uTrap', 'uJuliaHi', 'uJuliaLo',
  'uCenterHi', 'uCenterLo', 'uScale', 'uGrid',
] as const;
type UniformName = typeof uniformNames[number];
interface Program { program: WebGLProgram; uniforms: Record<UniformName, WebGLUniformLocation | null> }
type Point = { x: number; y: number };

const clamp = (x: number, lo: number, hi: number) => Math.min(hi, Math.max(lo, Number.isFinite(x) ? x : lo));
const clone = (s: EngineState): EngineState => ({ ...s, camera: { ...s.camera, ...(s.camera.position ? {position:[...s.camera.position] as [number,number,number]} : {}) }, center: [...s.center], julia: [...s.julia] });
const planar = (s: SceneId) => s === 'mandelbrot' || s === 'julia';

/**
 * A small renderer with no framework dependency and no state updates per frame.
 * The CPU owns navigation; custom GLSL owns the fractal iterations and shading.
 */
export class FractalEngine {
  private canvas: HTMLCanvasElement;
  private state: EngineState;
  private hooks: EngineHooks;
  private gl: WebGL2RenderingContext | null = null;
  private cpu: CanvasRenderingContext2D | null = null;
  private programs: Partial<Record<'volume' | 'complex' | 'landscape', Program>> = {};
  private fullscreenVao: WebGLVertexArrayObject | null = null;
  private landscapeVao: WebGLVertexArrayObject | null = null;
  private buffers: WebGLBuffer[] = [];
  private landscapeCount = 0;
  private resizeObserver: ResizeObserver;
  private abort = new AbortController();
  private pointers = new Map<number, Point>();
  private pointerTravel = 0;
  private raf = 0;
  private disposed = false;
  private lost = false;
  private dirty = true;
  private lastFrame = 0;
  private statsStart = performance.now();
  private renderedFrames = 0;
  private rotationSync = 0;
  private autoScale = 0.78;
  private slowFrames = 0;
  private lastWasRendered = false;
  private cpuGeneration = 0;
  private lastStatsFps = 0;
  private refinement = 0;
  private lastInteraction = performance.now();
  private effectiveIterations = 12;
  private clearance = 1;

  constructor(canvas: HTMLCanvasElement, state: EngineState, hooks: EngineHooks = {}) {
    this.canvas = canvas;
    this.state = this.sanitize(state);
    this.hooks = hooks;
    canvas.style.touchAction = 'none';
    canvas.setAttribute('aria-label', 'Interactive fractal viewport. Drag to orbit or look around. Scroll toward the cursor to fly. WASD/QE move in 3D. Shift-click the complex plane to choose a Julia parameter.');
    if (!canvas.hasAttribute('tabindex')) canvas.tabIndex = 0;
    this.gl = canvas.getContext('webgl2', {
      alpha: false, antialias: false, depth: true,
      powerPreference: 'high-performance', preserveDrawingBuffer: true,
    });
    if (this.gl) {
      try { this.initializeGpu(); }
      catch (error) { this.lost = true; this.hooks.onError?.(`The GPU renderer could not start: ${String(error)}`); }
    } else {
      this.cpu = canvas.getContext('2d');
      this.state.scene = 'mandelbrot';
      this.state.iterations = Math.max(128, this.state.iterations);
      this.hooks.onChange?.({ scene: 'mandelbrot', iterations: this.state.iterations, autoRotate: false });
      this.hooks.onError?.('WebGL2 is unavailable. A CPU Mandelbrot view is available; 3D requires WebGL2.');
    }
    this.bindInput();
    this.resizeObserver = new ResizeObserver(() => this.resize());
    this.resizeObserver.observe(canvas);
    this.resize();
    this.emitStats(0);
    this.schedule();
  }

  setState(state: EngineState) {
    if (this.disposed) return;
    const previous = this.state;
    this.state = this.sanitize(state);
    if (this.cpu && (!planar(this.state.scene) || this.state.autoRotate)) {
      this.state.scene = planar(this.state.scene) ? this.state.scene : 'mandelbrot';
      this.state.iterations = Math.max(128, this.state.iterations);
      this.state.autoRotate = false;
      this.hooks.onChange?.({ scene: this.state.scene, iterations: this.state.iterations, autoRotate: false });
    }
    this.restartRefinement();
    if (previous.scene !== this.state.scene) {
      this.autoScale = 0.78;
      this.slowFrames = 0;
      this.resize();
    } else if (previous.quality !== this.state.quality) this.resize();
    if (this.gl && !this.lost && this.state.scene === 'landscape' && (previous.scene !== 'landscape' || previous.detail !== this.state.detail)) this.createLandscapeMesh();
    this.dirty = true;
    this.cpuGeneration++;
    this.schedule();
  }

  private restartRefinement() {
    this.lastInteraction=performance.now();
    if (volumeScene(this.state.scene) && this.refinement!==0) {this.refinement=0;this.resize();}
  }

  /** Public controls use exactly the same navigation as pointer input. */
  zoom(multiplier:number) {
    const r=this.canvas.getBoundingClientRect();
    this.zoomAt(r.left+r.width/2,r.top+r.height/2,multiplier);
  }

  fly(key:string) {
    if(volumeScene(this.state.scene))this.change({autoRotate:false,camera:flightStep(this.state,key)});
  }

  resize() {
    if (this.disposed) return;
    const bounds = this.canvas.getBoundingClientRect();
    const quality = this.state.quality;
    const base = quality === 'high' ? 1 : quality === 'balanced' ? 0.8 : quality === 'low' ? 0.52 : volumeScene(this.state.scene)&&this.refinement===2 ? Math.max(.78,this.autoScale) : this.autoScale;
    let ratio = Math.min(window.devicePixelRatio || 1, quality === 'high' ? 2 : 1.5) * base;
    const maxPixels = quality === 'high' ? 2_400_000 : quality === 'low' ? 350_000 : 1_000_000;
    // Render interaction previews first; recover spatial detail after input stops.
    if(volumeScene(this.state.scene)) ratio*=this.refinement===0?.55:this.refinement===1?.8:1;
    const pixels = bounds.width * bounds.height * ratio * ratio;
    if (pixels > maxPixels) ratio *= Math.sqrt(maxPixels / pixels);
    if (this.cpu) ratio = Math.min(ratio, 400 / Math.max(1, bounds.width));
    const width = Math.max(1, Math.round(bounds.width * ratio));
    const height = Math.max(1, Math.round(bounds.height * ratio));
    if (this.canvas.width !== width || this.canvas.height !== height) {
      this.canvas.width = width;
      this.canvas.height = height;
      this.cpuGeneration++;
    }
    this.dirty = true;
    this.schedule();
  }

  /** Returns the actual current GPU image, at the active rendering resolution. */
  capture(): string {
    if (this.gl && !this.lost) {this.refinement=2;this.resize();this.renderGpu();}
    return this.canvas.toDataURL('image/png');
  }

  destroy() {
    this.disposed = true;
    cancelAnimationFrame(this.raf);
    this.raf = 0;
    this.cpuGeneration++;
    this.abort.abort();
    this.resizeObserver.disconnect();
    this.releaseGpu();
  }

  private sanitize(state: EngineState): EngineState {
    const s = clone(state);
    s.camera.yaw = Number.isFinite(s.camera.yaw) ? s.camera.yaw : 0.35;
    s.camera.pitch = clamp(s.camera.pitch, s.scene === 'landscape' ? 0.3 : -1.4, 1.4);
    s.camera.distance = clamp(s.camera.distance, 1.65, 14);
    if(!volumeScene(s.scene)||!s.camera.position||!s.camera.position.every(Number.isFinite)||Math.hypot(...s.camera.position)>14)delete s.camera.position;
    if(s.camera.position)s.autoRotate=false;
    s.power = clamp(s.power, s.scene === 'mandelbox' ? 1.2 : 2, s.scene === 'mandelbox' ? 3 : 16);
    s.iterations = Math.round(clamp(s.iterations, planar(s.scene) || s.scene === 'landscape' ? 32 : 2, planar(s.scene) ? 4096 : s.scene === 'landscape' ? 512 : s.scene==='mandelbox'?40:64));
    s.bailout = clamp(s.bailout, 2, 64);
    s.detail = clamp(s.detail, 0, 1);
    s.exposure = clamp(s.exposure, 0.2, 3);
    s.scale = clamp(s.scale, s.scene === 'landscape' ? MIN_LANDSCAPE_SCALE : MIN_COMPLEX_SCALE, 12);
    s.slice = clamp(s.slice, -2, 2);
    s.orbitTrap = clamp(s.orbitTrap, 0, 1);
    s.center = [clamp(s.center[0], -1e5, 1e5), clamp(s.center[1], -1e5, 1e5)];
    s.julia = [clamp(s.julia[0], -4, 4), clamp(s.julia[1], -4, 4)];
    return s;
  }

  private initializeGpu() {
    const gl = this.gl!;
    this.programs = {
      volume: this.createProgram(fullscreenVertex, volumeFragment),
      complex: this.createProgram(fullscreenVertex, complexFragment),
      landscape: this.createProgram(landscapeVertex, landscapeFragment),
    };
    this.fullscreenVao = gl.createVertexArray();
    this.landscapeVao = gl.createVertexArray();
    this.buffers = [];
    this.createLandscapeMesh();
    gl.disable(gl.CULL_FACE);
    this.lost = false;
  }

  private createLandscapeMesh() {
    const gl = this.gl!;
    for (const buffer of this.buffers) gl.deleteBuffer(buffer);
    const segments = Math.round(64 + this.state.detail * 192);
    const positions = new Float32Array((segments + 1) ** 2 * 2);
    let p = 0;
    for (let y = 0; y <= segments; y++) for (let x = 0; x <= segments; x++) {
      positions[p++] = (x / segments - 0.5) * 3.2;
      positions[p++] = (y / segments - 0.5) * 3.2;
    }
    const indices = new Uint32Array(segments * segments * 6);
    let k = 0;
    for (let y = 0; y < segments; y++) for (let x = 0; x < segments; x++) {
      const a = y * (segments + 1) + x;
      const b = a + segments + 1;
      indices[k++] = a; indices[k++] = b; indices[k++] = a + 1;
      indices[k++] = a + 1; indices[k++] = b; indices[k++] = b + 1;
    }
    const vertex = gl.createBuffer()!;
    const index = gl.createBuffer()!;
    this.buffers = [vertex, index];
    this.landscapeCount = indices.length;
    gl.bindVertexArray(this.landscapeVao);
    gl.bindBuffer(gl.ARRAY_BUFFER, vertex);
    gl.bufferData(gl.ARRAY_BUFFER, positions, gl.STATIC_DRAW);
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 2, gl.FLOAT, false, 0, 0);
    gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, index);
    gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, indices, gl.STATIC_DRAW);
    gl.bindVertexArray(null);
  }

  private createProgram(vertexSource: string, fragmentSource: string): Program {
    const gl = this.gl!;
    const compile = (type: number, source: string) => {
      const shader = gl.createShader(type);
      if (!shader) throw new Error('Unable to allocate a shader.');
      gl.shaderSource(shader, source);
      gl.compileShader(shader);
      if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
        const log = gl.getShaderInfoLog(shader);
        gl.deleteShader(shader);
        throw new Error(log || 'Shader compilation failed.');
      }
      return shader;
    };
    const vertex = compile(gl.VERTEX_SHADER, vertexSource);
    const fragment = compile(gl.FRAGMENT_SHADER, fragmentSource);
    const program = gl.createProgram();
    if (!program) throw new Error('Unable to allocate a GPU program.');
    gl.attachShader(program, vertex);
    gl.attachShader(program, fragment);
    gl.linkProgram(program);
    gl.deleteShader(vertex);
    gl.deleteShader(fragment);
    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
      const log = gl.getProgramInfoLog(program);
      gl.deleteProgram(program);
      throw new Error(log || 'Shader linking failed.');
    }
    const uniforms = Object.fromEntries(uniformNames.map(name => [name, gl.getUniformLocation(program, name)])) as Program['uniforms'];
    return { program, uniforms };
  }

  private releaseGpu() {
    const gl = this.gl;
    if (!gl) return;
    for (const value of Object.values(this.programs)) if (value) gl.deleteProgram(value.program);
    for (const buffer of this.buffers) gl.deleteBuffer(buffer);
    gl.deleteVertexArray(this.fullscreenVao);
    gl.deleteVertexArray(this.landscapeVao);
    this.programs = {};
    this.buffers = [];
  }

  private renderGpu() {
    const gl = this.gl;
    if (!gl || this.lost) return;
    const s = this.state;
    const kind = planar(s.scene) ? 'complex' : s.scene === 'landscape' ? 'landscape' : 'volume';
    const target = this.programs[kind];
    if (!target) return;
    const u = target.uniforms;
    gl.viewport(0, 0, this.canvas.width, this.canvas.height);
    gl.useProgram(target.program);
    gl.uniform2f(u.uResolution, this.canvas.width, this.canvas.height);
    gl.uniform3f(u.uCamera, s.camera.yaw, s.camera.pitch, s.camera.distance);
    gl.uniform1i(u.uScene, sceneIds[s.scene]);
    if(kind==='volume') {
      const p=eye(s.camera);
      this.clearance=clearanceAt(s,p);
      this.effectiveIterations=iterationBudget(s,this.clearance);
      gl.uniform3f(u.uEye,...p);
    } else this.effectiveIterations=s.iterations;
    gl.uniform1i(u.uIterations, this.effectiveIterations);
    gl.uniform1i(u.uPalette, paletteIds[s.palette] ?? 0);
    gl.uniform1f(u.uPower, s.power);
    gl.uniform1f(u.uBailout, s.bailout);
    gl.uniform1f(u.uDetail,kind==='volume'&&this.refinement===0?Math.min(s.detail,.55):s.detail);
    gl.uniform1f(u.uExposure, s.exposure);
    gl.uniform1f(u.uSlice, s.slice);
    gl.uniform1f(u.uTrap, s.orbitTrap);
    const xHi = Math.fround(s.center[0]);
    const yHi = Math.fround(s.center[1]);
    const jxHi = Math.fround(s.julia[0]);
    const jyHi = Math.fround(s.julia[1]);
    gl.uniform2f(u.uCenterHi, xHi, yHi);
    gl.uniform2f(u.uCenterLo, s.center[0] - xHi, s.center[1] - yHi);
    gl.uniform2f(u.uJuliaHi, jxHi, jyHi);
    gl.uniform2f(u.uJuliaLo, s.julia[0] - jxHi, s.julia[1] - jyHi);
    gl.uniform1f(u.uScale, s.scale);
    gl.uniform1i(u.uGrid, s.showGrid ? 1 : 0);
    if (kind === 'landscape') {
      gl.enable(gl.DEPTH_TEST);
      gl.clearColor(0.025, 0.04, 0.045, 1);
      gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
      gl.bindVertexArray(this.landscapeVao);
      gl.drawElements(gl.TRIANGLES, this.landscapeCount, gl.UNSIGNED_INT, 0);
    } else {
      gl.disable(gl.DEPTH_TEST);
      gl.bindVertexArray(this.fullscreenVao);
      gl.drawArrays(gl.TRIANGLES, 0, 3);
    }
    gl.bindVertexArray(null);
  }

  private schedule = () => {
    if (!this.raf && !this.disposed && !document.hidden) this.raf = requestAnimationFrame(this.frame);
  };

  private frame = (time: number) => {
    this.raf = 0;
    if (this.disposed || document.hidden) return;
    const delta = this.lastFrame ? Math.min(150, time - this.lastFrame) : 16;
    this.lastFrame = time;
    const animated = this.state.autoRotate && this.state.scene !== 'mandelbrot' && !this.cpu && !this.lost;
    if(volumeScene(this.state.scene)&&!animated){
      const idle=time-this.lastInteraction;
      const next=idle>650?2:idle>180?1:0;
      if(next>this.refinement){this.refinement=next;this.resize();}
    } else if(animated&&this.refinement!==0){this.refinement=0;this.resize();}
    if (animated) {
      if (this.state.scene === 'julia') {
        const angle = Math.min(delta, 80) * 0.000045;
        const [x, y] = this.state.julia;
        this.state.julia = [x * Math.cos(angle) - y * Math.sin(angle), x * Math.sin(angle) + y * Math.cos(angle)];
      } else this.state.camera.yaw += Math.min(delta, 80) * 0.00011;
      this.dirty = true;
      if (time - this.rotationSync > 1000) {
        this.rotationSync = time;
        this.hooks.onChange?.(this.state.scene === 'julia' ? { julia: [...this.state.julia] } : { camera: { ...this.state.camera } });
      }
    }
    // A slow preceding draw also triggers adjustment when the user has stopped
    // dragging. Static scenes should not stay at an unusable initial resolution.
    if (this.state.quality === 'auto' && (!volumeScene(this.state.scene)||this.refinement===0) && this.lastWasRendered && delta > 80 && this.autoScale > 0.34) {
      this.autoScale = Math.max(0.34, this.autoScale * Math.sqrt(50 / delta));
      this.resize();
    }
    const rendered = this.dirty && !this.lost;
    if (rendered) {
      if (this.gl) this.renderGpu();
      else if (this.cpu) this.renderCpu();
      this.renderedFrames++;
      this.dirty = false;
      if (this.state.quality === 'auto' && this.lastWasRendered && delta > 42) this.slowFrames++;
      else this.slowFrames = Math.max(0, this.slowFrames - 0.25);
      if (this.slowFrames >= 8 && this.autoScale > 0.34 && (!volumeScene(this.state.scene)||this.refinement===0)) {
        this.autoScale = Math.max(0.34, this.autoScale * 0.82);
        this.slowFrames = 0;
        this.resize();
      }
    }
    this.lastWasRendered = rendered;
    const elapsed = time - this.statsStart;
    if (elapsed > 1100) {
      this.lastStatsFps = Math.round(this.renderedFrames * 1000 / elapsed);
      this.emitStats(this.lastStatsFps);
      this.statsStart = time;
      this.renderedFrames = 0;
    }
    this.schedule();
  };

  private emitStats(fps: number) {
    this.hooks.onStats?.({
      fps,
      resolution: `${this.canvas.width} × ${this.canvas.height}`,
      precision: this.cpu ? 'Float64 · CPU' : planar(this.state.scene) ? 'Double-single · finite precision' : this.state.scene === 'landscape' ? 'Float32 · height field' : 'Float32 · adaptive distance estimate',
      ...(volumeScene(this.state.scene)?{iterations:this.effectiveIterations,clearance:this.clearance,refinement:['Preview','Refining','Settled'][this.refinement]}:{}),
      renderer: this.cpu ? 'CPU · 2D fallback' : this.lost ? 'GPU unavailable' : 'WebGL2 · custom GLSL',
    });
  }

  private change(patch: Partial<EngineState>) {
    this.state = this.sanitize({ ...this.state, ...patch });
    this.restartRefinement();
    this.dirty = true;
    this.cpuGeneration++;
    this.hooks.onChange?.(patch);
    this.schedule();
  }

  private pointToComplex(x: number, y: number): [number, number] {
    const r = this.canvas.getBoundingClientRect();
    return [
      this.state.center[0] + (x - r.left - r.width / 2) / r.height * this.state.scale,
      this.state.center[1] + (r.height / 2 - (y - r.top)) / r.height * this.state.scale,
    ];
  }

  private zoomAt(x: number, y: number, multiplier: number) {
    if (planar(this.state.scene)) {
      const before = this.pointToComplex(x, y);
      const scale = clamp(this.state.scale * multiplier, MIN_COMPLEX_SCALE, 12);
      const ratio = scale / this.state.scale;
      this.change({ scale, center: [
        before[0] + (this.state.center[0] - before[0]) * ratio,
        before[1] + (this.state.center[1] - before[1]) * ratio,
      ] });
    } else if(volumeScene(this.state.scene)) {
      const r=this.canvas.getBoundingClientRect();
      this.change({autoRotate:false,camera:dolly(this.state,multiplier,(x-r.left-r.width/2)/Math.max(1,r.height),(r.top+r.height/2-y)/Math.max(1,r.height))});
    } else {
      this.change({ camera: { ...this.state.camera, distance: clamp(this.state.camera.distance * multiplier, 1.65, 14) } });
    }
  }

  private bindInput() {
    const { signal } = this.abort;
    const c = this.canvas;
    c.addEventListener('contextmenu', e => e.preventDefault(), { signal });
    c.addEventListener('pointerdown', e => {
      if (e.button > 2) return;
      e.preventDefault();
      c.focus({ preventScroll: true });
      c.setPointerCapture(e.pointerId);
      this.pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
      if (this.pointers.size === 1) {
        this.pointerTravel = 0;
      }
      c.style.cursor = 'grabbing';
    }, { signal });
    c.addEventListener('pointermove', e => {
      const old = this.pointers.get(e.pointerId);
      if (!old) return;
      const dx = e.clientX - old.x, dy = e.clientY - old.y;
      this.pointerTravel += Math.hypot(dx, dy);
      if (this.pointers.size === 2) {
        const other = [...this.pointers.entries()].find(([id]) => id !== e.pointerId)?.[1];
        if (other) {
          const previous = Math.hypot(old.x - other.x, old.y - other.y);
          const current = Math.hypot(e.clientX - other.x, e.clientY - other.y);
          if (previous > 0 && current > 0) this.zoomAt((e.clientX + other.x) / 2, (e.clientY + other.y) / 2, previous / current);
        }
      } else if (!e.shiftKey) {
        if (planar(this.state.scene)) {
          const h = this.canvas.getBoundingClientRect().height || 1;
          this.change({ center: [this.state.center[0] - dx / h * this.state.scale, this.state.center[1] + dy / h * this.state.scale] });
        } else {
          this.change({ autoRotate: false, camera: {
            ...this.state.camera,
            yaw: this.state.camera.yaw - dx * 0.007,
            pitch: clamp(this.state.camera.pitch + dy * 0.007, this.state.scene === 'landscape' ? 0.3 : -1.4, 1.4),
          } });
        }
      }
      this.pointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
    }, { signal });
    const finishPointer = (e: PointerEvent) => {
      if (this.pointers.has(e.pointerId) && e.type === 'pointerup' && this.pointerTravel < 5 && e.shiftKey && planar(this.state.scene)) {
        this.hooks.onSelectParameter?.(this.pointToComplex(e.clientX, e.clientY));
      }
      this.pointers.delete(e.pointerId);
      if (!this.pointers.size) c.style.cursor = 'grab';
    };
    c.addEventListener('pointerup', finishPointer, { signal });
    c.addEventListener('pointercancel', finishPointer, { signal });
    c.addEventListener('lostpointercapture', finishPointer, { signal });
    c.addEventListener('wheel', e => {
      e.preventDefault();
      const pixels = e.deltaMode === 1 ? e.deltaY * 16 : e.deltaMode === 2 ? e.deltaY * 400 : e.deltaY;
      this.zoomAt(e.clientX, e.clientY, Math.exp(clamp(pixels, -200, 200) * 0.0015));
    }, { signal, passive: false });
    c.addEventListener('keydown', e => {
      if (e.ctrlKey || e.metaKey || e.altKey) return;
      if(volumeScene(this.state.scene)&&['w','a','s','d','q','e'].includes(e.key.toLowerCase())){e.preventDefault();e.stopPropagation();this.fly(e.key.toLowerCase());return;}
      if (['ArrowLeft', 'ArrowRight', 'ArrowUp', 'ArrowDown', '+', '=', '-'].includes(e.key)) {
        e.preventDefault();
        e.stopPropagation();
        if (e.key === '+' || e.key === '=' || e.key === '-') {
          const r = c.getBoundingClientRect();
          this.zoomAt(r.left + r.width / 2, r.top + r.height / 2, e.key === '-' ? 1.2 : 1 / 1.2);
        } else if (planar(this.state.scene)) {
          const step = this.state.scale * 0.06;
          this.change({ center: [
            this.state.center[0] + (e.key === 'ArrowLeft' ? -step : e.key === 'ArrowRight' ? step : 0),
            this.state.center[1] + (e.key === 'ArrowUp' ? step : e.key === 'ArrowDown' ? -step : 0),
          ] });
        } else {
          this.change({ autoRotate: false, camera: {
            ...this.state.camera,
            yaw: this.state.camera.yaw + (e.key === 'ArrowLeft' ? -0.12 : e.key === 'ArrowRight' ? 0.12 : 0),
            pitch: clamp(this.state.camera.pitch + (e.key === 'ArrowUp' ? 0.08 : e.key === 'ArrowDown' ? -0.08 : 0), this.state.scene === 'landscape' ? 0.3 : -1.4, 1.4),
          } });
        }
      }
    }, { signal });
    c.addEventListener('webglcontextlost', e => {
      e.preventDefault();
      this.lost = true;
      this.hooks.onError?.('The graphics context was interrupted. Waiting for the browser to restore it. Your scene is preserved.');
      this.emitStats(0);
    }, { signal });
    c.addEventListener('webglcontextrestored', () => {
      try {
        this.initializeGpu();
        this.resize();
        this.hooks.onError?.('');
        this.schedule();
      } catch (error) { this.hooks.onError?.(`Could not restore the graphics context: ${String(error)}`); }
    }, { signal });
    document.addEventListener('visibilitychange', () => {
      if (document.hidden) { cancelAnimationFrame(this.raf); this.raf = 0; }
      else { this.lastFrame = 0; this.statsStart = performance.now(); this.renderedFrames = 0; this.dirty = true; this.schedule(); }
    }, { signal });
  }

  /** Progressive, cancellable CPU fallback for browsers without WebGL2. */
  private renderCpu() {
    const ctx = this.cpu;
    if (!ctx) return;
    const generation = ++this.cpuGeneration;
    const s = clone(this.state);
    const width = this.canvas.width, height = this.canvas.height;
    const image = ctx.createImageData(width, height);
    const isJulia = s.scene === 'julia';
    let row = 0;
    const chunk = () => {
      if (generation !== this.cpuGeneration || this.disposed) return;
      const end = Math.min(height, row + 10);
      for (; row < end; row++) for (let col = 0; col < width; col++) {
        const x = s.center[0] + (col - width / 2) / height * s.scale;
        const y = s.center[1] + (height / 2 - row) / height * s.scale;
        let zx = isJulia ? x : 0, zy = isJulia ? y : 0;
        const cx = isJulia ? s.julia[0] : x, cy = isJulia ? s.julia[1] : y;
        let n = 0;
        const limit = Math.max(128, Math.min(s.iterations, 768));
        while (n < limit && zx * zx + zy * zy < 256) {
          const xx = zx * zx - zy * zy + cx;
          zy = 2 * zx * zy + cy;
          zx = xx;
          n++;
        }
        const q = (row * width + col) * 4;
        const v = n === limit ? 0.01 : 0.24 + 0.76 * (0.5 + 0.5 * Math.cos(n * 0.19));
        image.data[q] = n === limit ? 5 : Math.round(30 + v * 160);
        image.data[q + 1] = n === limit ? 12 : Math.round(60 + v * 160);
        image.data[q + 2] = n === limit ? 14 : Math.round(64 + v * 148);
        image.data[q + 3] = 255;
      }
      ctx.putImageData(image, 0, 0, 0, Math.max(0, row - 10), width, Math.min(10, row));
      if (row < height) requestAnimationFrame(chunk);
    };
    requestAnimationFrame(chunk);
  }
}
