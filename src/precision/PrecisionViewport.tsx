import { forwardRef, useEffect, useImperativeHandle, useRef, useState } from 'react';
import { DEFAULT_EXACT_VIEW, panExactView, pointAtPixel, zoomExactView } from './coordinates.ts';
import type {
  ExactComplex,
  ExactView,
  PrecisionQuality,
  PrecisionStats,
  PrecisionViewportHandle,
  PrecisionWorkerRequest,
  PrecisionWorkerResponse,
} from './types.ts';

export interface PrecisionViewportProps {
  view: ExactView;
  onViewChange(view: ExactView): void;
  onStats?(stats: PrecisionStats): void;
  onInspect?(point: ExactComplex): void;
  onError?(message: string): void;
  className?: string;
  quality?: PrecisionQuality;
  exposure?: number;
}
interface Gesture {
  view: ExactView;
  x: number;
  y: number;
  distance: number;
  moved: boolean;
  snapshot: HTMLCanvasElement;
  pointerCount: number;
}

/** One canvas and one cancellable worker per viewport, including linked Julia views. */
export const PrecisionViewport = forwardRef<PrecisionViewportHandle, PrecisionViewportProps>(
  function PrecisionViewport(
    {
      view,
      onViewChange,
      onStats,
      onInspect,
      onError,
      className = 'fractal-canvas',
      quality = 'auto',
      exposure = 1,
    },
    ref,
  ) {
    const canvasRef = useRef<HTMLCanvasElement>(null);
    const workerRef = useRef<Worker | null>(null);
    const hooks = useRef({ onViewChange, onStats, onInspect, onError });
    hooks.current = { onViewChange, onStats, onInspect, onError };
    const viewKey = JSON.stringify(view);
    const viewRef = useRef(view);
    const lastPropView = useRef(viewKey);
    if (lastPropView.current !== viewKey) {
      viewRef.current = view;
      lastPropView.current = viewKey;
    }
    const requestId = useRef(0);
    const activeGesture = useRef<Gesture | null>(null);
    const pointers = useRef(new Map<number, { x: number; y: number }>());
    const frameRequest = useRef(0);
    const [size, setSize] = useState({ width: 640, height: 480 });
    const [finishedGesture, setFinishedGesture] = useState(0);
    const tileCanvas = useRef<HTMLCanvasElement | null>(null);
    const reprojectCanvas = useRef<HTMLCanvasElement | null>(null);
    const lastStatsAt = useRef(0);

    function change(next: ExactView) {
      viewRef.current = next;
      cancelAnimationFrame(frameRequest.current);
      frameRequest.current = requestAnimationFrame(() =>
        hooks.current.onViewChange(viewRef.current),
      );
    }
    useImperativeHandle(
      ref,
      () => ({
        capture: () => canvasRef.current?.toDataURL('image/png') ?? '',
        zoom: (multiplier) =>
          change(zoomExactView(viewRef.current, multiplier, 0.5, 0.5, size.width / size.height)),
        reset: () =>
          change({
            ...viewRef.current,
            center:
              viewRef.current.family === 'julia' ? { re: '0', im: '0' } : DEFAULT_EXACT_VIEW.center,
            span: '3.2',
          }),
      }),
      [size],
    );

    useEffect(() => {
      const canvas = canvasRef.current;
      if (!canvas) return;
      const resize = () => {
        const rect = canvas.getBoundingClientRect();
        if (rect.width < 1 || rect.height < 1) return;
        const maxPixels = quality === 'high' ? 1_500_000 : quality === 'low' ? 220_000 : 720_000;
        const dpr = Math.min(window.devicePixelRatio || 1, quality === 'high' ? 2 : 1.25);
        const ratio = Math.min(
          dpr,
          Math.sqrt(maxPixels / (rect.width * rect.height)),
          1800 / Math.max(rect.width, rect.height),
        );
        const next = {
          width: Math.max(32, Math.round(rect.width * ratio)),
          height: Math.max(24, Math.round(rect.height * ratio)),
        };
        setSize((previous) =>
          previous.width === next.width && previous.height === next.height ? previous : next,
        );
      };
      const observer = new ResizeObserver(resize);
      observer.observe(canvas);
      resize();
      return () => observer.disconnect();
    }, [quality]);

    useEffect(() => {
      const fail = (message: string) => {
        hooks.current.onError?.(message);
        hooks.current.onStats?.({
          fps: 0,
          resolution: '—',
          precision: 'Unavailable',
          renderer: 'Precision worker unavailable',
          phase: 'error',
          progress: 0,
          elapsedMs: 0,
          referenceBits: 0,
          repairedPixels: 0,
          precisionDigits: 0,
        });
      };
      let worker: Worker;
      try {
        worker = new Worker(new URL('./renderer.worker.ts', import.meta.url), { type: 'module' });
      } catch (error) {
        fail(
          `The precision renderer could not start. ${error instanceof Error ? error.message : 'This browser could not create a worker.'}`,
        );
        return;
      }
      workerRef.current = worker;
      worker.onmessage = (event: MessageEvent<PrecisionWorkerResponse>) => {
        const message = event.data;
        if (message.id !== requestId.current) return;
        if (message.type === 'error') {
          fail(message.message);
          return;
        }
        if (message.type === 'tile') {
          const canvas = canvasRef.current,
            context = canvas?.getContext('2d', { alpha: false });
          if (!canvas || !context) return;
          const tile = tileCanvas.current ?? document.createElement('canvas');
          tileCanvas.current = tile;
          tile.width = message.width;
          tile.height = message.height;
          const tileContext = tile.getContext('2d', { alpha: false });
          if (!tileContext) return;
          // The constructor accepts an ArrayBuffer-backed clamped array transferred by the worker.
          tileContext.putImageData(
            new ImageData(new Uint8ClampedArray(message.pixels), message.width, message.height),
            0,
            0,
          );
          context.imageSmoothingEnabled = message.frameWidth < canvas.width;
          context.imageSmoothingQuality = 'high';
          const sx = canvas.width / message.frameWidth,
            sy = canvas.height / message.frameHeight;
          context.drawImage(
            tile,
            message.x * sx,
            message.y * sy,
            message.width * sx,
            message.height * sy,
          );
          if (performance.now() - lastStatsAt.current > 90) {
            hooks.current.onStats?.(message.stats);
            lastStatsAt.current = performance.now();
          }
        } else hooks.current.onStats?.(message.stats);
      };
      worker.onerror = (event) => fail(event.message || 'The precision worker could not start.');
      return () => {
        worker.terminate();
        workerRef.current = null;
        cancelAnimationFrame(frameRequest.current);
      };
    }, []);

    useEffect(() => {
      const canvas = canvasRef.current;
      if (!canvas || !workerRef.current || document.hidden) return;
      if (canvas.width !== size.width || canvas.height !== size.height) {
        const previous = document.createElement('canvas');
        previous.width = canvas.width;
        previous.height = canvas.height;
        previous.getContext('2d')?.drawImage(canvas, 0, 0);
        canvas.width = size.width;
        canvas.height = size.height;
        const context = canvas.getContext('2d', { alpha: false });
        if (context) {
          context.fillStyle = '#0a0a09';
          context.fillRect(0, 0, size.width, size.height);
          context.drawImage(previous, 0, 0, size.width, size.height);
        }
      }
      const id = ++requestId.current;
      workerRef.current?.postMessage({ type: 'cancel', id } satisfies PrecisionWorkerRequest);
      hooks.current.onStats?.({
        fps: 0,
        resolution: `${size.width} × ${size.height}`,
        precision: Number(view.span) < 1e-8 ? 'Building reference' : 'Float64',
        renderer: 'Preparing frame',
        phase: 'preview',
        progress: 0,
        elapsedMs: 0,
        referenceBits: 0,
        repairedPixels: 0,
        precisionDigits: 0,
      });
      const timer = window.setTimeout(
        () => {
          if (document.hidden || id !== requestId.current) return;
          workerRef.current?.postMessage({
            type: 'render',
            id,
            view,
            width: size.width,
            height: size.height,
            quality,
            exposure,
          } satisfies PrecisionWorkerRequest);
        },
        activeGesture.current ? 110 : 35,
      );
      return () => clearTimeout(timer);
    }, [viewKey, size, quality, exposure, finishedGesture]);

    useEffect(() => {
      const visibility = () => {
        if (document.hidden) {
          const id = ++requestId.current;
          workerRef.current?.postMessage({ type: 'cancel', id } satisfies PrecisionWorkerRequest);
        } else setFinishedGesture((n) => n + 1);
      };
      document.addEventListener('visibilitychange', visibility);
      return () => document.removeEventListener('visibilitychange', visibility);
    }, []);

    useEffect(() => {
      const canvas = canvasRef.current;
      if (!canvas) return;
      const wheel = (event: WheelEvent) => {
        event.preventDefault();
        const rect = canvas.getBoundingClientRect();
        const delta =
          event.deltaY * (event.deltaMode === 1 ? 16 : event.deltaMode === 2 ? rect.height : 1);
        const multiplier = Math.exp(Math.max(-0.7, Math.min(0.7, delta * 0.0018)));
        const x = (event.clientX - rect.left) / rect.width,
          y = (event.clientY - rect.top) / rect.height;
        const next = zoomExactView(viewRef.current, multiplier, x, y, rect.width / rect.height);
        const context = canvas.getContext('2d', { alpha: false });
        if (context && next.span !== viewRef.current.span) {
          const effectiveMultiplier = Number(next.span) / Number(viewRef.current.span);
          const previous = reprojectCanvas.current ?? document.createElement('canvas');
          reprojectCanvas.current = previous;
          if (previous.width !== canvas.width) previous.width = canvas.width;
          if (previous.height !== canvas.height) previous.height = canvas.height;
          previous.getContext('2d')?.drawImage(canvas, 0, 0);
          context.fillStyle = '#0a0a09';
          context.fillRect(0, 0, canvas.width, canvas.height);
          context.drawImage(
            previous,
            x * canvas.width * (1 - 1 / effectiveMultiplier),
            y * canvas.height * (1 - 1 / effectiveMultiplier),
            canvas.width / effectiveMultiplier,
            canvas.height / effectiveMultiplier,
          );
        }
        change(next);
      };
      canvas.addEventListener('wheel', wheel, { passive: false });
      return () => canvas.removeEventListener('wheel', wheel);
    }, []);

    function startGesture() {
      const canvas = canvasRef.current;
      if (!canvas || !pointers.current.size) return;
      const points = [...pointers.current.values()];
      const x = points.reduce((sum, p) => sum + p.x, 0) / points.length;
      const y = points.reduce((sum, p) => sum + p.y, 0) / points.length;
      const distance =
        points.length > 1 ? Math.hypot(points[0].x - points[1].x, points[0].y - points[1].y) : 1;
      const snapshot = document.createElement('canvas');
      snapshot.width = canvas.width;
      snapshot.height = canvas.height;
      snapshot.getContext('2d')?.drawImage(canvas, 0, 0);
      activeGesture.current = {
        view: viewRef.current,
        x,
        y,
        distance,
        moved: false,
        snapshot,
        pointerCount: points.length,
      };
    }
    return (
      <canvas
        ref={canvasRef}
        className={className}
        tabIndex={0}
        role="img"
        style={{
          touchAction: 'none',
          cursor: activeGesture.current ? 'grabbing' : 'grab',
          background: '#0a0a09',
        }}
        aria-label={`Interactive ${view.family} fractal. Drag to pan. Scroll or pinch to zoom. Arrow keys pan, plus and minus zoom, Home resets. Shift-click a point to inspect it.`}
        aria-keyshortcuts="ArrowUp ArrowDown ArrowLeft ArrowRight + - Home"
        onPointerDown={(event) => {
          if (event.button !== 0 && event.pointerType === 'mouse') return;
          if (pointers.current.size >= 2) return;
          event.currentTarget.focus({ preventScroll: true });
          event.currentTarget.setPointerCapture(event.pointerId);
          pointers.current.set(event.pointerId, { x: event.clientX, y: event.clientY });
          startGesture();
        }}
        onPointerMove={(event) => {
          if (!pointers.current.has(event.pointerId)) return;
          pointers.current.set(event.pointerId, { x: event.clientX, y: event.clientY });
          const gesture = activeGesture.current,
            canvas = canvasRef.current;
          if (!gesture || !canvas) return;
          const rect = canvas.getBoundingClientRect(),
            points = [...pointers.current.values()];
          const x = points.reduce((sum, p) => sum + p.x, 0) / points.length;
          const y = points.reduce((sum, p) => sum + p.y, 0) / points.length;
          const distance =
            points.length > 1
              ? Math.hypot(points[0].x - points[1].x, points[0].y - points[1].y)
              : gesture.distance;
          const multiplier = gesture.distance / Math.max(1, distance);
          const dx = x - gesture.x,
            dy = y - gesture.y;
          gesture.moved ||= Math.hypot(dx, dy) > 3 || points.length > 1;
          const zoomed = zoomExactView(
            gesture.view,
            multiplier,
            (gesture.x - rect.left) / rect.width,
            (gesture.y - rect.top) / rect.height,
            rect.width / rect.height,
          );
          const effectiveMultiplier = Number(zoomed.span) / Number(gesture.view.span);
          change(panExactView(zoomed, dx / rect.height, dy / rect.height));
          const context = canvas.getContext('2d', { alpha: false });
          if (context) {
            context.fillStyle = '#0a0a09';
            context.fillRect(0, 0, canvas.width, canvas.height);
            context.drawImage(
              gesture.snapshot,
              (((gesture.x - rect.left) * canvas.width) / rect.width) *
                (1 - 1 / effectiveMultiplier) +
                (dx * canvas.width) / rect.width,
              (((gesture.y - rect.top) * canvas.height) / rect.height) *
                (1 - 1 / effectiveMultiplier) +
                (dy * canvas.height) / rect.height,
              canvas.width / effectiveMultiplier,
              canvas.height / effectiveMultiplier,
            );
          }
        }}
        onPointerUp={(event) => {
          const gesture = activeGesture.current;
          if (gesture && !gesture.moved && gesture.pointerCount === 1 && event.shiftKey) {
            const rect = event.currentTarget.getBoundingClientRect();
            hooks.current.onInspect?.(
              pointAtPixel(
                viewRef.current,
                (event.clientX - rect.left) / rect.width,
                (event.clientY - rect.top) / rect.height,
                rect.width / rect.height,
              ),
            );
          }
          pointers.current.delete(event.pointerId);
          if (pointers.current.size) startGesture();
          else activeGesture.current = null;
          setFinishedGesture((n) => n + 1);
        }}
        onPointerCancel={(event) => {
          pointers.current.delete(event.pointerId);
          activeGesture.current = null;
          setFinishedGesture((n) => n + 1);
        }}
        onLostPointerCapture={(event) => {
          if (!pointers.current.has(event.pointerId)) return;
          pointers.current.delete(event.pointerId);
          activeGesture.current = null;
          setFinishedGesture((n) => n + 1);
        }}
        onDoubleClick={(event) => {
          const rect = event.currentTarget.getBoundingClientRect();
          change(
            zoomExactView(
              viewRef.current,
              0.35,
              (event.clientX - rect.left) / rect.width,
              (event.clientY - rect.top) / rect.height,
              rect.width / rect.height,
            ),
          );
        }}
        onKeyDown={(event) => {
          if (event.ctrlKey || event.metaKey || event.altKey) return;
          const step = event.shiftKey ? 0.025 : 0.12;
          if (event.key === 'ArrowLeft') change(panExactView(viewRef.current, step, 0));
          else if (event.key === 'ArrowRight') change(panExactView(viewRef.current, -step, 0));
          else if (event.key === 'ArrowUp') change(panExactView(viewRef.current, 0, step));
          else if (event.key === 'ArrowDown') change(panExactView(viewRef.current, 0, -step));
          else if (event.key === '+' || event.key === '=')
            change(zoomExactView(viewRef.current, 0.5));
          else if (event.key === '-') change(zoomExactView(viewRef.current, 2));
          else if (event.key === 'Home')
            change({
              ...viewRef.current,
              center:
                viewRef.current.family === 'julia'
                  ? { re: '0', im: '0' }
                  : DEFAULT_EXACT_VIEW.center,
              span: '3.2',
            });
          else return;
          event.preventDefault();
          event.stopPropagation();
        }}
      />
    );
  },
);
