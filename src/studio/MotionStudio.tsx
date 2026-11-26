import { useEffect, useRef, useState } from 'react';
import {
  ArrowDown,
  ArrowUp,
  Camera,
  Check,
  Circle,
  Download,
  Film,
  GripVertical,
  LoaderCircle,
  Pause,
  Play,
  Plus,
  RotateCcw,
  Square,
  Trash2,
  Upload,
  X,
} from 'lucide-react';
import type { EngineState } from '../types';
import { validateState } from '../lib/session';
import { eye, volumeScene } from '../engine/navigation';
import { Dialog, NumberInput, Range } from './UI';
import './motion.css';

export interface MotionKeyframe {
  id: string;
  title: string;
  state: EngineState;
  thumbnail?: string;
}
export interface MotionPath {
  format: 'loops-motion';
  version: 1;
  scene: EngineState['scene'];
  duration: number;
  easing: 'smooth' | 'linear';
  loop: boolean;
  frames: MotionKeyframe[];
}
interface MotionStudioProps {
  state: EngineState;
  onChange: (patch: Partial<EngineState>) => void;
  capture: () => string;
  getCanvas: () => HTMLCanvasElement | null;
  onClose: () => void;
  notify: (message: string) => void;
}
const STORAGE_KEY = 'loops.motion.v1';
const MAX_FRAMES = 8;
const MAX_FILE_SIZE = 3 * 1024 * 1024;
const copy = <T,>(value: T): T => structuredClone(value);
const frameId = () =>
  typeof crypto.randomUUID === 'function'
    ? crypto.randomUUID()
    : `frame-${Date.now()}-${Math.random().toString(36).slice(2)}`;
const clamp = (value: number, min: number, max: number) => Math.max(min, Math.min(max, value));
const lerp = (a: number, b: number, t: number) => a + (b - a) * t;
const angle = (a: number, b: number, t: number, turn = Math.PI * 2) =>
  a + (((((b - a + turn / 2) % turn) + turn) % turn) - turn / 2) * t;
const familyName = (scene: EngineState['scene']) =>
  ({
    mandelbulb: 'Mandelbulb',
    mandelbox: 'Mandelbox',
    quaternion: 'Quaternion Julia',
    mandelbrot: 'Mandelbrot',
    julia: 'Julia set',
    landscape: 'Escape landscape',
  })[scene];

export function validateMotionPath(value: unknown): MotionPath {
  if (!value || typeof value !== 'object') throw new Error('Choose a LOOPS motion path JSON file.');
  const item = value as Record<string, unknown>;
  if (
    item.format !== 'loops-motion' ||
    item.version !== 1 ||
    typeof item.scene !== 'string' ||
    !volumeScene(item.scene as EngineState['scene'])
  )
    throw new Error('This file is not a supported LOOPS 3D motion path.');
  if (!Array.isArray(item.frames) || item.frames.length < 1 || item.frames.length > MAX_FRAMES)
    throw new Error('A path needs between 1 and 8 keyframes.');
  if (
    typeof item.duration !== 'number' ||
    !Number.isFinite(item.duration) ||
    item.duration < 2 ||
    item.duration > 90
  )
    throw new Error('The path duration must be between 2 and 90 seconds.');
  if (item.easing !== 'smooth' && item.easing !== 'linear')
    throw new Error('Choose smooth or linear interpolation.');
  const ids = new Set<string>();
  const frames = item.frames.map((raw: unknown, index): MotionKeyframe => {
    if (!raw || typeof raw !== 'object') throw new Error(`Keyframe ${index + 1} is invalid.`);
    const frame = raw as Record<string, unknown>;
    if (
      !frame.state ||
      typeof frame.state !== 'object' ||
      (frame.state as Record<string, unknown>).scene !== item.scene
    )
      throw new Error('Every keyframe must use the same fractal family.');
    const state = validateState(frame.state);
    const camera = (frame.state as Record<string, unknown>).camera;
    if (
      !camera ||
      typeof camera !== 'object' ||
      !['yaw', 'pitch', 'distance'].every(
        (key) =>
          typeof (camera as Record<string, unknown>)[key] === 'number' &&
          Number.isFinite((camera as Record<string, unknown>)[key]),
      )
    )
      throw new Error(`Keyframe ${index + 1} has invalid camera coordinates.`);
    const position = (camera as Record<string, unknown>).position;
    if (
      position !== undefined &&
      (!Array.isArray(position) ||
        position.length !== 3 ||
        !position.every((n) => typeof n === 'number' && Number.isFinite(n)) ||
        Math.hypot(...position) > 14)
    )
      throw new Error(`Keyframe ${index + 1} has an invalid flight position.`);
    if (
      typeof frame.id !== 'string' ||
      !/^[a-zA-Z0-9_-]{1,100}$/.test(frame.id) ||
      ids.has(frame.id)
    )
      throw new Error('Every keyframe needs a unique identifier.');
    ids.add(frame.id);
    if (typeof frame.title !== 'string' || frame.title.length > 100)
      throw new Error('Keyframe titles must be shorter than 100 characters.');
    const thumbnail =
      typeof frame.thumbnail === 'string' &&
      frame.thumbnail.length < 350_000 &&
      /^data:image\/(png|jpeg|webp);base64,[A-Za-z0-9+/]+=*$/.test(frame.thumbnail)
        ? frame.thumbnail
        : undefined;
    return {
      id: frame.id,
      title: frame.title.trim() || `Keyframe ${index + 1}`,
      state,
      ...(thumbnail ? { thumbnail } : {}),
    };
  });
  return {
    format: 'loops-motion',
    version: 1,
    scene: item.scene as EngineState['scene'],
    duration: item.duration,
    easing: item.easing,
    loop: item.loop === true,
    frames,
  };
}

/** Interpolates numerical settings; palette changes occur at keyframe boundaries. */
export function sampleMotionPath(path: MotionPath, progress: number): EngineState {
  const frames = path.frames;
  if (!frames.length) throw new Error('The motion path has no keyframes.');
  const p = clamp(progress, 0, 1);
  const segments = path.loop ? frames.length : Math.max(1, frames.length - 1);
  const position = p * segments;
  const index = Math.min(frames.length - 1, Math.floor(position));
  const a = frames[index].state;
  const b =
    frames[path.loop ? (index + 1) % frames.length : Math.min(index + 1, frames.length - 1)].state;
  const rawT = p === 1 ? (path.loop ? 1 : 0) : position - index;
  const t = path.easing === 'smooth' ? rawT * rawT * (3 - 2 * rawT) : rawT;
  const result = copy(a);
  result.camera = {
    yaw: angle(a.camera.yaw, b.camera.yaw, t),
    pitch: lerp(a.camera.pitch, b.camera.pitch, t),
    distance: lerp(a.camera.distance, b.camera.distance, t),
  };
  if (a.camera.position || b.camera.position) {
    const from = eye(a.camera),
      to = eye(b.camera);
    result.camera.position = from.map((value, i) => lerp(value, to[i], t)) as [
      number,
      number,
      number,
    ];
  }
  for (const key of ['power', 'bailout', 'detail', 'exposure', 'slice', 'orbitTrap'] as const)
    result[key] = lerp(a[key], b[key], t);
  result.iterations = Math.round(lerp(a.iterations, b.iterations, t));
  result.julia = [lerp(a.julia[0], b.julia[0], t), lerp(a.julia[1], b.julia[1], t)];
  for (const key of Object.keys(a.controls) as (keyof EngineState['controls'])[])
    result.controls[key] = lerp(a.controls[key], b.controls[key], t);
  result.controls.lightAzimuth =
    ((angle(a.controls.lightAzimuth, b.controls.lightAzimuth, t, 360) + 540) % 360) - 180;
  result.controls.bandPhase =
    ((angle(a.controls.bandPhase, b.controls.bandPhase, t) % (Math.PI * 2)) + Math.PI * 2) %
    (Math.PI * 2);
  if (t === 1) result.palette = b.palette;
  result.autoRotate = false;
  result.volumePrecision = 'gpu';
  return result;
}

function initialPath(state: EngineState): { path: MotionPath; error: string | null } {
  try {
    const raw =
      localStorage.getItem(`${STORAGE_KEY}.${state.scene}`) ?? localStorage.getItem(STORAGE_KEY);
    if (raw) {
      const path = validateMotionPath(JSON.parse(raw));
      if (path.scene === state.scene) return { path, error: null };
    }
  } catch {
    return {
      path: newPath(state),
      error:
        'The previous local path could not be restored. You can still create and export a new path.',
    };
  }
  return { path: newPath(state), error: null };
}
function newPath(state: EngineState): MotionPath {
  return {
    format: 'loops-motion',
    version: 1,
    scene: state.scene,
    duration: 12,
    easing: 'smooth',
    loop: false,
    frames: [
      { id: frameId(), title: 'Starting point', state: copy({ ...state, autoRotate: false }) },
    ],
  };
}
function download(content: Blob | string, filename: string) {
  const url = URL.createObjectURL(
    typeof content === 'string' ? new Blob([content], { type: 'application/json' }) : content,
  );
  const anchor = document.createElement('a');
  anchor.href = url;
  anchor.download = filename;
  anchor.click();
  setTimeout(() => URL.revokeObjectURL(url), 2000);
}
function webmType(): string | null {
  if (
    typeof MediaRecorder === 'undefined' ||
    typeof HTMLCanvasElement === 'undefined' ||
    !HTMLCanvasElement.prototype.captureStream
  )
    return null;
  for (const mime of ['video/webm;codecs=vp9', 'video/webm;codecs=vp8', 'video/webm'])
    if (MediaRecorder.isTypeSupported(mime)) return mime;
  return null;
}
function nextPaint(): Promise<void> {
  return new Promise((resolve) =>
    requestAnimationFrame(() => requestAnimationFrame(() => resolve())),
  );
}

interface Recording {
  recorder: MediaRecorder;
  stream: MediaStream;
  chunks: Blob[];
  cancelled: boolean;
  full: boolean;
}
interface Runtime {
  path: MotionPath;
  startedAt: number;
  offset: number;
  repeat: boolean;
}

export function MotionStudio({
  state,
  onChange,
  capture,
  getCanvas,
  onClose,
  notify: notifyParent,
}: MotionStudioProps) {
  const [localNotice, setLocalNotice] = useState('');
  const notify = (message: string) => {
    setLocalNotice(message);
    notifyParent(message);
  };
  const initial = useRef<ReturnType<typeof initialPath> | null>(null);
  if (!initial.current) initial.current = initialPath(state);
  const [path, setPath] = useState(initial.current.path),
    [selected, setSelected] = useState(initial.current.path.frames[0].id);
  const [playing, setPlaying] = useState(false),
    [time, setTime] = useState(0),
    [recording, setRecording] = useState(false),
    [preparing, setPreparing] = useState(false),
    [capturing, setCapturing] = useState(false);
  const [storageError, setStorageError] = useState<string | null>(initial.current.error),
    [activeTab, setActiveTab] = useState<'camera' | 'appearance'>('camera');
  const preview = useRef<HTMLCanvasElement>(null),
    upload = useRef<HTMLInputElement>(null),
    original = useRef(copy(state)),
    current = useRef({ state, onChange, capture, getCanvas, notify });
  current.current = { state, onChange, capture, getCanvas, notify };
  const mounted = useRef(true),
    raf = useRef(0),
    runtime = useRef<Runtime | null>(null),
    elapsed = useRef(0),
    recorder = useRef<Recording | null>(null),
    playingRef = useRef(false),
    preparingRef = useRef(false);
  const lastUI = useRef(0),
    selectedFrame = path.frames.find((frame) => frame.id === selected) ?? path.frames[0];
  const canRecord = webmType();
  const locked = playing || recording || preparing;

  const thumbnail = async (): Promise<string | undefined> => {
    const source = current.current.getCanvas();
    const canvas = document.createElement('canvas');
    canvas.width = 320;
    canvas.height = 180;
    const context = canvas.getContext('2d');
    if (!context) return;
    const paint = (image: CanvasImageSource, width: number, height: number) => {
      context.fillStyle = '#070d15';
      context.fillRect(0, 0, 320, 180);
      const scale = Math.min(320 / width, 180 / height);
      context.drawImage(
        image,
        (320 - width * scale) / 2,
        (180 - height * scale) / 2,
        width * scale,
        height * scale,
      );
      return canvas.toDataURL('image/webp', 0.75);
    };
    try {
      if (source?.width && source.height) return paint(source, source.width, source.height);
      const url = current.current.capture();
      if (!url) return;
      const image = new Image();
      image.src = url;
      await image.decode();
      return paint(image, image.naturalWidth, image.naturalHeight);
    } catch {
      return;
    }
  };

  const finishRecording = (full = false, cancelled = false) => {
    const active = recorder.current;
    if (!active) return;
    active.full = full;
    active.cancelled ||= cancelled;
    if (active.recorder.state !== 'inactive') active.recorder.stop();
    else {
      active.stream.getTracks().forEach((track) => track.stop());
      recorder.current = null;
      if (mounted.current) setRecording(false);
    }
  };
  const pause = () => {
    cancelAnimationFrame(raf.current);
    runtime.current = null;
    playingRef.current = false;
    setPlaying(false);
    if (recorder.current?.recorder.state === 'recording') recorder.current.recorder.pause();
  };
  const stop = (restore = true) => {
    cancelAnimationFrame(raf.current);
    runtime.current = null;
    playingRef.current = false;
    preparingRef.current = false;
    elapsed.current = 0;
    setPlaying(false);
    setPreparing(false);
    setTime(0);
    finishRecording(false);
    if (restore) current.current.onChange(copy(original.current));
  };
  const tick = (timestamp: number) => {
    const run = runtime.current;
    if (!run || !mounted.current) return;
    const total = (timestamp - run.startedAt) / 1000 + run.offset;
    if (total >= run.path.duration && !run.repeat) {
      current.current.onChange(sampleMotionPath(run.path, 1));
      elapsed.current = run.path.duration;
      setTime(run.path.duration);
      setPlaying(false);
      playingRef.current = false;
      runtime.current = null;
      finishRecording(true);
      return;
    }
    const nextTime = run.repeat ? total % run.path.duration : total;
    elapsed.current = nextTime;
    current.current.onChange(sampleMotionPath(run.path, nextTime / run.path.duration));
    if (timestamp - lastUI.current > 70) {
      setTime(nextTime);
      lastUI.current = timestamp;
    }
    raf.current = requestAnimationFrame(tick);
  };
  const play = (recordMode = false) => {
    if (path.frames.length < 2) {
      notify('Add a second keyframe to play the path.');
      return;
    }
    if (playingRef.current) return;
    const offset = elapsed.current >= path.duration ? 0 : elapsed.current;
    runtime.current = {
      path: copy(path),
      startedAt: performance.now(),
      offset,
      repeat: path.loop && !recordMode && !recorder.current,
    };
    playingRef.current = true;
    setPlaying(true);
    if (recorder.current?.recorder.state === 'paused') recorder.current.recorder.resume();
    raf.current = requestAnimationFrame(tick);
  };
  const scrub = (value: number) => {
    if (recording || preparing) return;
    pause();
    elapsed.current = value;
    setTime(value);
    current.current.onChange(sampleMotionPath(path, value / path.duration));
  };

  useEffect(() => {
    mounted.current = true;
    current.current.onChange({
      ...copy(current.current.state),
      volumePrecision: 'gpu',
      autoRotate: false,
    });
    let frame = 0,
      lastPaint = 0;
    const mirror = (timestamp: number) => {
      if (timestamp - lastPaint > 1000 / 24 && preview.current && !document.hidden) {
        const source = current.current.getCanvas(),
          canvas = preview.current,
          context = canvas.getContext('2d', { alpha: false });
        if (source?.width && source.height && context) {
          const width = Math.min(1280, Math.max(640, source.width)),
            height = Math.round((width * 9) / 16);
          if (canvas.width !== width || canvas.height !== height) {
            canvas.width = width;
            canvas.height = height;
          }
          const scale = Math.min(width / source.width, height / source.height);
          context.fillStyle = '#050a10';
          context.fillRect(0, 0, width, height);
          try {
            context.drawImage(
              source,
              (width - source.width * scale) / 2,
              (height - source.height * scale) / 2,
              source.width * scale,
              source.height * scale,
            );
          } catch {
            /* Context recovery is handled by the main renderer. */
          }
        }
        lastPaint = timestamp;
      }
      frame = requestAnimationFrame(mirror);
    };
    frame = requestAnimationFrame(mirror);
    const visibility = () => {
      if (document.hidden && playingRef.current) {
        cancelAnimationFrame(raf.current);
        runtime.current = null;
        playingRef.current = false;
        setPlaying(false);
        if (recorder.current?.recorder.state === 'recording') recorder.current.recorder.pause();
        current.current.notify('Motion paused while this tab is hidden. Press play to resume.');
      }
    };
    document.addEventListener('visibilitychange', visibility);
    return () => {
      mounted.current = false;
      preparingRef.current = false;
      cancelAnimationFrame(frame);
      cancelAnimationFrame(raf.current);
      runtime.current = null;
      playingRef.current = false;
      document.removeEventListener('visibilitychange', visibility);
      const active = recorder.current;
      if (active) {
        active.cancelled = true;
        if (active.recorder.state !== 'inactive') active.recorder.stop();
        active.stream.getTracks().forEach((track) => track.stop());
      }
      current.current.onChange(copy(original.current));
    };
  }, []);

  useEffect(() => {
    const timer = setTimeout(() => {
      try {
        localStorage.setItem(`${STORAGE_KEY}.${path.scene}`, JSON.stringify(path));
        setStorageError(null);
      } catch {
        setStorageError('This browser could not save the path. Export the JSON file to keep it.');
      }
    }, 350);
    return () => clearTimeout(timer);
  }, [path]);
  useEffect(() => {
    if (path.frames.length === 1 && !path.frames[0].thumbnail) {
      let active = true;
      void nextPaint()
        .then(() => (active ? thumbnail() : undefined))
        .then((image) => {
          if (active && image)
            setPath((previous) => ({
              ...previous,
              frames: previous.frames.map((frame, i) =>
                i === 0 && !frame.thumbnail ? { ...frame, thumbnail: image } : frame,
              ),
            }));
        });
      return () => {
        active = false;
      };
    }
  }, []);

  const captureFrame = async (replace = false) => {
    if (locked || capturing) return;
    if (!replace && path.frames.length >= MAX_FRAMES) {
      notify('A motion path can hold up to eight keyframes.');
      return;
    }
    if (state.scene !== path.scene) {
      notify('Keep all keyframes in the same fractal family.');
      return;
    }
    setCapturing(true);
    const captured = copy({ ...state, autoRotate: false });
    try {
      const image = await thumbnail();
      if (!mounted.current) return;
      const id = replace ? selectedFrame.id : frameId();
      setPath((previous) => ({
        ...previous,
        frames: replace
          ? previous.frames.map((frame) =>
              frame.id === id ? { ...frame, state: captured, thumbnail: image } : frame,
            )
          : [
              ...previous.frames,
              {
                id,
                title: `Keyframe ${previous.frames.length + 1}`,
                state: captured,
                thumbnail: image,
              },
            ],
      }));
      setSelected(id);
      notify(
        replace
          ? 'Keyframe updated from the current view.'
          : 'Keyframe captured. Adjust the camera to compose the next view.',
      );
    } finally {
      if (mounted.current) setCapturing(false);
    }
  };
  const selectFrame = (frame: MotionKeyframe, index: number) => {
    if (locked) return;
    pause();
    setSelected(frame.id);
    current.current.onChange({ ...copy(frame.state), autoRotate: false, volumePrecision: 'gpu' });
    const position =
      (index / (path.loop ? path.frames.length : Math.max(1, path.frames.length - 1))) *
      path.duration;
    elapsed.current = position;
    setTime(position);
  };
  const moveFrame = (id: string, direction: number) => {
    setPath((previous) => {
      const frames = [...previous.frames],
        index = frames.findIndex((frame) => frame.id === id),
        next = index + direction;
      if (index < 0 || next < 0 || next >= frames.length) return previous;
      [frames[index], frames[next]] = [frames[next], frames[index]];
      return { ...previous, frames };
    });
    elapsed.current = 0;
    setTime(0);
  };
  const removeFrame = (id: string) => {
    if (path.frames.length < 2) return;
    const frames = path.frames.filter((frame) => frame.id !== id);
    setPath({ ...path, frames });
    if (selected === id) setSelected(frames[0].id);
    elapsed.current = 0;
    setTime(0);
  };
  const updateCamera = (patch: Partial<EngineState['camera']>) =>
    current.current.onChange({
      camera: { ...current.current.state.camera, ...patch },
      autoRotate: false,
      volumePrecision: 'gpu',
    });
  const updateControls = (patch: Partial<EngineState['controls']>) =>
    current.current.onChange({
      controls: { ...current.current.state.controls, ...patch },
      autoRotate: false,
      volumePrecision: 'gpu',
    });
  const startRecording = async () => {
    if (!canRecord || path.frames.length < 2 || recording || preparing) return;
    pause();
    elapsed.current = 0;
    setTime(0);
    preparingRef.current = true;
    setPreparing(true);
    current.current.onChange(sampleMotionPath(path, 0));
    try {
      await nextPaint();
      if (!mounted.current || !preparingRef.current) return;
      const canvas = current.current.getCanvas();
      if (!canvas?.width) throw new Error('The render canvas is not ready yet.');
      const stream = canvas.captureStream(24);
      let mediaRecorder: MediaRecorder;
      try {
        mediaRecorder = new MediaRecorder(stream, {
          mimeType: canRecord,
          videoBitsPerSecond: 8_000_000,
        });
      } catch (error) {
        stream.getTracks().forEach((track) => track.stop());
        throw error;
      }
      const active: Recording = {
        recorder: mediaRecorder,
        stream,
        chunks: [],
        cancelled: false,
        full: false,
      };
      recorder.current = active;
      mediaRecorder.ondataavailable = (event) => {
        if (event.data.size) active.chunks.push(event.data);
      };
      mediaRecorder.onerror = () => {
        active.cancelled = true;
        if (mounted.current) {
          notify(
            'The browser stopped recording. Try a lower rendering quality or export the path.',
          );
          stop(false);
        }
      };
      mediaRecorder.onstop = () => {
        active.stream.getTracks().forEach((track) => track.stop());
        if (recorder.current === active) recorder.current = null;
        if (mounted.current) setRecording(false);
        if (!active.cancelled && active.chunks.length && mounted.current) {
          const blob = new Blob(active.chunks, { type: active.recorder.mimeType || 'video/webm' });
          download(
            blob,
            `loops-${path.scene}-${active.full ? 'motion' : 'clip'}-${Date.now()}.webm`,
          );
          notify(
            active.full
              ? 'Motion recorded and downloaded as WebM.'
              : 'Your recorded clip has been downloaded.',
          );
        }
        active.chunks = [];
      };
      mediaRecorder.start(500);
      setRecording(true);
      preparingRef.current = false;
      setPreparing(false);
      play(true);
    } catch (error) {
      preparingRef.current = false;
      setPreparing(false);
      notify(error instanceof Error ? error.message : 'Recording is unavailable in this browser.');
    }
  };
  const importFile = async (file?: File) => {
    if (!file) return;
    try {
      if (file.size > MAX_FILE_SIZE) throw new Error('Choose a motion path smaller than 3 MB.');
      const next = validateMotionPath(JSON.parse(await file.text()));
      if (next.scene !== path.scene)
        throw new Error(
          `This path uses ${familyName(next.scene)}. Open that family before importing it.`,
        );
      stop(false);
      setPath(next);
      setSelected(next.frames[0].id);
      current.current.onChange({
        ...copy(next.frames[0].state),
        autoRotate: false,
        volumePrecision: 'gpu',
      });
      notify(`Imported ${next.frames.length} keyframes.`);
    } catch (error) {
      notify(error instanceof Error ? error.message : 'Could not import this motion path.');
    } finally {
      if (upload.current) upload.current.value = '';
    }
  };
  const drag = useRef<{ x: number; y: number; camera: EngineState['camera'] } | null>(null);

  return (
    <Dialog
      title="Motion studio"
      kicker="A PATH THROUGH INFINITY"
      onClose={onClose}
      className="ob-motion"
    >
      <div className="ob-motion-intro">
        <p>Compose a sequence of views. Let the mathematics unfold.</p>
        <span>
          {familyName(path.scene)} <i /> {path.frames.length} / {MAX_FRAMES} keyframes
        </span>
      </div>
      <div className="ob-motion-body">
        <div className="ob-motion-main">
          <div className={`ob-motion-view ${locked ? 'is-playing' : ''}`}>
            <canvas
              ref={preview}
              role="img"
              aria-label="Live preview of the current fractal. Drag to rotate the camera."
              onPointerDown={(event) => {
                if (locked) return;
                event.currentTarget.setPointerCapture(event.pointerId);
                drag.current = { x: event.clientX, y: event.clientY, camera: copy(state.camera) };
              }}
              onPointerMove={(event) => {
                if (!drag.current || locked) return;
                updateCamera({
                  ...drag.current.camera,
                  yaw: drag.current.camera.yaw + (event.clientX - drag.current.x) * 0.006,
                  pitch: clamp(
                    drag.current.camera.pitch + (event.clientY - drag.current.y) * 0.006,
                    -1.4,
                    1.4,
                  ),
                });
              }}
              onPointerUp={() => {
                drag.current = null;
              }}
              onPointerCancel={() => {
                drag.current = null;
              }}
            />
            <div className="ob-motion-view-top">
              <span>
                <i className={recording ? 'is-recording' : ''} />
                {recording
                  ? playing
                    ? 'RECORDING'
                    : 'RECORDING PAUSED'
                  : playing
                    ? 'PLAYBACK'
                    : 'LIVE PREVIEW'}
              </span>
              <code>
                {time.toFixed(1).padStart(4, '0')} / {path.duration.toFixed(1)} s
              </code>
            </div>
            {!locked && <span className="ob-motion-view-hint">Drag to compose the camera</span>}
          </div>
          <div className="ob-motion-transport">
            <button
              onClick={() => (playing ? pause() : play())}
              disabled={path.frames.length < 2 || preparing}
              aria-label={playing ? 'Pause path' : 'Play path'}
              className="ob-motion-play"
            >
              {playing ? (
                <Pause size={17} fill="currentColor" />
              ) : (
                <Play size={17} fill="currentColor" />
              )}
            </button>
            <button
              onClick={() => stop()}
              aria-label="Stop and restore the original view"
              title="Stop and restore original view"
            >
              <Square size={14} />
            </button>
            <input
              type="range"
              min={0}
              max={path.duration}
              step={0.01}
              value={time}
              onChange={(event) => scrub(Number(event.target.value))}
              disabled={recording || preparing || path.frames.length < 2}
              aria-label="Scrub along the motion path"
            />
            <code>{time.toFixed(1)}s</code>
            <button
              onClick={() => setPath((previous) => ({ ...previous, loop: !previous.loop }))}
              disabled={locked}
              className={path.loop ? 'is-active' : ''}
              aria-pressed={path.loop}
              aria-label="Close and repeat the path"
              title="Close path and loop"
            >
              <RotateCcw size={16} />
            </button>
          </div>
          <div className="ob-motion-frames-heading">
            <span>KEYFRAMES</span>
            <button
              onClick={() => void captureFrame()}
              disabled={locked || capturing || path.frames.length >= MAX_FRAMES}
            >
              {capturing ? (
                <LoaderCircle className="ob-motion-spin" size={13} />
              ) : (
                <Plus size={14} />
              )}{' '}
              Capture current view
            </button>
          </div>
          <div className="ob-motion-frames">
            {path.frames.map((frame, index) => (
              <article key={frame.id} className={selected === frame.id ? 'is-selected' : ''}>
                <button
                  className="ob-motion-frame-preview"
                  onClick={() => selectFrame(frame, index)}
                  disabled={locked}
                  aria-label={`Load keyframe ${index + 1}: ${frame.title}`}
                >
                  {frame.thumbnail ? (
                    <img src={frame.thumbnail} alt="" />
                  ) : (
                    <Camera size={22} strokeWidth={1} />
                  )}
                  <span>{String(index + 1).padStart(2, '0')}</span>
                </button>
                <div className="ob-motion-frame-text">
                  <input
                    value={frame.title}
                    maxLength={100}
                    disabled={locked}
                    aria-label={`Name of keyframe ${index + 1}`}
                    onChange={(event) =>
                      setPath((previous) => ({
                        ...previous,
                        frames: previous.frames.map((item) =>
                          item.id === frame.id ? { ...item, title: event.target.value } : item,
                        ),
                      }))
                    }
                  />
                  <code>
                    {frame.state.camera.position ? 'FLIGHT' : 'ORBIT'} ·{' '}
                    {(frame.state.camera.position
                      ? Math.hypot(...frame.state.camera.position)
                      : frame.state.camera.distance
                    ).toFixed(2)}
                  </code>
                </div>
                <div className="ob-motion-frame-actions">
                  <button
                    aria-label={`Move keyframe ${index + 1} earlier`}
                    disabled={locked || index === 0}
                    onClick={() => moveFrame(frame.id, -1)}
                  >
                    <ArrowUp size={12} />
                  </button>
                  <button
                    aria-label={`Move keyframe ${index + 1} later`}
                    disabled={locked || index === path.frames.length - 1}
                    onClick={() => moveFrame(frame.id, 1)}
                  >
                    <ArrowDown size={12} />
                  </button>
                  <button
                    aria-label={`Remove keyframe ${index + 1}`}
                    disabled={locked || path.frames.length === 1}
                    onClick={() => removeFrame(frame.id)}
                  >
                    <Trash2 size={12} />
                  </button>
                </div>
              </article>
            ))}
          </div>
          <div className="ob-motion-compose-tip">
            <Camera size={14} />
            <p>
              Move the camera in the preview, adjust its settings, then capture the next keyframe.
              Use <strong>Update selected</strong> to refine an existing view.
            </p>
          </div>
        </div>
        <aside className="ob-motion-sidebar">
          <div
            className="ob-motion-tabs"
            role="tablist"
            aria-label="Keyframe settings"
            onKeyDown={(event) => {
              if (!['ArrowLeft', 'ArrowRight', 'Home', 'End'].includes(event.key)) return;
              event.preventDefault();
              const next =
                event.key === 'Home'
                  ? 'camera'
                  : event.key === 'End'
                    ? 'appearance'
                    : activeTab === 'camera'
                      ? 'appearance'
                      : 'camera';
              setActiveTab(next);
              event.currentTarget.querySelector<HTMLButtonElement>(`#motion-${next}-tab`)?.focus();
            }}
          >
            <button
              id="motion-camera-tab"
              role="tab"
              aria-selected={activeTab === 'camera'}
              tabIndex={activeTab === 'camera' ? 0 : -1}
              aria-controls="motion-settings-panel"
              onClick={() => setActiveTab('camera')}
            >
              Camera
            </button>
            <button
              id="motion-appearance-tab"
              role="tab"
              aria-selected={activeTab === 'appearance'}
              tabIndex={activeTab === 'appearance' ? 0 : -1}
              aria-controls="motion-settings-panel"
              onClick={() => setActiveTab('appearance')}
            >
              Appearance
            </button>
          </div>
          <fieldset
            id="motion-settings-panel"
            role="tabpanel"
            aria-labelledby={`motion-${activeTab}-tab`}
            disabled={locked}
          >
            {activeTab === 'camera' ? (
              <>
                <Range
                  label="Yaw"
                  value={(((((state.camera.yaw * 180) / Math.PI) % 360) + 540) % 360) - 180}
                  min={-180}
                  max={180}
                  step={0.5}
                  format={(value) => `${value.toFixed(0)}°`}
                  onChange={(value) => updateCamera({ yaw: (value * Math.PI) / 180 })}
                />
                <Range
                  label="Pitch"
                  value={(state.camera.pitch * 180) / Math.PI}
                  min={-80}
                  max={80}
                  step={0.5}
                  format={(value) => `${value.toFixed(0)}°`}
                  onChange={(value) => updateCamera({ pitch: (value * Math.PI) / 180 })}
                />
                {!state.camera.position ? (
                  <Range
                    label="Orbit distance"
                    value={state.camera.distance}
                    min={1.65}
                    max={14}
                    step={0.01}
                    format={(value) => value.toFixed(2)}
                    onChange={(value) => updateCamera({ distance: value })}
                  />
                ) : (
                  <div className="ob-motion-flight">
                    <span>Flight position</span>
                    {(['x', 'y', 'z'] as const).map((axis, index) => (
                      <NumberInput
                        key={axis}
                        label={axis.toUpperCase()}
                        value={state.camera.position![index]}
                        min={-14}
                        max={14}
                        step={0.001}
                        onChange={(value) => {
                          const position = [...state.camera.position!] as [number, number, number];
                          position[index] = value;
                          const magnitude = Math.hypot(...position);
                          updateCamera({
                            position:
                              magnitude > 14
                                ? (position.map((n) => (n / magnitude) * 14) as [
                                    number,
                                    number,
                                    number,
                                  ])
                                : position,
                          });
                        }}
                      />
                    ))}
                    <button
                      className="ob-motion-text-button"
                      onClick={() => updateCamera({ position: undefined })}
                    >
                      Return to orbit camera
                    </button>
                  </div>
                )}
                <Range
                  label="Field of view"
                  value={state.controls.fov}
                  min={20}
                  max={95}
                  step={0.5}
                  format={(value) => `${value.toFixed(1)}°`}
                  onChange={(value) => updateControls({ fov: value })}
                />
              </>
            ) : (
              <>
                {state.scene !== 'quaternion' ? (
                  <Range
                    label="Power"
                    value={state.power}
                    min={state.scene === 'mandelbox' ? 1.2 : 2}
                    max={state.scene === 'mandelbox' ? 3 : 16}
                    step={0.05}
                    format={(value) => value.toFixed(2)}
                    onChange={(value) =>
                      onChange({ power: value, autoRotate: false, volumePrecision: 'gpu' })
                    }
                  />
                ) : (
                  <div className="ob-motion-quaternion">
                    <NumberInput
                      label="Julia parameter · real"
                      value={state.julia[0]}
                      min={-4}
                      max={4}
                      step={0.01}
                      onChange={(value) =>
                        onChange({ julia: [value, state.julia[1]], volumePrecision: 'gpu' })
                      }
                    />
                    <NumberInput
                      label="Julia parameter · imaginary"
                      value={state.julia[1]}
                      min={-4}
                      max={4}
                      step={0.01}
                      onChange={(value) =>
                        onChange({ julia: [state.julia[0], value], volumePrecision: 'gpu' })
                      }
                    />
                  </div>
                )}
                <Range
                  label="Exposure"
                  value={state.exposure}
                  min={0.2}
                  max={3}
                  step={0.01}
                  format={(value) => `${value.toFixed(2)}×`}
                  onChange={(value) => onChange({ exposure: value })}
                />
                <Range
                  label="Light azimuth"
                  value={state.controls.lightAzimuth}
                  min={-180}
                  max={180}
                  step={1}
                  format={(value) => `${value.toFixed(0)}°`}
                  onChange={(value) => updateControls({ lightAzimuth: value })}
                />
                <Range
                  label="Light elevation"
                  value={state.controls.lightElevation}
                  min={5}
                  max={85}
                  step={1}
                  format={(value) => `${value.toFixed(0)}°`}
                  onChange={(value) => updateControls({ lightElevation: value })}
                />
                {state.scene === 'quaternion' && (
                  <Range
                    label="Fourth-dimensional slice"
                    value={state.slice}
                    min={-2}
                    max={2}
                    step={0.01}
                    format={(value) => value.toFixed(2)}
                    onChange={(value) => onChange({ slice: value })}
                  />
                )}
              </>
            )}
            <button
              className="ob-motion-update"
              onClick={() => void captureFrame(true)}
              disabled={capturing}
            >
              <Check size={14} /> Update selected keyframe
            </button>
            <div className="ob-motion-timing">
              <h3>PATH SETTINGS</h3>
              <NumberInput
                label="Total duration · seconds"
                value={path.duration}
                min={2}
                max={90}
                step={1}
                onChange={(duration) => {
                  setPath((previous) => ({ ...previous, duration }));
                  elapsed.current = 0;
                  setTime(0);
                }}
              />
              <label className="ob-motion-select">
                <span>Interpolation</span>
                <select
                  value={path.easing}
                  onChange={(event) =>
                    setPath((previous) => ({
                      ...previous,
                      easing: event.target.value as MotionPath['easing'],
                    }))
                  }
                >
                  <option value="smooth">Ease at each keyframe</option>
                  <option value="linear">Constant segment speed</option>
                </select>
              </label>
              <p>
                {path.loop
                  ? 'The final segment returns to the first keyframe. Recording exports one complete loop.'
                  : 'Keyframes are evenly spaced across the duration.'}
              </p>
            </div>
          </fieldset>
        </aside>
      </div>
      {localNotice && (
        <div className="ob-motion-notice" role="status">
          <span>{localNotice}</span>
          <button onClick={() => setLocalNotice('')} aria-label="Dismiss motion status">
            <X size={14} />
          </button>
        </div>
      )}
      <div className="ob-motion-footnote">
        <span>
          Motion uses the GPU renderer. Camera paths are interpolated and can cross surfaces.
          Palette changes occur at keyframes.
        </span>
        {storageError ? (
          <span className="ob-motion-error">{storageError}</span>
        ) : (
          <span>
            <Check size={11} /> Path saved in this browser
          </span>
        )}
      </div>
      <footer className="ob-motion-footer">
        <div>
          <button onClick={() => upload.current?.click()} disabled={locked}>
            <Upload size={14} /> Import path
          </button>
          <button
            onClick={() =>
              download(JSON.stringify(path, null, 2), `loops-${path.scene}-motion.json`)
            }
          >
            <Download size={14} /> Export JSON
          </button>
        </div>
        <div>
          <span className="ob-motion-record-help">
            {canRecord
              ? '24 fps capture · WebM'
              : 'WebM recording is unavailable in this browser. Export JSON to replay the path.'}
          </span>
          <button
            className={`ob-motion-record ${recording ? 'is-recording' : ''}`}
            onClick={() => (recording ? stop(false) : void startRecording())}
            disabled={!canRecord || path.frames.length < 2 || preparing || (playing && !recording)}
          >
            {preparing ? (
              <LoaderCircle size={14} className="ob-motion-spin" />
            ) : recording ? (
              <Square size={13} fill="currentColor" />
            ) : (
              <Circle size={13} fill="currentColor" />
            )}
            {preparing ? 'Preparing…' : recording ? 'Finish recording' : 'Record WebM'}
          </button>
        </div>
      </footer>
      <input
        ref={upload}
        type="file"
        accept="application/json,.json"
        hidden
        onChange={(event) => void importFile(event.target.files?.[0])}
        aria-label="Import motion path"
      />
    </Dialog>
  );
}
