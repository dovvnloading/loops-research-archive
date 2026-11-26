import { useEffect, useRef, useState } from 'react';
import {
  ArrowUpRight,
  Check,
  Copy,
  Download,
  Image,
  Link,
  FileJson,
  X,
  Loader2,
} from 'lucide-react';
import { createSnapshotURL } from '../journal/codec';
import type { JournalPayload } from '../journal/types';
import { pngWithMetadata, saveBlob } from './png';
import { Dialog } from './UI';
export function ExportDialog({
  payload,
  capture,
  aspect,
  onClose,
}: {
  payload: JournalPayload;
  capture: () => string;
  aspect: number;
  onClose: () => void;
}) {
  const [tab, setTab] = useState<'image' | 'session' | 'share'>('image'),
    [size, setSize] = useState('1920'),
    [progress, setProgress] = useState<number | null>(null),
    [error, setError] = useState(''),
    [done, setDone] = useState(false),
    [copied, setCopied] = useState(false);
  const worker = useRef<Worker | null>(null),
    generation = useRef(0),
    output = useRef<HTMLCanvasElement | null>(null);
  const link = createSnapshotURL(payload);
  const landscape = payload.engine.scene === 'landscape';
  useEffect(
    () => () => {
      generation.current++;
      worker.current?.terminate();
    },
    [],
  );
  const stop = () => {
    generation.current++;
    worker.current?.terminate();
    worker.current = null;
    setProgress(null);
  };
  async function complete(canvas: HTMLCanvasElement, id: number) {
    const blob = await new Promise<Blob>((resolve, reject) =>
      canvas.toBlob(
        (b) => (b ? resolve(b) : reject(new Error('The image could not be encoded.'))),
        'image/png',
      ),
    );
    if (id !== generation.current) return;
    const metadata = {
      format: 'loops-image',
      version: 2,
      createdAt: new Date().toISOString(),
      width: canvas.width,
      height: canvas.height,
      arithmetic: 'Numerical finite-iteration rendering; not a membership certificate',
      ...payload,
    };
    const bytes = pngWithMetadata(new Uint8Array(await blob.arrayBuffer()), metadata);
    if (id !== generation.current) return;
    saveBlob(
      new Blob([bytes.buffer as ArrayBuffer], { type: 'image/png' }),
      `loops-${payload.engine.scene}-${canvas.width}x${canvas.height}.png`,
    );
    setDone(true);
    setProgress(null);
    worker.current?.terminate();
    worker.current = null;
  }
  const render = async () => {
    setError('');
    setDone(false);
    const id = ++generation.current;
    try {
      if (size === 'current' || landscape) {
        const image = capture();
        if (!image) throw new Error('Open the explorer and allow the view to render first.');
        const img = new window.Image();
        img.src = image;
        await img.decode();
        const canvas = document.createElement('canvas');
        canvas.width = img.naturalWidth;
        canvas.height = img.naturalHeight;
        canvas.getContext('2d')!.drawImage(img, 0, 0);
        await complete(canvas, id);
        return;
      }
      const longEdge = Number(size),
        ratio = Math.max(0.25, Math.min(4, aspect || 1.5));
      const width = Math.round(ratio >= 1 ? longEdge : longEdge * ratio),
        height = Math.round(ratio >= 1 ? longEdge / ratio : longEdge);
      const canvas = document.createElement('canvas');
      canvas.width = width;
      canvas.height = height;
      output.current = canvas;
      const context = canvas.getContext('2d', { alpha: false })!;
      context.fillStyle = '#070b12';
      context.fillRect(0, 0, width, height);
      setProgress(0);
      worker.current?.terminate();
      const task = new Worker(new URL('./export.worker.ts', import.meta.url), { type: 'module' });
      worker.current = task;
      task.onmessage = (event: MessageEvent) => {
        const data = event.data;
        if (data.id !== generation.current) return;
        if (data.type === 'tile') {
          context.putImageData(
            new ImageData(new Uint8ClampedArray(data.pixels), data.width, data.height),
            0,
            data.y,
          );
          setProgress(data.progress);
        }
        if (data.type === 'error') {
          setError(data.message);
          stop();
        }
        if (data.type === 'complete')
          void complete(canvas, id).catch((e) => {
            setError((e as Error).message);
            stop();
          });
      };
      task.onerror = () => {
        setError('The export worker stopped unexpectedly. Try a smaller image.');
        stop();
      };
      task.postMessage({ type: 'render', id, payload, width, height });
    } catch (e) {
      setError((e as Error).message);
      setProgress(null);
    }
  };
  const copy = async () => {
    try {
      await navigator.clipboard.writeText(link);
      setCopied(true);
    } catch {
      setError('Copy the link from the field below.');
    }
  };
  return (
    <Dialog
      title="Take a little infinity with you."
      kicker="EXPORT & SHARE"
      onClose={onClose}
      className="ob-export-dialog"
    >
      <div className="ob-segments">
        {(
          [
            { id: 'image', label: 'Image', Icon: Image },
            { id: 'session', label: 'Session', Icon: FileJson },
            { id: 'share', label: 'Share link', Icon: Link },
          ] as const
        ).map(({ id, label, Icon }) => (
          <button key={id} className={tab === id ? 'active' : ''} onClick={() => setTab(id)}>
            <Icon size={15} />
            {label}
          </button>
        ))}
      </div>
      {tab === 'image' && (
        <>
          <p className="ob-dialog-intro">
            Render the current mathematical view as a PNG. Exact parameters and research provenance
            are embedded in the file.
          </p>
          <label className="ob-field">
            <span>Image size · longest edge</span>
            <select
              value={landscape ? 'current' : size}
              disabled={progress !== null || landscape}
              onChange={(e) => setSize(e.target.value)}
            >
              <option value="current">Current viewport</option>
              <option value="1200">1,200 px · quick export</option>
              <option value="1920">1,920 px · full HD</option>
              <option value="3840">3,840 px · 4K</option>
            </select>
          </label>
          <p className="ob-micro">
            {landscape
              ? 'The escape landscape exports its current rendered viewport.'
              : 'A separate worker renders the image while the explorer stays responsive. Detailed or deep views can take longer. You can cancel at any time.'}
          </p>
          {progress !== null ? (
            <div className="ob-export-progress">
              <div>
                <span>Rendering your image</span>
                <strong>{Math.round(progress * 100)}%</strong>
              </div>
              <progress value={progress} max={1} />
              <button className="ob-button ob-subtle" onClick={stop}>
                <X size={14} />
                Cancel render
              </button>
            </div>
          ) : (
            <button className="ob-button ob-primary ob-wide" onClick={() => void render()}>
              {done ? <Check size={16} /> : <Download size={16} />}{' '}
              {done ? 'Render another image' : 'Render & download PNG'}
            </button>
          )}
        </>
      )}
      {tab === 'session' && (
        <>
          <p className="ob-dialog-intro">
            A portable record of the full engine state, exact coordinates, iteration budget,
            palette, and source revision. Reopen it with the import command in Explore.
          </p>
          <div className="ob-export-file">
            <FileJson size={32} />
            <div>
              <strong>LOOPS session · version 2</strong>
              <small>{payload.engine.scene} · lossless decimal coordinates</small>
            </div>
          </div>
          <button
            className="ob-button ob-primary ob-wide"
            onClick={() =>
              saveBlob(
                new Blob(
                  [JSON.stringify({ format: 'loops-session', version: 2, payload }, null, 2)],
                  { type: 'application/json' },
                ),
                'loops-session.json',
              )
            }
          >
            <Download size={16} />
            Download session
          </button>
        </>
      )}
      {tab === 'share' && (
        <>
          <p className="ob-dialog-intro">
            The link stores the mathematical view, including exact coordinates. Anyone who can
            access this site can reopen it. Journal notes stay in your browser.
          </p>
          <label className="ob-field">
            <span>Reproducible view link</span>
            <textarea rows={4} readOnly value={link} onFocus={(e) => e.target.select()} />
          </label>
          <button className="ob-button ob-primary ob-wide" onClick={() => void copy()}>
            {copied ? <Check size={16} /> : <Copy size={16} />}{' '}
            {copied ? 'Link copied' : 'Copy view link'}
          </button>
        </>
      )}
      {error && (
        <p className="ob-inline-error" role="alert">
          {error}
        </p>
      )}
      <p className="ob-export-foot">
        {payload.sourceRevision
          ? `Research revision ${payload.sourceRevision.slice(0, 8)}`
          : 'Local numerical exploration'}
        <span>LOOPS / An atlas of infinity</span>
      </p>
    </Dialog>
  );
}
