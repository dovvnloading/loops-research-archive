import { useEffect, useRef, useState } from 'react';
import { Download, Microscope, Play, Square } from 'lucide-react';
import { preparePrecisionFrame } from '../lib/precision';
import type { PrecisionFrame, PrecisionMessage, PrecisionSettings } from '../lib/precision';

const INITIAL: PrecisionSettings = {
  centerRe: '-0.7436438870371510079238', centerIm: '0.1318259042053119704931',
  zoomExponent: 5, iterations: 256, width: 192,
};
const PRESETS = [
  { name: 'Seahorse window', settings: INITIAL },
  { name: 'Seahorse detail', settings: { ...INITIAL, zoomExponent: 7, iterations: 2048, width: 128 } },
  { name: 'Overview · width 1', settings: { ...INITIAL, centerRe: '-0.75', centerIm: '0', zoomExponent: 0, iterations: 256 } },
];
type Phase = 'idle' | 'rendering' | 'complete' | 'cancelled' | 'error';

export function PrecisionStudy() {
  const [settings, setSettings] = useState<PrecisionSettings>(INITIAL);
  const [phase, setPhase] = useState<Phase>('idle');
  const [progress, setProgress] = useState(0);
  const [elapsed, setElapsed] = useState(0);
  const [error, setError] = useState('');
  const [frame, setFrame] = useState<PrecisionFrame | null>(null);
  const [escapeCount, setEscapeCount] = useState<number | null>(null);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const workerRef = useRef<Worker | null>(null);
  const requestId = useRef(0);
  const running = phase === 'rendering';
  const visibleImage = phase !== 'idle' && frame !== null;

  useEffect(() => () => {
    requestId.current++;
    workerRef.current?.terminate();
    workerRef.current = null;
  }, []);

  function stop() {
    requestId.current++;
    workerRef.current?.terminate();
    workerRef.current = null;
    setPhase('cancelled');
  }

  function render() {
    let prepared: PrecisionFrame;
    try { prepared = preparePrecisionFrame(settings); }
    catch (failure) {
      setError(failure instanceof Error ? failure.message : 'Check the render parameters.');
      return;
    }
    const canvas = canvasRef.current;
    if (!canvas) return;
    const context = canvas.getContext('2d');
    if (!context) { setError('This browser could not create a 2D canvas.'); return; }
    workerRef.current?.terminate();
    const id = ++requestId.current;
    canvas.width = prepared.width;
    canvas.height = prepared.height;
    context.fillStyle = '#050b09';
    context.fillRect(0, 0, canvas.width, canvas.height);
    setFrame(prepared); setProgress(0); setElapsed(0); setError(''); setEscapeCount(null); setPhase('rendering');
    try {
      const worker = new Worker(new URL('../workers/precision.worker.ts', import.meta.url), { type: 'module' });
      workerRef.current = worker;
      worker.onmessage = (event: MessageEvent<PrecisionMessage>) => {
        const message = event.data;
        if (message.id !== requestId.current) return;
        if (message.type === 'strip') {
          const data = new Uint8ClampedArray(message.buffer);
          context.putImageData(new ImageData(data, message.width, message.rows), 0, message.y);
          setProgress((message.y + message.rows) / message.height);
          setElapsed(message.elapsedMs);
        } else if (message.type === 'complete') {
          setProgress(1); setElapsed(message.elapsedMs); setEscapeCount(message.escapedPixels); setPhase('complete');
          worker.terminate(); workerRef.current = null;
        } else {
          setError(message.message); setPhase('error'); worker.terminate(); workerRef.current = null;
        }
      };
      worker.onerror = () => {
        if (id !== requestId.current) return;
        setError('The background worker could not complete this render. Try a smaller image or iteration budget.');
        setPhase('error'); worker.terminate(); workerRef.current = null;
      };
      worker.postMessage({ type: 'render', id, settings });
    } catch (failure) {
      setError(failure instanceof Error ? failure.message : 'This browser cannot start a background worker.');
      setPhase('error');
    }
  }

  function exportPng() {
    const canvas = canvasRef.current;
    if (!canvas || phase !== 'complete' || !frame) return;
    canvas.toBlob(blob => {
      if (!blob) { setError('PNG export could not be created.'); return; }
      const url = URL.createObjectURL(blob);
      const link = document.createElement('a');
      link.href = url; link.download = `loops-precision-e${frame.zoomExponent}-${frame.bits}bit.png`;
      document.body.append(link); link.click(); link.remove();
      setTimeout(() => URL.revokeObjectURL(url), 1000);
    }, 'image/png');
  }

  const status = phase === 'rendering' ? `Rendering ${Math.round(progress * 100)}%` : phase === 'complete' ? 'Render complete' : phase === 'cancelled' ? `Cancelled at ${Math.round(progress * 100)}%` : phase === 'error' ? 'Render stopped' : 'Ready to calculate';

  return <section className="precision-study" aria-labelledby="precision-study-title">
    <header className="precision-title">
      <div><span className="eyebrow">PRECISION STUDY / CPU WORKER</span><h3 id="precision-study-title">Past the GPU precision floor.</h3>
        <p>Decimal coordinates, BigInt arithmetic, and a separate rendering worker. Calculate a small Mandelbrot window with up to 60 orders of magnification.</p></div>
      <Microscope size={24} aria-hidden="true" />
    </header>
    <div className="precision-layout">
      <form className="precision-controls" onSubmit={event => { event.preventDefault(); if (!running) render(); }}>
        <label>STUDY PRESET<select aria-label="Precision study preset" disabled={running} defaultValue="custom" onChange={event => {
          const selected = PRESETS.find(preset => preset.name === event.target.value);
          if (selected) { setSettings({ ...selected.settings }); setError(''); }
        }}><option value="custom">Choose a window</option>{PRESETS.map(preset => <option key={preset.name}>{preset.name}</option>)}</select></label>
        <label>REAL CENTER<input aria-label="High precision real center" value={settings.centerRe} maxLength={112} disabled={running} spellCheck={false} autoComplete="off" onChange={event => setSettings({ ...settings, centerRe: event.target.value })} /></label>
        <label>IMAGINARY CENTER<input aria-label="High precision imaginary center" value={settings.centerIm} maxLength={112} disabled={running} spellCheck={false} autoComplete="off" onChange={event => setSettings({ ...settings, centerIm: event.target.value })} /></label>
        <label>WINDOW WIDTH · 10⁻ⁿ<input aria-label="Precision zoom exponent" type="number" min="0" max="60" step="1" value={Number.isNaN(settings.zoomExponent) ? '' : settings.zoomExponent} disabled={running} onChange={event => setSettings({ ...settings, zoomExponent: event.target.value === '' ? NaN : Number(event.target.value) })} /></label>
        <label>ITERATION BUDGET<select aria-label="Precision iteration budget" value={settings.iterations} disabled={running} onChange={event => setSettings({ ...settings, iterations: Number(event.target.value) })}>{[128, 256, 512, 1024, 2048].map(count => <option key={count} value={count}>{count.toLocaleString()} iterations</option>)}</select></label>
        <label>RENDER SIZE<select aria-label="Precision render size" value={settings.width} disabled={running} onChange={event => setSettings({ ...settings, width: Number(event.target.value) })}>{[128, 192, 256].map(width => <option key={width} value={width}>{width} × {width * 3 / 4}</option>)}</select></label>
        <p className="microcopy">Rendering starts only when requested. Large iteration budgets may take a minute; cancel at any time.</p>
        <div className="precision-actions">{running
          ? <button className="research-button secondary" type="button" onClick={stop}><Square size={13} aria-hidden="true" /> Cancel</button>
          : <button className="research-button" type="submit"><Play size={13} aria-hidden="true" /> Render window</button>}
          <button className="research-button secondary" type="button" onClick={exportPng} disabled={phase !== 'complete'} aria-label="Export precision render as PNG"><Download size={14} aria-hidden="true" /> PNG</button>
        </div>
      </form>
      <div className="precision-image">
        <canvas ref={canvasRef} hidden={!visibleImage} aria-label="Progressively rendered high precision Mandelbrot window" role="img" />
        {!visibleImage && <div className="precision-placeholder"><Microscope size={36} aria-hidden="true" /><span>Choose a decimal window.<br />Let the arithmetic reveal its boundary.</span></div>}
        <div className="precision-progress" role="progressbar" aria-label="Precision render progress" aria-valuemin={0} aria-valuemax={100} aria-valuenow={Math.round(progress * 100)}><span style={{ width: `${progress * 100}%` }} /></div>
        <div className="precision-meta"><span role="status" aria-live="polite">{status}</span><span>{frame ? `${frame.bits} BITS · ${frame.width} × ${frame.height} · ${(elapsed / 1000).toFixed(1)}s` : 'ROUNDED FIXED POINT'}</span></div>
        {frame && <div className="precision-meta"><span>≈{frame.decimalDigits} decimal digits of arithmetic resolution</span><span>Width 10⁻{frame.zoomExponent}</span></div>}
        {escapeCount !== null && <div className="precision-meta"><span>{escapeCount.toLocaleString()} of {(frame!.width * frame!.height).toLocaleString()} pixels escaped by {frame!.iterations} iterations</span></div>}
        {error && <p className="precision-error" role="alert">{error}</p>}
      </div>
    </div>
    <p className="precision-caveat">The entered decimals are parsed exactly, then rounded to a binary fixed-point grid. Each orbit operation is rounded. These are numerical images, not interval enclosures or membership proofs. Dark pixels have not escaped within the chosen budget; an insufficient budget can produce a uniform image. More bits cannot recover digits omitted from a chosen center.</p>
  </section>;
}

export default PrecisionStudy;
