import { useEffect, useMemo, useRef, useState } from 'react';
import { ChevronLeft, ChevronRight, Crosshair, Pause, Play, RotateCcw } from 'lucide-react';
import type { EngineState } from '../types';
import { criticalOrbit } from '../lib/math';
import { DownloadButton, formatComplex, Metric, ResearchHeading, ScopeNote, SourceLink } from './common';

type Point = { re: number; im: number; index: number; magnitude: number };
export function orbitPoints(c: [number, number], count = 64): Point[] {
  return criticalOrbit(c, count, Math.max(2, Math.hypot(...c) + 1)).map(p => ({ ...p, magnitude: Math.hypot(p.re, p.im) }));
}

const parameters: { name: string; c: [number, number]; note: string }[] = [
  { name: 'Dendrite', c: [0, 1], note: 'Preperiodic critical orbit' },
  { name: 'Douady rabbit', c: [-0.122561167, 0.744861767], note: 'Approximate period-three center' },
  { name: 'Basilica', c: [-1, 0], note: 'Critical period two' },
  { name: 'Spiral', c: [-0.74543, 0.11301], note: 'Numerical Julia portrait' },
  { name: 'Airplane', c: [-1.754877666, 0], note: 'Approximate period-three center' },
  { name: 'Period 27', c: [-1.786429858055761, 0], note: 'Rounded center; exact bracket in Atlas' },
];

function Preview({ c, mode = 'julia', children, onPick }: { c: [number, number]; mode?: 'julia' | 'parameter'; children?: React.ReactNode; onPick?: (c: [number, number]) => void }) {
  const canvas = useRef<HTMLCanvasElement>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState('');
  const renderRe = mode === 'julia' ? c[0] : 0;
  const renderIm = mode === 'julia' ? c[1] : 0;
  useEffect(() => {
    let worker: Worker;
    try { worker = new Worker(new URL('./preview.worker.ts', import.meta.url), { type: 'module' }); }
    catch { setLoading(false); setError('Preview unavailable. Orbit controls remain available.'); return; }
    const width = mode === 'julia' ? 680 : 280, height = mode === 'julia' ? 520 : 190;
    setLoading(true);
    setError('');
    worker.onerror = event => {
      event.preventDefault();
      setLoading(false);
      setError('Preview unavailable. Orbit controls remain available.');
      worker.terminate();
    };
    worker.onmessage = ({ data }: MessageEvent<{ pixels: Uint8ClampedArray; width: number; height: number }>) => {
      const ctx = canvas.current?.getContext('2d');
      if (ctx) { canvas.current!.width = data.width; canvas.current!.height = data.height; ctx.putImageData(new ImageData(data.pixels as Uint8ClampedArray<ArrayBuffer>, data.width, data.height), 0, 0); }
      setLoading(false);
    };
    worker.postMessage({ id: 1, mode, width, height, c: [renderRe, renderIm] });
    return () => worker.terminate();
  }, [renderRe, renderIm, mode]);
  const selectedX = (c[0] + 2.3) / 3.2 * 100, selectedY = (0.5 - c[1] / 2.2) * 100;
  return <div className={`numerical-preview ${mode}`} aria-busy={loading}>
    <canvas ref={canvas} aria-label={mode === 'parameter' ? 'Mandelbrot parameter plane. Choose a parameter by clicking, or use the real and imaginary input fields.' : 'Numerical Julia set preview for the chosen parameter.'} onClick={event => {
      if (!onPick) return;
      const box = event.currentTarget.getBoundingClientRect();
      onPick([(event.clientX - box.left) / box.width * 3.2 - 2.3, (0.5 - (event.clientY - box.top) / box.height) * 2.2]);
    }} />
    {mode === 'parameter' && selectedX >= 0 && selectedX <= 100 && selectedY >= 0 && selectedY <= 100 && <span className="parameter-crosshair" style={{ left: `${selectedX}%`, top: `${selectedY}%` }}><Crosshair size={18} /></span>}
    {children}
    {loading && <span className="preview-status">Computing preview…</span>}
    {error && <span className="preview-status preview-error" role="status">{error}</span>}
  </div>;
}

export function Dynamics({ state, onChange, onExplore }: { state: EngineState; onChange: (patch: Partial<EngineState>) => void; onExplore: () => void }) {
  const c = state.julia;
  const [iteration, setIteration] = useState(12);
  const [count, setCount] = useState(64);
  const [playing, setPlaying] = useState(false);
  const [showTrail, setShowTrail] = useState(true);
  const points = useMemo(() => orbitPoints(c, count), [c[0], c[1], count]);
  const limit = points.length - 1;
  const active = Math.min(iteration, limit);
  const selected = points[active];
  const escape = points[limit].magnitude > Math.max(2, Math.hypot(...c) + 1);
  useEffect(() => { setIteration(Math.min(12, limit)); setPlaying(false); }, [c[0], c[1], limit]);
  useEffect(() => {
    if (!playing) return;
    const timer = window.setInterval(() => setIteration(n => n >= limit ? 0 : n + 1), 160);
    const pauseHidden = () => { if (document.hidden) setPlaying(false); };
    document.addEventListener('visibilitychange', pauseHidden);
    return () => { clearInterval(timer); document.removeEventListener('visibilitychange', pauseHidden); };
  }, [playing, limit]);
  const project = (p: Point) => [340 + p.re / 3.7 * 680, 260 - p.im / 3.7 * 680];
  const path = points.slice(0, active + 1).map(point => project(point).join(',')).join(' ');
  const [sx, sy] = project(selected);
  const setC = (value: [number, number]) => onChange({ julia: value.map(n => Math.max(-2.5, Math.min(2.5, n))) as [number, number] });
  return <div className="research-content dynamics-workspace">
    <ResearchHeading title="Dynamics workbench" description="The critical orbit of z ↦ z² + c for one parameter, stepped one iteration at a time.">
      <button className="research-button" onClick={() => { onChange({ scene: 'julia', iterations: 256, center: [0, 0], scale: 3.2, autoRotate: false }); onExplore(); }}>Open this Julia set in Explore</button>
    </ResearchHeading>
    <div className="dynamics-layout">
      <section className="research-panel orbit-panel">
        <div className="panel-heading"><h2>Orbit of 0 in the dynamical plane</h2><label className="research-toggle"><input type="checkbox" checked={showTrail} onChange={event => setShowTrail(event.target.checked)} /> Orbit trail</label></div>
        <Preview c={c}>
          <svg className="orbit-overlay" viewBox="0 0 680 520" aria-label={`Critical orbit through iteration ${active}`}>
            <defs><clipPath id="orbit-clip"><rect width="680" height="520" /></clipPath></defs>
            <g clipPath="url(#orbit-clip)">
              <path d="M0 260H680M340 0V520" className="plot-axis" />
              {[1, -1].map(n => <g key={n}><path d={`M${340 + n * 680 / 3.7} 255v10M335 ${260 + n * 680 / 3.7}h10`} className="plot-axis" /><text x={340 + n * 680 / 3.7} y={279} className="plot-label" textAnchor="middle">{n}</text></g>)}
              {showTrail && <polyline points={path} fill="none" stroke="#e3b75f" strokeWidth="1.1" strokeOpacity=".8" />}
              {points.slice(0, active + 1).map((point, index) => { const [x, y] = project(point); return <circle key={index} cx={x} cy={y} r={index === active ? 4.5 : 2} fill={index === active ? '#ffffff' : '#e3b75f'} opacity={index === active ? 1 : 0.85} onClick={() => setIteration(index)}><title>{`z${index} = ${formatComplex(point.re, point.im)}`}</title></circle>; })}
              <circle cx={sx} cy={sy} r="10" fill="none" stroke="#ffffff" />
              <circle cx="340" cy="260" r="3" fill="none" stroke="#ebe7dc" />
            </g>
            <text x="20" y="32" className="plot-label">Im(z)</text><text x="625" y="285" className="plot-label">Re(z)</text>
          </svg>
          <div className="orbit-coordinate"><span>z<sub>{active}</sub></span><code>{formatComplex(selected.re, selected.im)}</code></div>
        </Preview>
        <div className="orbit-transport"><button aria-label="Previous iteration" className="icon-action" onClick={() => { setPlaying(false); setIteration(n => Math.max(0, n - 1)); }}><ChevronLeft size={17} /></button><button aria-label={playing ? 'Pause orbit' : 'Animate orbit'} className="icon-action play-action" onClick={() => setPlaying(!playing)}>{playing ? <Pause size={15} /> : <Play size={15} />}</button><button aria-label="Next iteration" className="icon-action" onClick={() => { setPlaying(false); setIteration(n => Math.min(limit, n + 1)); }}><ChevronRight size={17} /></button><input aria-label="Orbit iteration" type="range" min="0" max={limit} value={active} onChange={event => { setPlaying(false); setIteration(Number(event.target.value)); }} /><span className="transport-count">{String(active).padStart(2, '0')} / {limit}</span></div>
        <div className="metric-row"><Metric label="Parameter" value={formatComplex(...c, 5)} /><Metric label="Orbit" value={escape ? `Escapes at ${limit}` : `Bounded through ${count}`} /><Metric label="Magnitude" value={selected.magnitude.toFixed(6)} /></div>
      </section>
      <aside className="research-panel parameter-panel">
        <div className="panel-heading"><h2>Parameter c</h2><button aria-label="Reset parameter" className="icon-action" onClick={() => setC([-0.74543, 0.11301])}><RotateCcw size={15} /></button></div>
        <Preview c={c} mode="parameter" onPick={setC} />
        <p className="muted micro">Click the plane or enter a value below.</p>
        <div className="number-fields"><label>Real component<input aria-label="Real component of c" type="number" min="-2.5" max="2.5" step="0.0001" value={c[0]} onChange={event => { const value = event.target.valueAsNumber; if (Number.isFinite(value)) setC([value, c[1]]); }} /></label><label>Imaginary component<input aria-label="Imaginary component of c" type="number" min="-2.5" max="2.5" step="0.0001" value={c[1]} onChange={event => { const value = event.target.valueAsNumber; if (Number.isFinite(value)) setC([c[0], value]); }} /></label></div>
        <div className="parameter-presets">{parameters.map(preset => <button key={preset.name} title={preset.note} className={Math.abs(c[0] - preset.c[0]) < 1e-12 && Math.abs(c[1] - preset.c[1]) < 1e-12 ? 'selected' : ''} onClick={() => setC(preset.c)}><span>{preset.name}</span><small>{preset.note}</small></button>)}</div>
        <label className="research-select">Maximum iterations<select value={count} onChange={event => setCount(Number(event.target.value))}><option value="32">32 iterations</option><option value="64">64 iterations</option><option value="128">128 iterations</option><option value="256">256 iterations</option></select></label>
        <DownloadButton data={{ schema: 'loops-numerical-critical-orbit-v1', parameter: c, precision: 'IEEE-754 float64', maximumIterations: count, escapeDetected: escape, points }} name="loops-critical-orbit.json" label="Export orbit" />
      </aside>
    </div>
    <ScopeNote>These are finite numerical orbits and escape-time previews. A bounded orbit at the selected iteration limit is not a proof of membership in the Mandelbrot set. The period-27 preset uses a rounded display coordinate; the Atlas preserves its exact source bracket.</ScopeNote>
    <div className="research-footer-links"><SourceLink path="results/period27_symbolic_marking.json" label="Period-27 certificate" /><SourceLink path="RESEARCH_MAP.md" label="Research map" /></div>
  </div>;
}
