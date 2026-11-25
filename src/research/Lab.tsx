import { useEffect, useMemo, useRef, useState } from 'react';
import { ArrowRight, Binary, FlaskConical, Focus, Waves } from 'lucide-react';
import type { EngineState } from '../types';
import { PrecisionStudy } from '../components/PrecisionStudy';
import { criticalOrbit } from '../lib/math';
import { DownloadButton, Metric, ResearchHeading, ScopeNote, SourceLink } from './common';

function RealSlice({ state, onChange, onExplore }: { state: EngineState; onChange: (patch: Partial<EngineState>) => void; onExplore: () => void }) {
  const canvas = useRef<HTMLCanvasElement>(null);
  const [windowIndex, setWindowIndex] = useState(0);
  const windows = [{ name: 'Full real slice', min: -2, max: .25 }, { name: 'Period-doubling cascade', min: -1.5, max: -.7 }, { name: 'Airplane window', min: -1.81, max: -1.72 }];
  const window = windows[windowIndex];
  const c = state.julia[0];
  const orbit = useMemo(() => criticalOrbit([c, 0], 1024, 4), [c]);
  const tail = orbit.slice(-64);
  const escape = Boolean(orbit.at(-1)?.escaped);
  const candidate = useMemo(() => {
    if (escape || orbit.length < 1025) return null;
    for (let period = 1; period <= 32; period++) if (tail.slice(period).every((point, index) => Math.abs(point.re - tail[index].re) < 1e-7)) return period;
    return null;
  }, [orbit, tail, escape]);
  useEffect(() => {
    const ctx = canvas.current?.getContext('2d'); if (!ctx) return;
    const width = 1100, height = 450;
    canvas.current!.width = width; canvas.current!.height = height;
    const image = ctx.createImageData(width, height);
    for (let p = 0; p < image.data.length; p += 4) { image.data[p] = 11; image.data[p + 1] = 18; image.data[p + 2] = 19; image.data[p + 3] = 255; }
    for (let x = 0; x < width; x++) {
      const parameter = window.min + x / (width - 1) * (window.max - window.min);
      let z = 0;
      for (let i = 0; i < 512; i++) { z = z * z + parameter; if (Math.abs(z) > 4) break; if (i < 384) continue;
        const y = Math.round((2 - z) / 4 * (height - 1));
        if (y >= 0 && y < height) { const index = (y * width + x) * 4; image.data[index] = Math.min(193, image.data[index] + 25); image.data[index + 1] = Math.min(228, image.data[index + 1] + 30); image.data[index + 2] = Math.min(203, image.data[index + 2] + 26); }
      }
    }
    ctx.putImageData(image, 0, 0);
  }, [window.min, window.max]);
  const choose = (value: number) => onChange({ julia: [Math.min(.25, Math.max(-2, value)), 0] });
  const x = (c - window.min) / (window.max - window.min) * 100;
  return <><div className="research-panel real-slice-panel"><div className="panel-heading"><div><span className="research-eyebrow">NUMERICAL EXPERIMENT 01</span><h2>Order gives way to complexity.</h2></div><select aria-label="Real slice viewing window" value={windowIndex} onChange={event => setWindowIndex(Number(event.target.value))}>{windows.map((item, index) => <option value={index} key={item.name}>{item.name}</option>)}</select></div><p className="panel-description">For each real c, iterate from 0, discard the transient, and plot the remaining values of z. Select a column to inspect its orbit.</p><div className="bifurcation-chart"><canvas ref={canvas} aria-label="Real quadratic orbit diagram. Horizontal coordinate is real c, vertical coordinate is z. Use parameter input below for keyboard selection." onClick={event => { const box = event.currentTarget.getBoundingClientRect(); choose(window.min + (event.clientX - box.left) / box.width * (window.max - window.min)); }} />{x >= 0 && x <= 100 && <div className="bifurcation-marker" style={{ left: `${x}%` }}><span>c = {c.toFixed(6)}</span></div>}<span className="bifurcation-z top">z = 2</span><span className="bifurcation-z bottom">z = −2</span></div><div className="chart-x-ticks">{Array.from({ length: 6 }, (_, index) => <span key={index}>{(window.min + index / 5 * (window.max - window.min)).toFixed(2)}</span>)}</div><div className="real-slice-controls"><label>Real parameter c<input aria-label="Real slice parameter" type="number" step="0.00001" min="-2" max=".25" value={c} onChange={event => { if (Number.isFinite(event.target.valueAsNumber)) choose(event.target.valueAsNumber); }} /></label><input aria-label="Move along real parameter slice" type="range" min={window.min} max={window.max} step="0.00001" value={Math.max(window.min, Math.min(window.max, c))} onChange={event => choose(Number(event.target.value))} /><button className="research-button" onClick={() => { onChange({ scene: 'julia', julia: [c, 0], center: [0, 0], scale: 3.6, iterations: 256, autoRotate: false }); onExplore(); }}>Inspect Julia set<ArrowRight size={14} /></button></div><div className="metric-row"><Metric label="PARAMETER" value={c.toFixed(9)} /><Metric label="NUMERICAL RETURN" value={candidate ? `Period ${candidate} candidate` : escape ? 'Escaping' : 'Not resolved ≤ 32'} /><Metric label="SAMPLES" value="1,024" detail="Critical orbit; 64-point tail inspected" /></div></div><div className="experiment-presets"><span>JUMP TO</span>{[{ name: 'Basilica', value: -1 }, { name: 'Feigenbaum vicinity', value: -1.401155189 }, { name: 'Airplane center', value: -1.754877666 }, { name: 'Period-27 center', value: -1.786429858055761 }].map(item => <button key={item.name} onClick={() => choose(item.value)}>{item.name}<ArrowRight size={12} /></button>)}<DownloadButton data={{ schema: 'loops-real-slice-experiment-v1', parameter: c, numericPrecision: 'IEEE-754 float64', transientIterations: 960, returnTolerance: 1e-7, candidatePeriod: candidate, orbitTail: tail }} name="loops-real-slice.json" label="Export sample" /></div><ScopeNote>This plot is a finite floating-point experiment. A period candidate uses a 10⁻⁷ tolerance on the last 64 values; it is not an exact period certificate. Preset centers are rounded. Near a repelling or nearly neutral cycle, transients and rounding can dominate the displayed orbit.</ScopeNote></>;
}

function Methods() {
  const methods = [
    { number: '01', title: 'A rendered orbit', tag: 'NUMERICAL', description: 'The GPU and browser calculate finite approximations. They are useful for exploring a shape, comparing parameters, and finding questions. Boundedness at a finite iteration limit is not a membership proof.' },
    { number: '02', title: 'An exact finite certificate', tag: 'FINITE ARITHMETIC', description: 'Rational angle arithmetic and integer relations retain their exact source values. A finite verifier establishes its stated finite claim. Analytic assumptions and physical identifications remain separate.' },
    { number: '03', title: 'A formal theorem', tag: 'KERNEL CHECKED', description: 'A Lean result has the scope of its checked statement and explicit assumptions. The app links to the original formalization and research record; it does not infer formal status from a green visualization or the ledger label “proved”.' },
    { number: '04', title: 'An unresolved bridge', tag: 'OPEN / CONDITIONAL', description: 'The archive preserves open hypotheses, imported results, and conditional implications. The Mandelbrot local connectivity conjecture remains open; the explorer does not promote finite experiments into a global result.' },
  ];
  return <><div className="methods-grid">{methods.map(method => <article className="research-panel method-card" key={method.number}><div className="method-number">{method.number}</div><span className="research-eyebrow">{method.tag}</span><h2>{method.title}</h2><p>{method.description}</p></article>)}</div><div className="research-panel formula-method"><Binary size={24} /><div><h2>Keep the spaces distinct.</h2><p>The complex Mandelbrot set is a parameter set for z ↦ z² + c. A Mandelbulb, Mandelbox, or quaternion Julia slice is a different three-dimensional construction. The engine labels each scene and the Atlas preserves the actual research model.</p></div></div><div className="research-footer-links"><SourceLink path="RESEARCH_MAP.md" label="Read the research map" /><SourceLink path="formalization/weighted/README.md" label="Formalization scope" /><SourceLink path="results/period27_symbolic_marking.json" label="Example finite certificate" /></div></>;
}

export function Lab({ state, onChange, onExplore }: { state: EngineState; onChange: (patch: Partial<EngineState>) => void; onExplore: () => void }) {
  const [tab, setTab] = useState<'precision' | 'slice' | 'methods'>('precision');
  return <div className="research-content lab-workspace"><ResearchHeading index="03 / EXPERIMENT LAB" title="A question becomes an experiment." description="Probe a parameter, inspect a return, or leave hardware precision behind for a slower, high-precision study." /><nav className="research-tabs" aria-label="Lab experiments"><button className={tab === 'precision' ? 'active' : ''} aria-pressed={tab === 'precision'} onClick={() => setTab('precision')}><Focus size={15} />Precision study</button><button className={tab === 'slice' ? 'active' : ''} aria-pressed={tab === 'slice'} onClick={() => setTab('slice')}><Waves size={15} />Real-slice dynamics</button><button className={tab === 'methods' ? 'active' : ''} aria-pressed={tab === 'methods'} onClick={() => setTab('methods')}><FlaskConical size={15} />Methods & scope</button></nav>{tab === 'precision' && <PrecisionStudy />}{tab === 'slice' && <RealSlice state={state} onChange={onChange} onExplore={onExplore} />}{tab === 'methods' && <Methods />}</div>;
}
