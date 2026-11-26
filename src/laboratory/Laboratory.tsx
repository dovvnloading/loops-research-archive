import { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import type { ReactNode } from 'react';
import { ArrowUpRight } from 'lucide-react';
import {
  alignedIndex,
  analyzeOrbit,
  sampleParameter,
  validateComparisonSettings,
  validateScanSettings,
} from './math';
import type {
  ComparisonMetrics,
  ComparisonRegion,
  ComparisonSettings,
  DiscoveryCandidate,
  OrbitAnalysis,
  ScanSettings,
} from './math';
import {
  encodeSurveyPixels,
  prepareExperimentReplay,
  restoreComparisonResult,
  restoreSurveyResult,
  validateOrbitSettings,
} from './replay';
import type {
  LaboratoryManifest as Manifest,
  SurveyResult as ScanResult,
  ComparisonResult as CompareResult,
} from './replay';
import './laboratory.css';

export interface LaboratoryTarget {
  re: string;
  im: string;
  span: string;
  family?: 'mandelbrot' | 'julia';
  iterations?: number;
  title?: string;
}
export interface LaboratoryProps {
  parameter?: [number, number];
  replay?: unknown;
  initialInstrument?: 'discovery' | 'orbit' | 'comparison';
  onNavigate: (target: LaboratoryTarget) => void;
  onSaveExperiment?: (experiment: {
    title: string;
    notes: string;
    data: unknown;
  }) => void | Promise<void>;
}
type Tab = 'discovery' | 'orbit' | 'comparison';
type RunStatus = 'idle' | 'running' | 'paused' | 'complete' | 'cancelled' | 'error';
interface Imported {
  nonce: number;
  manifest: Manifest;
}
const DEFAULT_SCAN: ScanSettings = {
  reMin: -2.1,
  reMax: 0.6,
  imMin: -1.35,
  imMax: 1.35,
  resolution: 80,
  iterations: 1024,
  maxPeriod: 32,
};
const DEFAULT_COMPARISON: ComparisonSettings = {
  a: { re: '-0.5', im: '0', span: '3.2' },
  b: { re: '-1.7548776662466927', im: '0', span: '0.12' },
  resolution: 96,
  iterations: 512,
  align: true,
};
const REGIONS = [
  {
    label: 'The whole parameter plane',
    value: 'whole',
    bounds: { reMin: -2.1, reMax: 0.6, imMin: -1.35, imMax: 1.35 },
  },
  {
    label: 'Airplane window',
    value: 'airplane',
    bounds: { reMin: -1.81, reMax: -1.72, imMin: -0.045, imMax: 0.045 },
  },
  {
    label: 'Seahorse valley',
    value: 'seahorse',
    bounds: { reMin: -0.78, reMax: -0.7, imMin: 0.09, imMax: 0.17 },
  },
  {
    label: 'Rabbit archipelago',
    value: 'rabbit',
    bounds: { reMin: -0.22, reMax: -0.02, imMin: 0.65, imMax: 0.85 },
  },
];
const fmt = (n: number, digits = 5) =>
  Number.isFinite(n) ? n.toLocaleString('en-US', { maximumFractionDigits: digits }) : '—';
const scientific = (n: number | null, digits = 3) =>
  n === null
    ? '—'
    : n === 0
      ? '0'
      : Math.abs(n) < 0.001
        ? n.toExponential(digits)
        : n.toFixed(digits);
const complex = (re: number, im: number, digits = 6) =>
  `${re.toFixed(digits)} ${im < 0 ? '−' : '+'} ${Math.abs(im).toFixed(digits)}i`;

function saveFile(filename: string, content: string, type = 'application/json') {
  const url = URL.createObjectURL(new Blob([content], { type })),
    a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.append(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
function manifest(instrument: Tab, settings: unknown, result?: unknown): Manifest {
  return {
    schema: 'loops-laboratory-v1',
    instrument,
    settings,
    ...(result === undefined ? {} : { result }),
    createdAt: new Date().toISOString(),
    method: 'loops-quadratic-instruments-1',
    precision: 'IEEE-754 binary64',
    claim:
      'Finite numerical experiment. Periods, centers and shape comparisons are candidates or diagnostics, not certified mathematical results.',
  };
}
function exportManifest(data: Manifest) {
  saveFile(
    `loops-${data.instrument}-${new Date().toISOString().slice(0, 10)}.json`,
    JSON.stringify(data, null, 2),
  );
}

function Field({ label, children, hint }: { label: string; children: ReactNode; hint?: string }) {
  return (
    <label className="lab-field">
      <span>{label}</span>
      {children}
      {hint && <small>{hint}</small>}
    </label>
  );
}
function Stat({ label, value, detail }: { label: string; value: ReactNode; detail?: string }) {
  return (
    <div className="lab-stat">
      <span>{label}</span>
      <strong>{value}</strong>
      {detail && <small>{detail}</small>}
    </div>
  );
}
function Scope({ children }: { children: ReactNode }) {
  return (
    <div className="lab-scope">
      <span>Scope</span>
      <p>{children}</p>
    </div>
  );
}
function useExperimentWorker(onMessage: (message: any) => void) {
  const worker = useRef<Worker | null>(null),
    generation = useRef(0),
    callback = useRef(onMessage);
  callback.current = onMessage;
  useEffect(
    () => () => {
      generation.current++;
      worker.current?.terminate();
    },
    [],
  );
  const run = useCallback((type: 'scan' | 'compare', settings: unknown) => {
    const id = generation.current + 1;
    let next: Worker | null = null;
    try {
      next = new Worker(new URL('./experiment.worker.ts', import.meta.url), { type: 'module' });
      next.onmessage = (event) => {
        if (event.data.id === generation.current) callback.current(event.data);
      };
      next.onerror = () => {
        if (id === generation.current)
          callback.current({
            id,
            type: 'error',
            message: 'The calculation worker stopped. Reduce the budget and try again.',
          });
      };
      next.postMessage({ type, id, settings });
      worker.current?.terminate();
      generation.current = id;
      worker.current = next;
      return true;
    } catch (error) {
      next?.terminate();
      callback.current({
        id: generation.current,
        type: 'error',
        message: `The calculation could not start: ${error instanceof Error ? error.message : 'Web Workers are unavailable in this browser.'} Your previous result is retained.`,
      });
      return false;
    }
  }, []);
  const control = useCallback((type: 'pause' | 'resume' | 'cancel') => {
    if (type === 'cancel') {
      generation.current++;
      worker.current?.terminate();
      worker.current = null;
    } else worker.current?.postMessage({ id: generation.current, type });
  }, []);
  return { run, control };
}

function useExperimentSaver(
  handler: LaboratoryProps['onSaveExperiment'],
  onError: (message: string) => void,
) {
  const [saved, setSavedState] = useState(false),
    [saving, setSaving] = useState(false),
    pending = useRef(false),
    revision = useRef(0);
  const setSaved = (value: boolean) => {
    if (!value) revision.current++;
    setSavedState(value);
  };
  const saveExperiment = async (experiment: { title: string; notes: string; data: unknown }) => {
    if (!handler || pending.current) return;
    pending.current = true;
    setSaving(true);
    setSaved(false);
    onError('');
    const version = revision.current;
    try {
      await handler(experiment);
      if (version === revision.current) setSavedState(true);
    } catch (error) {
      onError(error instanceof Error ? error.message : 'The experiment could not be saved.');
    } finally {
      pending.current = false;
      setSaving(false);
    }
  };
  return { saved, setSaved, saving, saveExperiment };
}

function Discovery({
  onNavigate,
  onSaveExperiment,
  imported,
}: LaboratoryProps & { imported: Imported | null }) {
  const [settings, setSettings] = useState<ScanSettings>(DEFAULT_SCAN),
    [region, setRegion] = useState('whole');
  const [status, setStatus] = useState<RunStatus>('idle'),
    [result, setResult] = useState<ScanResult | null>(null),
    [error, setError] = useState('');
  const [runSettings, setRunSettings] = useState<ScanSettings | null>(null),
    [filter, setFilter] = useState('all'),
    [selected, setSelected] = useState<DiscoveryCandidate | null>(null);
  const canvas = useRef<HTMLCanvasElement>(null),
    requestSettings = useRef<ScanSettings>(DEFAULT_SCAN);
  const [preview, setPreview] = useState<{
      pixels: Uint8ClampedArray;
      settings: ScanSettings;
      processed: number;
    } | null>(null),
    [restoredRecord, setRestoredRecord] = useState(false);
  const { saved, setSaved, saving, saveExperiment } = useExperimentSaver(
    onSaveExperiment,
    setError,
  );
  const { run, control } = useExperimentWorker((message) => {
    if (message.type === 'error') {
      setError(message.message);
      setStatus('error');
    }
    if (message.type === 'scan-progress' || message.type === 'scan-complete') {
      setResult(message);
      setPreview({
        pixels: message.pixels,
        settings: requestSettings.current,
        processed: message.processed,
      });
      if (message.type === 'scan-complete') setStatus('complete');
    }
  });
  useEffect(() => {
    if (imported?.manifest.instrument !== 'discovery') return;
    try {
      const valid = validateScanSettings(imported.manifest.settings),
        restored = restoreSurveyResult(imported.manifest.result, valid);
      control('cancel');
      requestSettings.current = valid;
      setSettings(valid);
      setRegion('custom');
      setResult(restored);
      setRunSettings(valid);
      setStatus('idle');
      setError('');
      setSelected(null);
      setFilter('all');
      setSaved(false);
      setRestoredRecord(true);
      if (restored?.pixels)
        setPreview({ pixels: restored.pixels, settings: valid, processed: restored.processed });
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Invalid scan settings.');
    }
  }, [imported, control]);
  useEffect(() => {
    const element = canvas.current,
      ctx = element?.getContext('2d');
    if (!element || !ctx) return;
    const n = preview?.settings.resolution ?? settings.resolution;
    element.width = n;
    element.height = n;
    ctx.fillStyle = '#0a0a09';
    ctx.fillRect(0, 0, n, n);
    if (preview) ctx.putImageData(new ImageData(new Uint8ClampedArray(preview.pixels), n, n), 0, 0);
  }, [preview, settings.resolution]);
  const busy = status === 'running' || status === 'paused';
  const begin = () => {
    try {
      const valid = validateScanSettings(settings);
      if (!run('scan', valid)) return;
      requestSettings.current = valid;
      setError('');
      setResult(null);
      setSelected(null);
      setSaved(false);
      setRunSettings(valid);
      setStatus('running');
      setFilter('all');
      setRestoredRecord(false);
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Check the experiment settings.');
      setStatus('error');
    }
  };
  const update = (key: keyof ScanSettings, value: number) => {
    setSettings((s) => ({ ...s, [key]: value }));
    setRegion('custom');
  };
  const candidates = useMemo(
    () =>
      (result?.candidates ?? [])
        .filter((c) => filter === 'all' || c.period === Number(filter))
        .sort(
          (a, b) => a.period - b.period || a.center.re - b.center.re || a.center.im - b.center.im,
        ),
    [result?.candidates, filter],
  );
  const periods = [...new Set((result?.candidates ?? []).map((c) => c.period))].sort(
    (a, b) => a - b,
  );
  const activeSettings = runSettings ?? settings,
    displaySettings = preview?.settings ?? activeSettings;
  const previewMatches =
    !!preview && JSON.stringify(preview.settings) === JSON.stringify(activeSettings);
  const payload = () => {
    if (!result) return manifest('discovery', activeSettings);
    const { pixels, ...record } = result;
    return manifest('discovery', activeSettings, {
      ...record,
      ...(pixels ? { pixelsBase64: encodeSurveyPixels(pixels) } : {}),
      status,
    });
  };
  const viewCandidate = (candidate: DiscoveryCandidate) =>
    onNavigate({
      re: String(candidate.center.re),
      im: String(candidate.center.im),
      span: String(
        Math.min(
          activeSettings.reMax - activeSettings.reMin,
          activeSettings.imMax - activeSettings.imMin,
        ) / 5,
      ),
      iterations: Math.max(512, activeSettings.iterations),
      title: `Period ${candidate.period} candidate`,
    });
  const progress = result ? result.processed / result.total : 0;
  return (
    <div className="lab-instrument">
      <div className="lab-instrument-intro">
        <div>
          <h2>Parameter expedition</h2>
          <p>
            Samples a rectangle of the parameter plane, classifies each sample by its critical
            orbit, and refines candidate centers of attracting components.
          </p>
        </div>
        <span className="lab-method-tag">Float64, numerical</span>
      </div>
      <div className="lab-discovery-layout">
        <aside className="lab-panel lab-settings">
          <div className="lab-panel-label">
            <span>Settings</span>
          </div>
          <Field label="Region">
            <select
              value={region}
              disabled={busy}
              onChange={(event) => {
                const choice = REGIONS.find((r) => r.value === event.target.value);
                setRegion(event.target.value);
                if (choice) setSettings((s) => ({ ...s, ...choice.bounds }));
              }}
            >
              {REGIONS.map((r) => (
                <option key={r.value} value={r.value}>
                  {r.label}
                </option>
              ))}
              <option value="custom">Custom window</option>
            </select>
          </Field>
          <div className="lab-field-grid">
            <Field label="Real · from">
              <input
                aria-label="Scan minimum real coordinate"
                type="number"
                step="any"
                value={Number.isFinite(settings.reMin) ? settings.reMin : ''}
                disabled={busy}
                onChange={(e) => update('reMin', e.target.valueAsNumber)}
              />
            </Field>
            <Field label="Real · to">
              <input
                aria-label="Scan maximum real coordinate"
                type="number"
                step="any"
                value={Number.isFinite(settings.reMax) ? settings.reMax : ''}
                disabled={busy}
                onChange={(e) => update('reMax', e.target.valueAsNumber)}
              />
            </Field>
            <Field label="Imaginary · from">
              <input
                aria-label="Scan minimum imaginary coordinate"
                type="number"
                step="any"
                value={Number.isFinite(settings.imMin) ? settings.imMin : ''}
                disabled={busy}
                onChange={(e) => update('imMin', e.target.valueAsNumber)}
              />
            </Field>
            <Field label="Imaginary · to">
              <input
                aria-label="Scan maximum imaginary coordinate"
                type="number"
                step="any"
                value={Number.isFinite(settings.imMax) ? settings.imMax : ''}
                disabled={busy}
                onChange={(e) => update('imMax', e.target.valueAsNumber)}
              />
            </Field>
          </div>
          <div className="lab-setting-divider" />
          <Field
            label="Sampling grid"
            hint={`${fmt(settings.resolution ** 2, 0)} parameters, sampled at cell centers`}
          >
            <select
              value={settings.resolution}
              disabled={busy}
              onChange={(e) => setSettings((s) => ({ ...s, resolution: Number(e.target.value) }))}
            >
              {[48, 80, 128, 192].map((n) => (
                <option key={n} value={n}>
                  {n} × {n}
                  {n === 80 ? ' · balanced' : n === 192 ? ' · detailed' : ''}
                </option>
              ))}
            </select>
          </Field>
          <div className="lab-field-grid">
            <Field label="Iteration budget">
              <select
                value={settings.iterations}
                disabled={busy}
                onChange={(e) => setSettings((s) => ({ ...s, iterations: Number(e.target.value) }))}
              >
                {[512, 1024, 2048, 4096, 8192].map((n) => (
                  <option key={n} value={n}>
                    {fmt(n, 0)}
                  </option>
                ))}
              </select>
            </Field>
            <Field label="Maximum period">
              <select
                value={settings.maxPeriod}
                disabled={busy}
                onChange={(e) => setSettings((s) => ({ ...s, maxPeriod: Number(e.target.value) }))}
              >
                {[8, 16, 32, 64].map((n) => (
                  <option key={n} value={n}>
                    {n}
                  </option>
                ))}
              </select>
            </Field>
          </div>
          {!busy ? (
            <button className="lab-button lab-primary lab-full" onClick={begin}>
              {status === 'complete' ? 'Run expedition again' : 'Start expedition'}
            </button>
          ) : (
            <div className="lab-run-actions">
              <button
                className="lab-button lab-primary"
                onClick={() => {
                  control(status === 'paused' ? 'resume' : 'pause');
                  setStatus(status === 'paused' ? 'running' : 'paused');
                }}
              >
                {status === 'paused' ? 'Resume' : 'Pause'}
              </button>
              <button
                className="lab-button"
                onClick={() => {
                  control('cancel');
                  setStatus('cancelled');
                }}
              >
                Stop
              </button>
            </div>
          )}
          <p className="lab-small">
            Runs in this browser. Stopping keeps the samples already taken.
          </p>
        </aside>
        <div className="lab-survey">
          <div className="lab-panel lab-survey-plot">
            <div className="lab-chart-header">
              <span>
                <span className={`lab-live-dot ${status === 'running' ? 'is-live' : ''}`} />
                {restoredRecord
                  ? 'Saved record, ready to replay'
                  : status === 'idle'
                    ? 'Not started'
                    : status[0].toUpperCase() + status.slice(1)}
              </span>
              <span>
                {result
                  ? `${fmt(result.processed, 0)} / ${fmt(result.total, 0)}`
                  : `${fmt(settings.resolution ** 2, 0)} samples planned`}
              </span>
            </div>
            <div className="lab-map-frame">
              <span className="lab-axis-label lab-y-top">{displaySettings.imMax.toFixed(3)}i</span>
              <span className="lab-axis-label lab-y-bottom">
                {displaySettings.imMin.toFixed(3)}i
              </span>
              <canvas
                ref={canvas}
                aria-label="Parameter survey. Colors show numerical attracting periods, escape, or unresolved return. Candidate controls are listed below."
                onClick={(event) => {
                  if (!preview) return;
                  const shown = preview.settings,
                    box = event.currentTarget.getBoundingClientRect(),
                    x = Math.floor(((event.clientX - box.left) / box.width) * shown.resolution),
                    y = Math.floor(((event.clientY - box.top) / box.height) * shown.resolution);
                  if (y * shown.resolution + x >= preview.processed) return;
                  const c = sampleParameter(shown, x, y);
                  onNavigate({
                    re: String(c.re),
                    im: String(c.im),
                    span: String(
                      Math.min(shown.reMax - shown.reMin, shown.imMax - shown.imMin) / 5,
                    ),
                    iterations: shown.iterations,
                    title: 'Expedition parameter',
                  });
                }}
              />
              {!preview && (
                <div className="lab-map-empty">
                  <h3>{restoredRecord ? 'Saved catalog restored' : 'No survey yet'}</h3>
                  <p>
                    {restoredRecord
                      ? 'Run the expedition to reconstruct its survey image.'
                      : 'Set the region and start the expedition. Each cell of the grid is one sampled parameter.'}
                  </p>
                </div>
              )}
              {selected && previewMatches && (
                <span
                  className="lab-map-selection"
                  style={{
                    left: `${((selected.center.re - activeSettings.reMin) / (activeSettings.reMax - activeSettings.reMin)) * 100}%`,
                    top: `${((activeSettings.imMax - selected.center.im) / (activeSettings.imMax - activeSettings.imMin)) * 100}%`,
                  }}
                />
              )}
            </div>
            <div className="lab-x-axis">
              <span>{displaySettings.reMin.toFixed(3)}</span>
              <span>Re(c)</span>
              <span>{displaySettings.reMax.toFixed(3)}</span>
            </div>
            <div
              className="lab-progress"
              role="progressbar"
              aria-label="Expedition progress"
              aria-valuemin={0}
              aria-valuemax={100}
              aria-valuenow={Math.round(progress * 100)}
            >
              <span style={{ width: `${progress * 100}%` }} />
            </div>
            <div className="lab-map-legend">
              <span>
                <i className="is-attracting" />
                Attracting return
              </span>
              <span>
                <i className="is-escaped" />
                Escaped
              </span>
              <span>
                <i className="is-unresolved" />
                Unresolved
              </span>
              <span>
                {preview && (!previewMatches || (busy && !result))
                  ? 'Previous survey preview retained'
                  : restoredRecord && preview
                    ? 'Saved numerical preview · rerun to verify'
                    : result
                      ? `${(result.elapsed / 1000).toFixed(1)}s elapsed`
                      : 'Float64 · tolerance 10⁻⁹'}
              </span>
            </div>
          </div>
          <div className="lab-stat-grid">
            <Stat
              label="Component candidates"
              value={result?.candidates.length ?? '—'}
              detail="Distinct refined centers"
            />
            <Stat
              label="Periods observed"
              value={result ? Object.keys(result.periods).length : '—'}
              detail={`Searches periods 1–${activeSettings.maxPeriod}`}
            />
            <Stat
              label="Unresolved"
              value={result ? `${((result.unresolved / result.processed) * 100).toFixed(1)}%` : '—'}
              detail="At the current finite budget"
            />
          </div>
        </div>
      </div>
      {error && (
        <div className="lab-error" role="alert">
          {error}
        </div>
      )}
      <div className="lab-panel lab-findings">
        <div className="lab-panel-title">
          <div>
            <h3>
              Candidate centers <span>{result?.candidates.length ?? 0}</span>
            </h3>
          </div>
          <div className="lab-toolbar">
            <select
              aria-label="Filter discovered candidates by period"
              value={filter}
              onChange={(e) => setFilter(e.target.value)}
            >
              <option value="all">All periods</option>
              {periods.map((p) => (
                <option key={p} value={p}>
                  Period {p}
                </option>
              ))}
            </select>
            <button
              className="lab-button"
              aria-label="Export expedition JSON"
              title="Export reproducible JSON"
              onClick={() => exportManifest(payload())}
            >
              Export JSON
            </button>
          </div>
        </div>
        {candidates.length ? (
          <div className="lab-table-scroll">
            <table className="lab-table">
              <thead>
                <tr>
                  <th>Period</th>
                  <th>Refined center c</th>
                  <th>Center residual</th>
                  <th>Inspect</th>
                </tr>
              </thead>
              <tbody>
                {candidates.slice(0, 80).map((candidate) => (
                  <tr
                    key={candidate.id}
                    className={selected?.id === candidate.id ? 'is-selected' : ''}
                  >
                    <td>
                      <button
                        className="lab-period-pill"
                        onClick={() => setSelected(candidate)}
                        aria-label={`Highlight period ${candidate.period} center on map`}
                      >
                        p{candidate.period}
                      </button>
                    </td>
                    <td>
                      <button
                        className="lab-coordinate-button"
                        onClick={() => setSelected(candidate)}
                      >
                        {complex(candidate.center.re, candidate.center.im, 10)}
                      </button>
                    </td>
                    <td className="lab-mono">{scientific(candidate.residual)}</td>
                    <td>
                      <button
                        className="lab-table-action"
                        aria-label={`Explore period ${candidate.period} candidate at ${candidate.center.re}, ${candidate.center.im}`}
                        onClick={() => viewCandidate(candidate)}
                      >
                        <ArrowUpRight size={16} />
                      </button>
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
            {candidates.length > 80 && (
              <p className="lab-small lab-table-more">
                Showing 80 of {candidates.length} candidates. Export CSV for the complete catalog.
              </p>
            )}
          </div>
        ) : (
          <div className="lab-empty-findings">
            <p>
              {status === 'idle'
                ? 'Refined centers are listed here once an expedition has run.'
                : status === 'running' || status === 'paused'
                  ? 'Looking for converged attracting cycles…'
                  : 'No refined centers found in the sampled window.'}
            </p>
            <small>
              {status === 'idle'
                ? 'Each row keeps its period, coordinates and residual; the export includes the settings.'
                : 'A finer grid or larger iteration budget can reveal additional candidates.'}
            </small>
          </div>
        )}
        {result && (
          <div className="lab-findings-footer">
            <span>
              {fmt(result.attracting, 0)} attracting samples · {fmt(result.escaped, 0)} escaped ·{' '}
              {fmt(result.unresolved, 0)} unresolved
            </span>
            <div>
              <button
                className="lab-text-button"
                onClick={() =>
                  saveFile(
                    'loops-expedition-candidates.csv',
                    'period,real,imaginary,residual,seed_real,seed_imaginary,seed_multiplier_modulus\n' +
                      result.candidates
                        .map((c) =>
                          [
                            c.period,
                            c.center.re,
                            c.center.im,
                            c.residual,
                            c.seed.re,
                            c.seed.im,
                            c.multiplierModulus,
                          ].join(','),
                        )
                        .join('\n'),
                    'text/csv',
                  )
                }
              >
                Export CSV
              </button>
              {onSaveExperiment && (
                <button
                  className="lab-text-button"
                  disabled={saving}
                  onClick={() => {
                    void saveExperiment({
                      title: `Expedition · ${result.candidates.length} candidates`,
                      notes: `Surveyed ${result.processed} parameters, with ${activeSettings.iterations} iterations and periods up to ${activeSettings.maxPeriod}. Numerical candidates; not certified.`,
                      data: payload(),
                    });
                  }}
                >
                  {saving ? 'Saving…' : saved ? 'Saved to journal' : 'Save experiment'}
                </button>
              )}
            </div>
          </div>
        )}
      </div>
      <Scope>
        Three repeated tail returns within 10⁻⁹ and a numerical multiplier below 1 identify an
        attracting-cycle candidate. Newton iteration then searches for a critical periodic center.
        The catalog retains up to 256 refined centers. The grid can miss small components; slow or
        neutral dynamics can remain unresolved. None of these tests certifies a period, membership,
        or a new discovery.
      </Scope>
    </div>
  );
}

function OrbitPlot({ analysis }: { analysis: OrbitAnalysis }) {
  const points = analysis.orbit.filter((p) => Math.abs(p.re) <= 2.5 && Math.abs(p.im) <= 2.5),
    width = 640,
    height = 440;
  const scale = 84,
    cx = width / 2,
    cy = height / 2;
  const segments: string[] = [];
  let path = '',
    previous = -1;
  for (const p of points) {
    if (p.index !== previous + 1 && path) {
      segments.push(path);
      path = '';
    }
    path += `${path ? ' L' : 'M'}${cx + p.re * scale},${cy - p.im * scale}`;
    previous = p.index;
  }
  if (path) segments.push(path);
  return (
    <svg
      viewBox={`0 0 ${width} ${height}`}
      className="lab-orbit-plot"
      role="img"
      aria-label={`Critical orbit of c equals ${complex(analysis.parameter.re, analysis.parameter.im)}. ${analysis.disposition}.`}
    >
      <rect width={width} height={height} fill="#0a0a09" />
      {[-2, -1, 0, 1, 2].map((n) => (
        <g key={n}>
          <line
            x1={cx + n * scale}
            y1={24}
            x2={cx + n * scale}
            y2={height - 24}
            stroke={n === 0 ? '#45453d' : '#1f1f1c'}
            strokeWidth={n === 0 ? 1 : 0.6}
          />
          <line
            x1={24}
            y1={cy + n * scale}
            x2={width - 24}
            y2={cy + n * scale}
            stroke={n === 0 ? '#45453d' : '#1f1f1c'}
            strokeWidth={n === 0 ? 1 : 0.6}
          />
          <text x={cx + n * scale + 5} y={cy + 15} fill="#8a877c" fontSize={11}>
            {n}
          </text>
        </g>
      ))}
      <circle
        cx={cx}
        cy={cy}
        r={2 * scale}
        fill="none"
        stroke="#8a877c"
        strokeWidth=".8"
        strokeDasharray="3 5"
      />
      {segments.map((d, i) => (
        <path key={i} d={d} fill="none" stroke="#b6b2a6" strokeWidth="1" opacity=".5" />
      ))}
      {points.slice(0, 128).map((p) => (
        <circle
          key={p.index}
          cx={cx + p.re * scale}
          cy={cy - p.im * scale}
          r={p.index === 0 ? 4 : 2.1}
          fill={p.index === 0 ? '#ffffff' : '#b6b2a6'}
          opacity={Math.max(0.2, 1 - p.index / 150)}
        />
      ))}
      {analysis.cycle.map((p, i) => (
        <g key={i}>
          <circle
            cx={cx + p.re * scale}
            cy={cy - p.im * scale}
            r={7}
            fill="none"
            stroke="#e3b75f"
          />
          <circle cx={cx + p.re * scale} cy={cy - p.im * scale} r={3} fill="#e3b75f" />
        </g>
      ))}
      <text
        className="lab-orbit-axis-name"
        x={width - 18}
        y={cy - 8}
        textAnchor="end"
        fill="#8a877c"
        fontSize={12}
      >
        Re(z)
      </text>
      <text className="lab-orbit-axis-name" x={cx + 8} y={28} fill="#8a877c" fontSize={12}>
        Im(z)
      </text>
      <text
        className="lab-orbit-radius-label"
        x={cx + 1.4142 * scale + 8}
        y={cy - 1.4142 * scale - 4}
        fill="#8a877c"
        fontSize={11}
      >
        |z| = 2
      </text>
    </svg>
  );
}

function OrbitMicroscope({
  parameter,
  onNavigate,
  onSaveExperiment,
  imported,
}: LaboratoryProps & { imported: Imported | null }) {
  const [initial] = useState(() => {
    try {
      return {
        analysis: analyzeOrbit(
          { re: parameter?.[0] ?? -1.7548776662466927, im: parameter?.[1] ?? 0 },
          2048,
        ),
        error: '',
      };
    } catch (error) {
      return {
        analysis: analyzeOrbit({ re: -1.7548776662466927, im: 0 }, 2048),
        error:
          error instanceof Error
            ? error.message
            : 'The selected parameter is outside this instrument’s range.',
      };
    }
  });
  const [re, setRe] = useState(String(parameter?.[0] ?? -1.7548776662466927)),
    [im, setIm] = useState(String(parameter?.[1] ?? 0)),
    [budget, setBudget] = useState(2048);
  const [analysis, setAnalysis] = useState<OrbitAnalysis>(initial.analysis);
  const [error, setError] = useState(initial.error);
  const { saved, setSaved, saving, saveExperiment } = useExperimentSaver(
    onSaveExperiment,
    setError,
  );
  const analyze = (nextRe = re, nextIm = im, nextBudget = budget) => {
    try {
      if (!nextRe.trim() || !nextIm.trim()) throw new Error('Enter both parts of the parameter.');
      const value = analyzeOrbit({ re: Number(nextRe), im: Number(nextIm) }, nextBudget);
      setAnalysis(value);
      setError('');
      setSaved(false);
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Check the parameter.');
    }
  };
  useEffect(() => {
    if (!parameter || imported) return;
    setRe(String(parameter[0]));
    setIm(String(parameter[1]));
    try {
      setAnalysis(analyzeOrbit({ re: parameter[0], im: parameter[1] }, budget));
      setError('');
      setSaved(false);
    } catch (error) {
      setError(
        `${error instanceof Error ? error.message : 'The selected parameter is unsupported.'} The last valid orbit remains visible.`,
      );
    }
  }, [parameter?.[0], parameter?.[1], imported]);
  useEffect(() => {
    if (imported?.manifest.instrument !== 'orbit') return;
    try {
      const s = validateOrbitSettings(imported.manifest.settings);
      setRe(s.re);
      setIm(s.im);
      setBudget(s.iterations);
      analyze(s.re, s.im, s.iterations);
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Invalid orbit experiment.');
    }
  }, [imported]);
  const payload = () =>
    manifest(
      'orbit',
      {
        re: String(analysis.parameter.re),
        im: String(analysis.parameter.im),
        iterations: analysis.budget,
        maxPeriod: 64,
        tolerance: 1e-9,
        initial: { re: 0, im: 0 },
      },
      analysis,
    );
  const label =
    analysis.disposition === 'escaped'
      ? 'Escaping orbit'
      : analysis.period
        ? `Period ${analysis.period} candidate`
        : 'Return unresolved';
  const selectedRows =
    analysis.orbit.length > 16
      ? [...analysis.orbit.slice(0, 8), ...analysis.orbit.slice(-8)]
      : analysis.orbit;
  return (
    <div className="lab-instrument">
      <div className="lab-instrument-intro">
        <div>
          <h2>Orbit microscope</h2>
          <p>
            Iterates the critical point for one parameter and reports whether the orbit escapes,
            returns to an attracting cycle, or stays unresolved at the budget.
          </p>
        </div>
        <span className="lab-formula math">
          <i>z</i>
          <sub>0</sub> = 0, <i>z</i> ↦ <i>z</i>² + <i>c</i>
        </span>
      </div>
      <div className="lab-orbit-layout">
        <aside className="lab-panel lab-settings">
          <div className="lab-panel-label">
            <span>Parameter</span>
          </div>
          <Field label="Real part of c">
            <input
              aria-label="Orbit parameter real part"
              inputMode="decimal"
              value={re}
              onChange={(e) => setRe(e.target.value)}
              onKeyDown={(e) => {
                if (e.key === 'Enter') analyze();
              }}
            />
          </Field>
          <Field label="Imaginary part of c">
            <input
              aria-label="Orbit parameter imaginary part"
              inputMode="decimal"
              value={im}
              onChange={(e) => setIm(e.target.value)}
              onKeyDown={(e) => {
                if (e.key === 'Enter') analyze();
              }}
            />
          </Field>
          <Field label="Iteration budget">
            <select value={budget} onChange={(e) => setBudget(Number(e.target.value))}>
              {[512, 1024, 2048, 4096, 16384, 32768].map((n) => (
                <option key={n} value={n}>
                  {fmt(n, 0)} iterations
                </option>
              ))}
            </select>
          </Field>
          <button className="lab-button lab-primary lab-full" onClick={() => analyze()}>
            Analyze parameter
          </button>
          <div className="lab-setting-divider" />
          <span className="lab-kicker">Presets</span>
          <div className="lab-orbit-presets">
            {[
              { label: 'Center of the main cardioid', re: '0', im: '0' },
              { label: 'Basilica', re: '-1', im: '0' },
              { label: 'Airplane', re: '-1.7548776662466927', im: '0' },
              { label: 'A slowly escaping orbit', re: '-0.75', im: '0.1' },
              { label: 'Near a parabolic boundary', re: '-0.75', im: '0' },
            ].map((p) => (
              <button
                key={p.label}
                onClick={() => {
                  setRe(p.re);
                  setIm(p.im);
                  analyze(p.re, p.im);
                }}
              >
                {p.label}
              </button>
            ))}
          </div>
        </aside>
        <div>
          <div className="lab-panel lab-orbit-main">
            <div className="lab-chart-header">
              <span>{label}</span>
              <span>{analysis.iterations.toLocaleString()} iterations observed</span>
            </div>
            <OrbitPlot analysis={analysis} />
            <div className="lab-orbit-caption">
              <span>
                <i />
                Transient orbit
              </span>
              <span>
                <i />
                Estimated attracting cycle
              </span>
              <span>First and final 128 samples</span>
            </div>
          </div>
          <div className="lab-stat-grid lab-orbit-stats">
            <Stat
              label="Return period"
              value={analysis.period ?? (analysis.escapeIteration ? 'Escaped' : 'Unresolved')}
              detail={
                analysis.escapeIteration
                  ? `Escape at iteration ${analysis.escapeIteration}`
                  : 'Searches periods 1–64'
              }
            />
            <Stat
              label="Cycle multiplier |λ|"
              value={scientific(analysis.multiplierModulus, 4)}
              detail="Numerical stability diagnostic"
            />
            <Stat
              label="Return residual"
              value={scientific(analysis.residual)}
              detail="Maximum error across 3 returns"
            />
          </div>
        </div>
      </div>
      {error && (
        <div className="lab-error" role="alert">
          {error}
        </div>
      )}
      <div className="lab-panel lab-orbit-conclusion">
        <div>
          <h3>{label}</h3>
          <p>
            {analysis.escapeIteration
              ? `The critical orbit crossed |z| = 2 after ${analysis.escapeIteration} iterations in this floating-point calculation. The resulting Julia set can be explored at this parameter.`
              : analysis.period
                ? `The observed tail repeats with a candidate period of ${analysis.period}. Its numerical multiplier has modulus ${scientific(analysis.multiplierModulus, 6)}. This is evidence of attraction at this precision and budget.`
                : 'No attracting return up to period 64 passed the test at this budget. The orbit may converge slowly, have a larger period, or exhibit more complicated dynamics. Finite non-escape does not establish membership.'}
          </p>
        </div>
        <button
          className="lab-button"
          onClick={() =>
            onNavigate({
              re: String(analysis.parameter.re),
              im: String(analysis.parameter.im),
              span: '.15',
              iterations: Math.min(4096, analysis.budget),
              title: label,
            })
          }
        >
          Open this parameter in Explore
        </button>
      </div>
      <details className="lab-panel lab-orbit-details">
        <summary>
          <span>Numerical record</span>
          <span className="lab-mono">
            {complex(analysis.parameter.re, analysis.parameter.im, 10)}
          </span>
        </summary>
        <div className="lab-table-scroll">
          <table className="lab-table">
            <thead>
              <tr>
                <th>Iteration</th>
                <th>Real part</th>
                <th>Imaginary part</th>
                <th>|z|</th>
              </tr>
            </thead>
            <tbody>
              {selectedRows.map((p, index) => (
                <tr key={p.index}>
                  <td>
                    {index === 8 && analysis.orbit.length > 16 ? '… ' : ''}
                    {p.index}
                  </td>
                  <td className="lab-mono">{p.re.toPrecision(14)}</td>
                  <td className="lab-mono">{p.im.toPrecision(14)}</td>
                  <td className="lab-mono">{Math.hypot(p.re, p.im).toPrecision(10)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        <p className="lab-small">
          Finite tail Lyapunov mean: {scientific(analysis.finiteLyapunov, 6)}. Exact zero
          derivatives have a logarithmic singularity and are shown as unavailable. Full retained
          samples are included in the JSON export.
        </p>
      </details>
      <div className="lab-export-row">
        <button className="lab-button" onClick={() => exportManifest(payload())}>
          Export experiment
        </button>
        {onSaveExperiment && (
          <button
            className="lab-button"
            disabled={saving}
            onClick={() => {
              void saveExperiment({
                title: `Orbit · ${label}`,
                notes: `Critical orbit of c = ${complex(analysis.parameter.re, analysis.parameter.im, 12)}. ${analysis.budget} iterations, float64. ${label}; numerical evidence only.`,
                data: payload(),
              });
            }}
          >
            {saving ? 'Saving…' : saved ? 'Saved to journal' : 'Save to journal'}
          </button>
        )}
      </div>
      <Scope>
        Coordinates are evaluated as IEEE-754 binary64 values. A finite return and multiplier are
        numerical estimates, not exact or interval certificates. The dashed circle is the quadratic
        escape radius |z| = 2; displayed transient points are limited to the first 128 and final 128
        samples.
      </Scope>
    </div>
  );
}

function FieldCanvas({
  field,
  resolution,
  other,
  alignment,
  label,
}: {
  field?: Float32Array;
  resolution: number;
  other?: Float32Array;
  alignment?: ComparisonMetrics['alignment'];
  label: string;
}) {
  const ref = useRef<HTMLCanvasElement>(null);
  useEffect(() => {
    const canvas = ref.current,
      ctx = canvas?.getContext('2d');
    if (!canvas || !ctx) return;
    canvas.width = resolution;
    canvas.height = resolution;
    ctx.fillStyle = '#0a0a09';
    ctx.fillRect(0, 0, resolution, resolution);
    if (!field) return;
    const pixels = ctx.createImageData(resolution, resolution);
    for (let y = 0; y < resolution; y++)
      for (let x = 0; x < resolution; x++) {
        const i = y * resolution + x,
          value = field[alignment ? alignedIndex(x, y, resolution, alignment) : i];
        let rgb: [number, number, number];
        if (other) {
          const difference = Math.abs(value - other[i]);
          rgb = [12 + 228 * difference, 18 + 158 * difference, 29 + 74 * difference];
        } else if (value >= 1) rgb = [6, 10, 18];
        else {
          const t = Math.min(1, value * 1.15);
          rgb = [20 + 170 * t ** 2, 41 + 154 * t, 68 + 164 * Math.sqrt(t)];
        }
        pixels.data.set([...rgb.map(Math.round), 255], i * 4);
      }
    ctx.putImageData(pixels, 0, 0);
  }, [field, other, resolution, alignment]);
  return <canvas ref={ref} aria-label={label} />;
}

function Comparison({
  onNavigate,
  onSaveExperiment,
  imported,
}: LaboratoryProps & { imported: Imported | null }) {
  const [settings, setSettings] = useState<ComparisonSettings>(DEFAULT_COMPARISON),
    [runSettings, setRunSettings] = useState<ComparisonSettings | null>(null);
  const [result, setResult] = useState<CompareResult | null>(null),
    [status, setStatus] = useState<RunStatus>('idle'),
    [progress, setProgress] = useState(0),
    [error, setError] = useState(''),
    [restoredRecord, setRestoredRecord] = useState(false);
  const requestSettings = useRef<ComparisonSettings>(DEFAULT_COMPARISON);
  const { saved, setSaved, saving, saveExperiment } = useExperimentSaver(
    onSaveExperiment,
    setError,
  );
  const { run, control } = useExperimentWorker((message) => {
    if (message.type === 'error') {
      setError(message.message);
      setStatus('error');
    }
    if (message.type === 'compare-progress') setProgress(message.processed / message.total);
    if (message.type === 'compare-complete') {
      setResult(message);
      setRunSettings(requestSettings.current);
      setStatus('complete');
      setProgress(1);
    }
  });
  useEffect(() => {
    if (imported?.manifest.instrument !== 'comparison') return;
    try {
      const valid = validateComparisonSettings(imported.manifest.settings),
        restored = restoreComparisonResult(imported.manifest.result, valid);
      control('cancel');
      setSettings(valid);
      requestSettings.current = valid;
      setStatus('idle');
      setProgress(0);
      setError('');
      setSaved(false);
      setRestoredRecord(true);
      if (restored) {
        setResult(restored);
        setRunSettings(valid);
      }
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Invalid comparison settings.');
    }
  }, [imported, control]);
  const begin = () => {
    try {
      const valid = validateComparisonSettings(settings);
      if (!run('compare', valid)) return;
      requestSettings.current = valid;
      if (!result) setRunSettings(valid);
      setError('');
      setProgress(0);
      setSaved(false);
      setRestoredRecord(false);
      setStatus('running');
    } catch (e) {
      setError(e instanceof Error ? e.message : 'Check the comparison settings.');
      setStatus('error');
    }
  };
  const updateRegion = (key: 'a' | 'b', field: keyof ComparisonRegion, value: string) =>
    setSettings((s) => ({ ...s, [key]: { ...s[key], [field]: value } }));
  const active = runSettings ?? settings,
    busy = status === 'running';
  const previewMatches = JSON.stringify(active) === JSON.stringify(settings);
  const payload = () =>
    manifest(
      'comparison',
      active,
      result
        ? {
            metrics: result.metrics,
            elapsed: result.elapsed,
            fieldDefinition:
              'log1p(smooth escape) / log1p(iteration budget + 1); finite non-escape = 1',
            a: Array.from(result.a),
            b: Array.from(result.b),
          }
        : undefined,
    );
  const alignmentLabel = result?.metrics.alignment.replaceAll('-', ' ') ?? 'pending';
  return (
    <div className="lab-instrument">
      <div className="lab-instrument-intro">
        <div>
          <h2>Window comparison</h2>
          <p>
            Samples two parameter windows under the same grid and iteration budget and measures how
            far the two escape fields differ.
          </p>
        </div>
        <span className="lab-method-tag">Float64, shared settings</span>
      </div>
      <div className="lab-comparison-settings">
        {(['a', 'b'] as const).map((key, index) => (
          <div className="lab-panel lab-region-settings" key={key}>
            <div className="lab-panel-title">
              <h3>
                <span className="lab-region-letter">{key.toUpperCase()}</span>
                {index === 0 ? 'Reference window' : 'Comparison window'}
              </h3>
              <button
                className="lab-icon-button"
                aria-label={`Explore window ${key.toUpperCase()}`}
                title="Open in explorer"
                onClick={() => {
                  try {
                    validateComparisonSettings(settings);
                    onNavigate({
                      ...settings[key],
                      iterations: settings.iterations,
                      title: `Comparison window ${key.toUpperCase()}`,
                    });
                  } catch (e) {
                    setError(e instanceof Error ? e.message : 'Invalid region.');
                  }
                }}
              >
                <ArrowUpRight size={16} />
              </button>
            </div>
            <div className="lab-region-fields">
              <Field label="Center · real">
                <input
                  aria-label={`Region ${key.toUpperCase()} real center`}
                  value={settings[key].re}
                  disabled={busy}
                  onChange={(e) => updateRegion(key, 're', e.target.value)}
                />
              </Field>
              <Field label="Center · imaginary">
                <input
                  aria-label={`Region ${key.toUpperCase()} imaginary center`}
                  value={settings[key].im}
                  disabled={busy}
                  onChange={(e) => updateRegion(key, 'im', e.target.value)}
                />
              </Field>
              <Field label="Window span">
                <input
                  aria-label={`Region ${key.toUpperCase()} window span`}
                  value={settings[key].span}
                  disabled={busy}
                  onChange={(e) => updateRegion(key, 'span', e.target.value)}
                />
              </Field>
            </div>
          </div>
        ))}
      </div>
      <div className="lab-comparison-options">
        <div className="lab-comparison-presets">
          <span>Presets</span>
          <button
            disabled={busy}
            onClick={() => {
              setSettings(DEFAULT_COMPARISON);
              setStatus('idle');
              setRestoredRecord(false);
            }}
          >
            A miniature Mandelbrot
          </button>
          <button
            disabled={busy}
            onClick={() => {
              setSettings((s) => ({
                ...s,
                a: { re: '-.7435', im: '.1314', span: '.006' },
                b: { re: '-.7435', im: '-.1314', span: '.006' },
                align: true,
              }));
              setStatus('idle');
              setRestoredRecord(false);
            }}
          >
            Conjugate symmetry
          </button>
          <button
            disabled={busy}
            onClick={() => {
              setSettings((s) => ({ ...s, b: { ...s.a } }));
              setStatus('idle');
              setRestoredRecord(false);
            }}
          >
            Self-comparison
          </button>
        </div>
        <div className="lab-comparison-budget">
          <Field label="Sampling">
            <select
              value={settings.resolution}
              disabled={busy}
              onChange={(e) => setSettings((s) => ({ ...s, resolution: Number(e.target.value) }))}
            >
              {[64, 96, 128, 192].map((n) => (
                <option key={n} value={n}>
                  {n} × {n}
                </option>
              ))}
            </select>
          </Field>
          <Field label="Iterations">
            <select
              value={settings.iterations}
              disabled={busy}
              onChange={(e) => setSettings((s) => ({ ...s, iterations: Number(e.target.value) }))}
            >
              {[256, 512, 1024, 2048, 4096].map((n) => (
                <option key={n} value={n}>
                  {fmt(n, 0)}
                </option>
              ))}
            </select>
          </Field>
        </div>
      </div>
      <div className="lab-compare-controls">
        <label className="lab-checkbox">
          <input
            type="checkbox"
            checked={settings.align}
            disabled={busy}
            onChange={(e) => setSettings((s) => ({ ...s, align: e.target.checked }))}
          />
          <span>Test quarter turns and horizontal / vertical reflections</span>
        </label>
        {busy ? (
          <button
            className="lab-button"
            onClick={() => {
              control('cancel');
              setStatus('cancelled');
            }}
          >
            Cancel comparison
          </button>
        ) : (
          <button className="lab-button lab-primary" onClick={begin}>
            Compare windows
          </button>
        )}
      </div>
      {error && (
        <div className="lab-error" role="alert">
          {error}
        </div>
      )}
      <div
        className="lab-progress"
        role="progressbar"
        aria-label="Comparison progress"
        aria-valuemin={0}
        aria-valuemax={100}
        aria-valuenow={Math.round(progress * 100)}
      >
        <span style={{ width: `${progress * 100}%` }} />
      </div>
      {result && (restoredRecord || busy || !previewMatches) && (
        <div className="lab-preview-note" role="status">
          {!previewMatches
            ? 'Previous result shown below. Run the new settings to replace it.'
            : restoredRecord
              ? 'Saved numerical fields restored. Run the comparison to reproduce them.'
              : 'Previous result remains visible while the new comparison runs.'}
        </div>
      )}
      <div className="lab-comparison-images">
        <div className="lab-panel lab-comparison-image">
          <div className="lab-chart-header">
            <span>A, reference</span>
            <span>{active.a.span} span</span>
          </div>
          <FieldCanvas
            field={result?.a}
            resolution={active.resolution}
            label="Reference normalized escape field"
          />
          {!result && (
            <div className="lab-comparison-empty">
              <span>A</span>
              <p>{busy ? 'Sampling reference…' : 'Reference field'}</p>
            </div>
          )}
        </div>
        <div className="lab-panel lab-comparison-image">
          <div className="lab-chart-header">
            <span>B, aligned</span>
            <span>{result ? alignmentLabel : 'Awaiting comparison'}</span>
          </div>
          <FieldCanvas
            field={result?.b}
            alignment={result?.metrics.alignment}
            resolution={active.resolution}
            label="Comparison normalized escape field after selected alignment"
          />
          {!result && (
            <div className="lab-comparison-empty">
              <span>B</span>
              <p>{busy ? 'Sampling comparison…' : 'Comparison field'}</p>
            </div>
          )}
        </div>
        <div className="lab-panel lab-comparison-image">
          <div className="lab-chart-header">
            <span>Absolute difference</span>
            <span>0 → 1</span>
          </div>
          <FieldCanvas
            field={result?.b}
            other={result?.a}
            alignment={result?.metrics.alignment}
            resolution={active.resolution}
            label="Absolute pointwise difference. Darker values indicate smaller differences."
          />
          {!result && (
            <div className="lab-comparison-empty">
              <span>Δ</span>
              <p>Difference field</p>
            </div>
          )}
        </div>
      </div>
      <div className="lab-stat-grid lab-comparison-stats">
        <Stat
          label="Mean field difference"
          value={result ? result.metrics.meanAbsoluteDifference.toFixed(5) : '—'}
          detail="0 = identical sampled fields"
        />
        <Stat
          label="Field correlation"
          value={result?.metrics.correlation != null ? result.metrics.correlation.toFixed(5) : '—'}
          detail="Unavailable for constant fields"
        />
        <Stat
          label="Finite non-escape overlap"
          value={
            result?.metrics.finiteNonescapeJaccard != null
              ? `${(result.metrics.finiteNonescapeJaccard * 100).toFixed(2)}%`
              : '—'
          }
          detail="Intersection / union of sampled masks"
        />
      </div>
      {result && (
        <div className="lab-panel lab-comparison-reading">
          <div>
            <h3>
              {result.metrics.meanAbsoluteDifference < 1e-7
                ? 'The sampled fields coincide'
                : result.metrics.meanAbsoluteDifference < 0.05
                  ? 'The sampled fields are close'
                  : 'The sampled fields differ measurably'}
            </h3>
            <p>
              Best tested alignment: <strong>{alignmentLabel}</strong>. Compared{' '}
              {fmt(result.metrics.samples, 0)} point pairs with {active.iterations} iterations each,
              in {(result.elapsed / 1000).toFixed(2)} seconds. Finite non-escape occupied{' '}
              {(result.metrics.finiteNonescapeA * 100).toFixed(1)}% of A and{' '}
              {(result.metrics.finiteNonescapeB * 100).toFixed(1)}% of B.
            </p>
          </div>
          <div className="lab-export-row">
            <button className="lab-button" onClick={() => exportManifest(payload())}>
              Export comparison
            </button>
            {onSaveExperiment && (
              <button
                className="lab-button"
                disabled={saving}
                onClick={() => {
                  void saveExperiment({
                    title: 'Structural comparison',
                    notes: `Two Mandelbrot windows, ${active.resolution}×${active.resolution} samples, ${active.iterations} iterations. Mean field difference ${result.metrics.meanAbsoluteDifference.toFixed(6)}; alignment ${alignmentLabel}. Numerical diagnostic only.`,
                    data: payload(),
                  });
                }}
              >
                {saving ? 'Saving…' : saved ? 'Saved' : 'Save to journal'}
              </button>
            )}
          </div>
        </div>
      )}
      <Scope>
        Both windows use the same log-normalized smooth escape field, iteration cap, resolution, and
        palette. Alignment tests six fixed transformations; it does not optimize translations or
        continuous rotations. Similarity of finite images does not establish dynamical equivalence,
        renormalization, or set membership. Coordinates below the instrument’s float64 resolution
        are rejected.
      </Scope>
    </div>
  );
}

export function Laboratory(props: LaboratoryProps) {
  const [tab, setTab] = useState<Tab>(props.initialInstrument ?? 'discovery'),
    [imported, setImported] = useState<Imported | null>(null),
    [message, setMessage] = useState(''),
    [isError, setIsError] = useState(false);
  const upload = useRef<HTMLInputElement>(null),
    replayKey = useRef<string | null>(null),
    importSequence = useRef(0);
  const applyReplay = (input: unknown, origin: 'journal' | 'file') => {
    const prepared = prepareExperimentReplay(input);
    if (origin === 'journal' && prepared.key === replayKey.current) return;
    if (origin === 'journal') replayKey.current = prepared.key;
    setImported({ nonce: ++importSequence.current, manifest: prepared.manifest });
    setTab(prepared.manifest.instrument);
    setIsError(false);
    setMessage(
      prepared.manifest.instrument === 'orbit'
        ? 'Experiment restored and the critical orbit recomputed from its saved settings.'
        : 'Experiment settings and available numerical results restored. Run the instrument to reproduce them.',
    );
  };
  useEffect(() => {
    if (props.replay === undefined || props.replay === null) return;
    try {
      applyReplay(props.replay, 'journal');
    } catch (error) {
      setIsError(true);
      setMessage(
        error instanceof Error ? error.message : 'The journal experiment could not be restored.',
      );
    }
  }, [props.replay]);
  useEffect(() => {
    if (props.replay !== undefined && props.replay !== null) return;
    replayKey.current = null;
    setImported(null);
    setTab(props.initialInstrument ?? 'discovery');
    setMessage('');
    setIsError(false);
  }, [props.initialInstrument, props.replay]);
  const importFile = async (file: File | undefined) => {
    if (!file) return;
    try {
      if (file.size > 4_000_000)
        throw new Error('Choose a LOOPS experiment JSON smaller than 4 MB.');
      applyReplay(JSON.parse(await file.text()), 'file');
    } catch (e) {
      setIsError(true);
      setMessage(e instanceof Error ? e.message : 'The file could not be read.');
    }
    if (upload.current) upload.current.value = '';
  };
  return (
    <div className="laboratory-workspace">
      <header className="lab-workspace-header">
        <div>
          <h1>Laboratory</h1>
          <p>
            Three numerical instruments. Each result records its settings, precision and budget, and
            can be exported, saved to the journal and run again.
          </p>
        </div>
        <button className="lab-button" onClick={() => upload.current?.click()}>
          Import experiment
        </button>
        <input
          ref={upload}
          className="lab-file-input"
          type="file"
          accept=".json,application/json"
          aria-label="Import LOOPS experiment JSON"
          onChange={(e) => void importFile(e.target.files?.[0])}
        />
      </header>
      <nav className="lab-tabs" aria-label="Laboratory instruments" role="tablist">
        {[
          { id: 'discovery' as const, label: 'Expeditions' },
          { id: 'orbit' as const, label: 'Orbit microscope' },
          { id: 'comparison' as const, label: 'Compare structures' },
        ].map(({ id, label }) => (
          <button
            id={`lab-tab-${id}`}
            role="tab"
            aria-controls={`lab-panel-${id}`}
            aria-selected={tab === id}
            className={tab === id ? 'active' : ''}
            key={id}
            onClick={() => setTab(id)}
          >
            {label}
          </button>
        ))}
      </nav>
      {message && (
        <div
          className={isError ? 'lab-error' : 'lab-import-notice'}
          role={isError ? 'alert' : 'status'}
        >
          {message}
          <button aria-label="Dismiss import message" onClick={() => setMessage('')}>
            ×
          </button>
        </div>
      )}
      <section
        id="lab-panel-discovery"
        role="tabpanel"
        aria-labelledby="lab-tab-discovery"
        hidden={tab !== 'discovery'}
      >
        <Discovery {...props} imported={imported} />
      </section>
      <section
        id="lab-panel-orbit"
        role="tabpanel"
        aria-labelledby="lab-tab-orbit"
        hidden={tab !== 'orbit'}
      >
        <OrbitMicroscope {...props} imported={imported} />
      </section>
      <section
        id="lab-panel-comparison"
        role="tabpanel"
        aria-labelledby="lab-tab-comparison"
        hidden={tab !== 'comparison'}
      >
        <Comparison {...props} imported={imported} />
      </section>
    </div>
  );
}
