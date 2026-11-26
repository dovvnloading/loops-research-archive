import { useEffect, useState } from 'react';
import { ArrowDown, ArrowLeft, ArrowRight, ArrowUp, X } from 'lucide-react';
import type { EngineState } from '../types';
import type { ExactView } from '../precision/types';
import { validateExactView } from '../precision/coordinates';
import { CONTROL_LIMITS } from '../lib/controls';
import type { ControlKey } from '../lib/controls';
import type { Destination } from './destinations';
import { Disclosure, Formula, IconButton, NumberInput, Range, Switch } from './UI';

type Props = {
  state: EngineState;
  exact: ExactView;
  destination: Destination;
  onChange: (p: Partial<EngineState>) => void;
  onExact: (v: ExactView) => void;
  onReset: () => void;
  onFly: (key: string) => void;
  onGuide: () => void;
  onMotion: () => void;
  onClose: () => void;
};
const TABS = [
  { id: 'model', label: 'Model' },
  { id: 'material', label: 'Material' },
  { id: 'camera', label: 'View' },
] as const;
const MAP_NAME: Record<EngineState['scene'], string> = {
  mandelbulb: 'Triplex power map, iterated from 0',
  mandelbox: 'Box fold, sphere fold, scale',
  quaternion: 'Quaternion Julia set, three-dimensional slice',
  mandelbrot: 'Mandelbrot set: orbit of 0 for each c',
  julia: 'Julia set: orbit of each z for one c',
  landscape: 'Escape time over the parameter plane',
};
export function Inspector({
  state,
  exact,
  destination,
  onChange,
  onExact,
  onReset,
  onFly,
  onGuide,
  onMotion,
  onClose,
}: Props) {
  const [tab, setTab] = useState<(typeof TABS)[number]['id']>('model');
  const [coordinateError, setCoordinateError] = useState('');
  const [draft, setDraft] = useState({
    re: exact.center.re,
    im: exact.center.im,
    span: exact.span,
    jre: exact.julia.re,
    jim: exact.julia.im,
  });
  const plane = state.scene === 'mandelbrot' || state.scene === 'julia';
  const volume = ['mandelbulb', 'mandelbox', 'quaternion'].includes(state.scene);
  useEffect(
    () =>
      setDraft({
        re: exact.center.re,
        im: exact.center.im,
        span: exact.span,
        jre: exact.julia.re,
        jim: exact.julia.im,
      }),
    [exact.center.re, exact.center.im, exact.span, exact.julia.re, exact.julia.im],
  );
  const control = (key: ControlKey, label: string, step: number) => {
    const [, min, max] = CONTROL_LIMITS[key];
    return (
      <Range
        key={key}
        label={label}
        value={state.controls[key]}
        min={min}
        max={max}
        step={step}
        onChange={(value) => onChange({ controls: { ...state.controls, [key]: value } })}
      />
    );
  };
  const applyCoordinates = () => {
    try {
      onExact(
        validateExactView({
          ...exact,
          center: { re: draft.re, im: draft.im },
          span: draft.span,
          julia: { re: draft.jre, im: draft.jim },
        }),
      );
      setCoordinateError('');
    } catch (e) {
      setCoordinateError((e as Error).message);
    }
  };
  const changePalette = (palette: ExactView['palette']) => {
    onChange({ palette: palette === 'aurora' ? 'glacier' : palette });
    onExact({ ...exact, palette });
  };
  const palette = plane ? exact.palette : state.palette;
  return (
    <aside className="ob-inspector" aria-label="Fractal inspector">
      <div className="ob-panel-top">
        <div className="ob-tabs" role="tablist" aria-label="Inspector sections">
          {TABS.map(({ id, label }) => (
            <button
              key={id}
              role="tab"
              aria-selected={tab === id}
              onClick={() => setTab(id)}
              className={tab === id ? 'active' : ''}
            >
              {label}
            </button>
          ))}
        </div>
        <IconButton label="Hide inspector" onClick={onClose}>
          <X size={15} />
        </IconButton>
      </div>
      <div className="ob-inspector-scroll">
        {tab === 'model' && (
          <>
            <div className="ob-equation">
              <Formula scene={state.scene} power={state.power} />
              <span>{MAP_NAME[state.scene]}</span>
            </div>
            {(state.scene === 'mandelbulb' || state.scene === 'mandelbox') && (
              <Range
                label={state.scene === 'mandelbox' ? 'Fold scale' : 'Power'}
                value={state.power}
                min={state.scene === 'mandelbox' ? 1.2 : 2}
                max={state.scene === 'mandelbox' ? 3 : 16}
                step={0.05}
                onChange={(power) => onChange({ power })}
                format={(n) =>
                  `${state.scene === 'mandelbox' ? '−' : ''}${n.toFixed(n % 1 === 0 ? 0 : 2)}`
                }
              />
            )}
            <Range
              label="Iterations"
              value={plane ? exact.iterations : state.iterations}
              min={plane ? 64 : state.scene === 'landscape' ? 32 : 2}
              max={
                plane
                  ? 20000
                  : state.scene === 'landscape'
                    ? 512
                    : state.scene === 'mandelbox'
                      ? 40
                      : 64
              }
              step={plane ? 64 : 1}
              onChange={(iterations) =>
                plane ? onExact({ ...exact, iterations }) : onChange({ iterations })
              }
              description={
                plane
                  ? 'The budget per pixel. Raise it to resolve points that escape slowly.'
                  : undefined
              }
            />
            {plane && (
              <NumberInput
                label="Iterations, exact"
                value={exact.iterations}
                min={64}
                max={20000}
                step={1}
                onChange={(iterations) => onExact({ ...exact, iterations: Math.round(iterations) })}
              />
            )}
            {volume && (
              <>
                <Range
                  label="Surface detail"
                  value={state.detail}
                  min={0}
                  max={1}
                  step={0.01}
                  onChange={(detail) => onChange({ detail })}
                  format={(n) => `${Math.round(n * 100)}%`}
                />
                <Range
                  label="Escape radius"
                  value={state.bailout}
                  min={2}
                  max={32}
                  step={0.5}
                  onChange={(bailout) => onChange({ bailout })}
                />
              </>
            )}
            {state.scene === 'quaternion' && (
              <>
                <Range
                  label="Slice, fourth coordinate"
                  value={state.slice}
                  min={-2}
                  max={2}
                  step={0.005}
                  onChange={(slice) => onChange({ slice })}
                />
                <div className="ob-field-pair">
                  <NumberInput
                    label="c, real"
                    value={state.julia[0]}
                    min={-4}
                    max={4}
                    onChange={(n) => onChange({ julia: [n, state.julia[1]] })}
                  />
                  <NumberInput
                    label="c, imaginary"
                    value={state.julia[1]}
                    min={-4}
                    max={4}
                    onChange={(n) => onChange({ julia: [state.julia[0], n] })}
                  />
                </div>
              </>
            )}
            {plane && (
              <form
                className="ob-coordinate-form"
                onSubmit={(e) => {
                  e.preventDefault();
                  applyCoordinates();
                }}
              >
                <h3 className="ob-section-title">Exact coordinates</h3>
                {(
                  [
                    { id: 're', label: 'Center, real' },
                    { id: 'im', label: 'Center, imaginary' },
                    { id: 'span', label: 'Vertical span' },
                    ...(state.scene === 'julia'
                      ? [
                          { id: 'jre', label: 'c, real' },
                          { id: 'jim', label: 'c, imaginary' },
                        ]
                      : []),
                  ] as { id: keyof typeof draft; label: string }[]
                ).map(({ id, label }) => (
                  <label className="ob-field" key={id}>
                    <span>{label}</span>
                    <input
                      type="text"
                      spellCheck={false}
                      value={draft[id]}
                      onChange={(e) => setDraft({ ...draft, [id]: e.target.value })}
                    />
                  </label>
                ))}
                {coordinateError && (
                  <p className="ob-inline-error" role="alert">
                    {coordinateError}
                  </p>
                )}
                <button type="submit" className="ob-button">
                  Apply coordinates
                </button>
                <p className="ob-micro">
                  Decimal strings are kept exactly. Rendering rounds them and stops at the iteration
                  budget. Span may run from 32 down to 10⁻²⁰⁰.
                </p>
              </form>
            )}
            {state.scene === 'landscape' && (
              <>
                {control('reliefHeight', 'Relief height', 0.05)}
                {control('contourDensity', 'Contour density', 1)}
                <div className="ob-field-pair">
                  <NumberInput
                    label="Center, real"
                    value={state.center[0]}
                    min={-4}
                    max={4}
                    onChange={(n) => onChange({ center: [n, state.center[1]] })}
                  />
                  <NumberInput
                    label="Center, imaginary"
                    value={state.center[1]}
                    min={-4}
                    max={4}
                    onChange={(n) => onChange({ center: [state.center[0], n] })}
                  />
                </div>
                <NumberInput
                  label="Plane span"
                  value={state.scale}
                  min={0.0001}
                  max={12}
                  onChange={(scale) => onChange({ scale })}
                />
              </>
            )}
          </>
        )}
        {tab === 'material' && (
          <>
            <div className="ob-palettes" role="group" aria-label="Palette">
              {(
                [
                  'glacier',
                  'ember',
                  'violet',
                  'mono',
                  ...(plane ? ['aurora'] : []),
                ] as ExactView['palette'][]
              ).map((p) => (
                <button
                  key={p}
                  className={palette === p ? 'selected' : ''}
                  onClick={() => changePalette(p)}
                  aria-label={`${p} palette`}
                  aria-pressed={palette === p}
                >
                  <i className={`ob-swatch ${p}`} />
                  <span>{p}</span>
                </button>
              ))}
            </div>
            <Range
              label="Exposure"
              value={state.exposure}
              min={0.2}
              max={3}
              step={0.05}
              onChange={(exposure) => onChange({ exposure })}
            />
            {!plane && (
              <>
                {control('gamma', 'Gamma', 0.05)}
                {control('contrast', 'Contrast', 0.05)}
                {control('saturation', 'Saturation', 0.05)}
                <Range
                  label="Orbit trap influence"
                  value={state.orbitTrap}
                  min={0}
                  max={1}
                  step={0.01}
                  onChange={(orbitTrap) => onChange({ orbitTrap })}
                />
              </>
            )}
            {volume && (
              <Disclosure title="Lighting" open>
                {control('lightAzimuth', 'Azimuth', 1)}
                {control('lightElevation', 'Elevation', 1)}
                {control('lightIntensity', 'Key light', 0.05)}
                {control('ambientIntensity', 'Ambient light', 0.05)}
              </Disclosure>
            )}
            <p className="ob-micro">
              Colour is a display choice. It does not change the iteration.
            </p>
          </>
        )}
        {tab === 'camera' && (
          <>
            <label className="ob-field">
              <span>Rendering quality</span>
              <select
                value={state.quality}
                onChange={(e) => onChange({ quality: e.target.value as EngineState['quality'] })}
              >
                <option value="auto">Adaptive</option>
                <option value="high">High detail</option>
                <option value="balanced">Balanced</option>
                <option value="low">Low power</option>
              </select>
            </label>
            {volume && (
              <>
                <label className="ob-field">
                  <span>Volume precision</span>
                  <select
                    value={state.volumePrecision}
                    onChange={(e) =>
                      onChange({
                        volumePrecision: e.target.value as EngineState['volumePrecision'],
                      })
                    }
                  >
                    <option value="auto">Automatic · GPU / float64</option>
                    <option value="gpu">GPU · float32</option>
                    <option value="float64">CPU · float64 refinement</option>
                  </select>
                </label>
                <Switch
                  label="Orbit animation"
                  checked={state.autoRotate}
                  onChange={() =>
                    onChange({
                      autoRotate: !state.autoRotate,
                      camera: {
                        yaw: state.camera.yaw,
                        pitch: state.camera.pitch,
                        distance: state.camera.distance,
                      },
                    })
                  }
                />
                {control('animationSpeed', 'Orbit speed', 0.1)}
                {control('fov', 'Field of view', 0.5)}
                {control('flightSpeed', 'Flight speed', 0.1)}
                <h3 className="ob-section-title">Free flight</h3>
                <div className="ob-flight">
                  <button onClick={() => onFly('q')}>Q down</button>
                  <button onClick={() => onFly('w')} aria-label="Fly forward">
                    <ArrowUp size={15} />
                  </button>
                  <button onClick={() => onFly('e')}>E up</button>
                  <button onClick={() => onFly('a')} aria-label="Fly left">
                    <ArrowLeft size={15} />
                  </button>
                  <button onClick={() => onFly('s')} aria-label="Fly backward">
                    <ArrowDown size={15} />
                  </button>
                  <button onClick={() => onFly('d')} aria-label="Fly right">
                    <ArrowRight size={15} />
                  </button>
                </div>
                <button className="ob-button" onClick={onMotion}>
                  Open motion studio
                </button>
                <p className="ob-micro">
                  Scrolling approaches the point under the cursor and slows near the surface.
                  Distance estimates are numerical approximations.
                </p>
              </>
            )}
            {!plane && (
              <Switch
                label="Reference grid"
                checked={state.showGrid}
                onChange={() => onChange({ showGrid: !state.showGrid })}
              />
            )}
            <button className="ob-button" onClick={onReset}>
              Reset this view
            </button>
            {plane && (
              <p className="ob-micro">
                Drag pans. Scroll or pinch zooms about the pointer. Arrow keys pan, + and − zoom,
                Home resets. On the Mandelbrot set, shift-click picks the parameter for a Julia set.
              </p>
            )}
          </>
        )}
        <div className="ob-question-card">
          <h3>Question</h3>
          <p>{destination.question}</p>
          <button className="ob-link" onClick={onGuide}>
            Field guide
          </button>
        </div>
      </div>
    </aside>
  );
}
