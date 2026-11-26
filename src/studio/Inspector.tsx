import { useEffect, useState } from 'react';
import {
  ArrowDown,
  ArrowLeft,
  ArrowRight,
  ArrowUp,
  Check,
  Crosshair,
  SlidersHorizontal,
  Sun,
  Video,
  RotateCcw,
  Move3D,
  BookOpen,
} from 'lucide-react';
import type { EngineState } from '../types';
import type { ExactView } from '../precision/types';
import { validateExactView } from '../precision/coordinates';
import { CONTROL_LIMITS } from '../lib/controls';
import type { ControlKey } from '../lib/controls';
import type { Destination } from './destinations';
import { Range, Switch, NumberInput, Disclosure } from './UI';

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
}: Props) {
  const [tab, setTab] = useState<'model' | 'material' | 'camera'>('model');
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
  return (
    <aside className="ob-inspector" aria-label="Fractal inspector">
      <div className="ob-panel-top">
        <span className="ob-eyebrow">INSPECTOR</span>
        <span className="ob-small-label">
          {plane ? 'Complex plane' : state.scene === 'landscape' ? 'Height field' : '3D volume'}
        </span>
      </div>
      <div className="ob-segments" role="tablist" aria-label="Inspector sections">
        {(
          [
            { id: 'model', label: 'Model', Icon: SlidersHorizontal },
            { id: 'material', label: 'Material', Icon: Sun },
            { id: 'camera', label: 'View', Icon: Video },
          ] as const
        ).map(({ id, label, Icon }) => (
          <button
            key={id}
            role="tab"
            aria-selected={tab === id}
            onClick={() => setTab(id)}
            className={tab === id ? 'active' : ''}
          >
            <Icon size={14} />
            {label}
          </button>
        ))}
      </div>
      <div className="ob-inspector-scroll">
        {tab === 'model' && (
          <>
            <div className="ob-equation">
              <span>THE REPEATED RULE</span>
              <code>
                {state.scene === 'mandelbulb'
                  ? `zₙ₊₁ = sphericalPower${state.power}(zₙ) + c`
                  : state.scene === 'mandelbox'
                    ? `zₙ₊₁ = −${state.power} · fold(zₙ) + c`
                    : state.scene === 'quaternion'
                      ? 'qₙ₊₁ = qₙ² + c'
                      : state.scene === 'julia'
                        ? 'zₙ₊₁ = zₙ² + c,  c fixed'
                        : 'z₀ = 0,  zₙ₊₁ = zₙ² + c'}
              </code>
            </div>
            {(state.scene === 'mandelbulb' || state.scene === 'mandelbox') && (
              <div className="ob-primary-control">
                <div>
                  <span>{state.scene === 'mandelbox' ? 'Fold scale' : 'Power'}</span>
                  <strong>
                    {state.scene === 'mandelbox' ? '−' : ''}
                    {state.power.toFixed(state.power % 1 === 0 ? 0 : 2)}
                  </strong>
                </div>
                <Range
                  label={state.scene === 'mandelbox' ? 'Magnitude' : 'Spherical exponent'}
                  value={state.power}
                  min={state.scene === 'mandelbox' ? 1.2 : 2}
                  max={state.scene === 'mandelbox' ? 3 : 16}
                  step={0.05}
                  onChange={(power) => onChange({ power })}
                />
              </div>
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
                  ? 'A finite observation budget. Increase it to resolve slow-escaping boundary points.'
                  : 'How many times the equation is repeated.'
              }
            />
            {plane && (
              <NumberInput
                label="Exact iteration budget"
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
                  label="Fourth-dimensional slice"
                  value={state.slice}
                  min={-2}
                  max={2}
                  step={0.005}
                  onChange={(slice) => onChange({ slice })}
                />
                <div className="ob-field-pair">
                  <NumberInput
                    label="c · real"
                    value={state.julia[0]}
                    min={-4}
                    max={4}
                    onChange={(n) => onChange({ julia: [n, state.julia[1]] })}
                  />
                  <NumberInput
                    label="c · imaginary"
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
                <div className="ob-section-title">
                  <Crosshair size={13} />
                  <span>Exact coordinates</span>
                </div>
                {(
                  [
                    { id: 're', label: 'Center · real' },
                    { id: 'im', label: 'Center · imaginary' },
                    { id: 'span', label: 'Vertical span' },
                    ...(state.scene === 'julia'
                      ? [
                          { id: 'jre', label: 'Parameter c · real' },
                          { id: 'jim', label: 'Parameter c · imaginary' },
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
                <button type="submit" className="ob-button ob-subtle">
                  <Check size={14} />
                  Apply coordinates
                </button>
                <p className="ob-micro">
                  Decimal coordinates stay exact. Rendering uses rounded arithmetic and a finite
                  budget. Supported span: 32 to 10⁻²⁰⁰.
                </p>
              </form>
            )}
            {state.scene === 'landscape' && (
              <>
                {control('reliefHeight', 'Relief height', 0.05)}
                {control('contourDensity', 'Contour density', 1)}
                <div className="ob-field-pair">
                  <NumberInput
                    label="Center · real"
                    value={state.center[0]}
                    min={-4}
                    max={4}
                    onChange={(n) => onChange({ center: [n, state.center[1]] })}
                  />
                  <NumberInput
                    label="Center · imaginary"
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
            <div className="ob-section-title">COLOR PALETTE</div>
            <div className="ob-palettes">
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
                  className={(plane ? exact.palette : state.palette) === p ? 'selected' : ''}
                  onClick={() => changePalette(p)}
                  aria-label={`${p} palette`}
                  aria-pressed={(plane ? exact.palette : state.palette) === p}
                >
                  <i className={`ob-swatch ${p}`}>
                    {(plane ? exact.palette : state.palette) === p && <Check size={14} />}
                  </i>
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
              Color reveals numerical structure. A palette change does not change the underlying
              equation.
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
                <div className="ob-section-title">
                  <Move3D size={14} />
                  FREE FLIGHT
                </div>
                <div className="ob-flight">
                  <button onClick={() => onFly('q')}>Q · Down</button>
                  <button onClick={() => onFly('w')} aria-label="Fly forward">
                    <ArrowUp size={16} />
                  </button>
                  <button onClick={() => onFly('e')}>E · Up</button>
                  <button onClick={() => onFly('a')} aria-label="Fly left">
                    <ArrowLeft size={16} />
                  </button>
                  <button onClick={() => onFly('s')} aria-label="Fly backward">
                    <ArrowDown size={16} />
                  </button>
                  <button onClick={() => onFly('d')} aria-label="Fly right">
                    <ArrowRight size={16} />
                  </button>
                </div>
                <button className="ob-button ob-subtle" onClick={onMotion}>
                  <Video size={15} />
                  Open motion studio
                </button>
                <p className="ob-micro">
                  Scroll toward a feature to approach it. Movement slows near the surface. Distance
                  estimates guide navigation; they are numerical approximations.
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
            <button className="ob-button ob-subtle" onClick={onReset}>
              <RotateCcw size={14} />
              Reset this view
            </button>
            {plane && (
              <p className="ob-micro">
                Drag to pan. Scroll or pinch to zoom around the pointer. In Mandelbrot, shift-click
                selects a Julia parameter. Arrow keys pan; + / − zoom.
              </p>
            )}
          </>
        )}
        <button className="ob-question-card" onClick={onGuide}>
          <BookOpen size={16} />
          <span>
            <small>A QUESTION TO FOLLOW</small>
            <strong>{destination.question}</strong>
            <em>
              Open the field guide <ArrowRight size={12} />
            </em>
          </span>
        </button>
      </div>
    </aside>
  );
}
