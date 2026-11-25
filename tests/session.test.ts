import assert from 'node:assert/strict';
import { test } from 'node:test';
import { validateState, readSession, shareURL } from '../src/lib/session.ts';
import { DEFAULT_STATE } from '../src/presets.ts';

function withLocation<T>(url: string, action: () => T): T {
  const previous = Object.getOwnPropertyDescriptor(globalThis, 'location');
  Object.defineProperty(globalThis, 'location', { configurable: true, value: new URL(url) });
  try { return action(); }
  finally {
    if (previous) Object.defineProperty(globalThis, 'location', previous);
    else Reflect.deleteProperty(globalThis, 'location');
  }
}

test('malformed imported JSON and non-finite coordinates cannot poison the renderer', () => {
  for (const value of [null, false, 42, 'not a session', [], { scene: { toString: null }, palette: {}, quality: [] }]) {
    const state = validateState(value);
    assert.equal(state.scene, 'mandelbulb');
    assert.equal(state.palette, 'glacier');
    assert.equal(state.quality, 'auto');
  }
  const state = validateState({
    scene: 'julia', center: [Infinity, NaN], julia: [-Infinity, '0.2'],
    camera: { yaw: NaN, pitch: Infinity, distance: -Infinity },
    power: NaN, iterations: Infinity, scale: NaN, exposure: -Infinity,
    autoRotate: 'true', detail: {},
  });
  assert.deepEqual(state.center, [-0.5, 0]);
  assert.deepEqual(state.julia, DEFAULT_STATE.julia);
  assert.deepEqual(state.camera, DEFAULT_STATE.camera);
  assert.equal(state.autoRotate, false);
  assert.equal(state.iterations, 384);
  for (const value of [state.power, state.iterations, state.scale, state.exposure, state.detail]) assert.ok(Number.isFinite(value));
});

test('numerical exploration boundaries are preserved and excessive imports are limited', () => {
  const lower = validateState({ scene: 'mandelbox', power: 1.2, iterations: 2, camera: { distance: 1.65, pitch: -1.4 } });
  assert.equal(lower.power, 1.2);
  assert.equal(lower.iterations, 2);
  assert.equal(lower.camera.distance, 1.65);
  assert.equal(lower.camera.pitch, -1.4);
  const excessive = validateState({ scene: 'mandelbox', power: 99, iterations: 1e9, camera: { distance: 100, pitch: 7 } });
  assert.equal(excessive.power, 3);
  assert.equal(excessive.iterations, 40);
  assert.equal(excessive.camera.distance, 14);
  assert.equal(excessive.camera.pitch, 1.4);
  const plane = validateState({ scene: 'julia', scale: 1e-30, iterations: 1e9, julia: [-4, 4] });
  assert.equal(plane.scale, 1e-7);
  assert.equal(plane.iterations, 4096);
  assert.deepEqual(plane.julia, [-4, 4]);
  const terrain = validateState({ scene: 'landscape', scale: 1e-30, iterations: 3, camera: { pitch: -1 } });
  assert.equal(terrain.scale, 1e-4);
  assert.equal(terrain.iterations, 32);
  assert.equal(terrain.camera.pitch, 0.3);
  assert.equal(validateState({ scene: 'mandelbrot', autoRotate: true }).autoRotate, false);
  assert.equal(validateState({ scene: 'julia', autoRotate: true }).autoRotate, true);
});

test('a share URL reproduces a valid numerical view and workspace at a project subpath', () => {
  const original = validateState({
    ...DEFAULT_STATE, scene: 'julia', center: [-0.743643887037151, 0.13182590420533],
    scale: 1e-7, iterations: 2048, julia: [-0.74543, 0.11301],
    camera: { yaw: -2.75, pitch: 0.75, distance: 4.6 }, palette: 'ember',
  });
  const shared = withLocation('https://example.test/loops-research-archive/?obsolete=yes#papers', () => shareURL(original, 'lab'));
  const url = new URL(shared);
  assert.equal(url.pathname, '/loops-research-archive/');
  assert.equal(url.hash, '');
  assert.equal(url.searchParams.has('obsolete'), false);
  assert.equal(url.searchParams.get('workspace'), 'lab');
  const restored = withLocation(shared, readSession);
  assert.equal(restored.workspace, 'lab');
  assert.deepEqual(restored.state, original);
});

test('broken, oversized, and unsupported shared sessions fall back without losing legacy navigation', () => {
  for (const view of ['not-base64!!', btoa('null'), btoa('{broken json'), btoa(JSON.stringify({ v: 900, state: { scene: 'julia' } })), 'a'.repeat(10_001)]) {
    const restored = withLocation(`https://example.test/loops/?view=${encodeURIComponent(view)}#ledger`, readSession);
    assert.deepEqual(restored.state, DEFAULT_STATE);
    assert.equal(restored.workspace, 'archive');
  }
  assert.equal(withLocation('https://example.test/loops/#model', readSession).workspace, 'dynamics');
  assert.equal(withLocation('https://example.test/loops/?workspace=not-real', readSession).workspace, 'explore');
});

test('validated state owns its coordinate arrays so edits do not mutate presets or input', () => {
  const input = { ...DEFAULT_STATE, camera: { ...DEFAULT_STATE.camera }, center: [0, 1], julia: [-1, 0] };
  const validated = validateState(input);
  validated.center[0] = 2;
  validated.julia[1] = 0.5;
  validated.camera.distance = 10;
  assert.deepEqual(input.center, [0, 1]);
  assert.deepEqual(input.julia, [-1, 0]);
  assert.equal(input.camera.distance, 3.6);
  assert.deepEqual(DEFAULT_STATE.center, [-0.5, 0]);
});

test('legacy sessions inherit every instrument default and invalid advanced values are bounded', () => {
  const defaults=DEFAULT_STATE.controls;
  assert.deepEqual(validateState({}).controls,defaults);
  const next=validateState({controls:{fov:999,gamma:NaN,contrast:-1,saturation:0,lightAzimuth:-999,planeBailout:99,flightSpeed:.01,reliefHeight:5}});
  assert.equal(next.controls.fov,95);
  assert.equal(next.controls.gamma,defaults.gamma);
  assert.equal(next.controls.contrast,.5);
  assert.equal(next.controls.saturation,0);
  assert.equal(next.controls.lightAzimuth,-180);
  assert.equal(next.controls.planeBailout,64);
  assert.equal(next.controls.flightSpeed,.1);
  assert.equal(next.controls.reliefHeight,3);
  assert.notEqual(next.controls,defaults);
});
test('advanced parameters survive share-link round trips', () => {
  const original=validateState({...DEFAULT_STATE,controls:{...DEFAULT_STATE.controls,fov:38,gamma:1.8,saturation:.4,bandFrequency:.75,lightAzimuth:83,reliefHeight:1.8}});
  const shared=withLocation('https://example.test/loops/',()=>shareURL(original,'explore'));
  assert.deepEqual(withLocation(shared,readSession).state.controls,original.controls);
});
