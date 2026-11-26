import assert from 'node:assert/strict';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';
import { build } from 'esbuild';
import { DEFAULT_STATE } from '../src/presets.ts';
import type { MotionPath } from '../src/studio/MotionStudio.tsx';

// The module also contains its React view. Bundle JSX in memory so numerical
// path tests can run in Node without a browser or a generated source file.
const compiled = await build({ entryPoints: [fileURLToPath(new URL('../src/studio/MotionStudio.tsx', import.meta.url))], bundle: true, format: 'esm', platform: 'node', write: false, loader: { '.css': 'empty' }, logLevel: 'silent' });
const { sampleMotionPath, validateMotionPath } = await import(`data:text/javascript;base64,${Buffer.from(compiled.outputFiles[0].text).toString('base64')}`) as typeof import('../src/studio/MotionStudio.tsx');

function path(loop = false): MotionPath {
  const first = structuredClone(DEFAULT_STATE), last = structuredClone(DEFAULT_STATE);
  first.camera.yaw = 170 * Math.PI / 180; last.camera.yaw = -170 * Math.PI / 180;
  first.camera.distance = 3; last.camera.distance = 5;
  first.exposure = 1; last.exposure = 2;
  first.controls.lightAzimuth = 170; last.controls.lightAzimuth = -170;
  first.controls.bandPhase = .1; last.controls.bandPhase = 2 * Math.PI - .1;
  return { format: 'loops-motion', version: 1, scene: 'mandelbulb', duration: 12, easing: 'linear', loop, frames: [{ id: 'first', title: 'First', state: first }, { id: 'last', title: 'Last', state: last }] };
}
const near = (a: number, b: number) => assert.ok(Math.abs(a - b) < 1e-10, `${a} ≠ ${b}`);

test('camera and lighting cross angular boundaries by the short route', () => {
  const halfway = sampleMotionPath(path(), .5);
  near(Math.abs(halfway.camera.yaw), Math.PI);
  near(Math.abs(halfway.controls.lightAzimuth), 180);
  assert.ok(halfway.controls.bandPhase < 1e-10 || Math.abs(halfway.controls.bandPhase - 2 * Math.PI) < 1e-10);
  near(halfway.camera.distance, 4); near(halfway.exposure, 1.5);
  assert.equal(halfway.volumePrecision, 'gpu');
  assert.equal(halfway.autoRotate, false);
});

test('a closed path reaches every frame and returns to its exact starting geometry', () => {
  const route = path(true), middle = sampleMotionPath(route, .5), end = sampleMotionPath(route, 1);
  near(middle.camera.distance, route.frames[1].state.camera.distance);
  near(end.camera.distance, route.frames[0].state.camera.distance);
  near(Math.sin(end.camera.yaw), Math.sin(route.frames[0].state.camera.yaw));
  near(Math.cos(end.camera.yaw), Math.cos(route.frames[0].state.camera.yaw));
  near(end.exposure, route.frames[0].state.exposure);
});

test('freeflight endpoints interpolate as world positions without mutating keyframes', () => {
  const route = path(); route.frames[0].state.camera.position = [1, 2, 3]; route.frames[1].state.camera.position = [3, 4, 5];
  const midpoint = sampleMotionPath(route, .5);
  assert.deepEqual(midpoint.camera.position, [2, 3, 4]);
  midpoint.camera.position![0] = 10; midpoint.controls.fov = 60;
  assert.deepEqual(route.frames[0].state.camera.position, [1, 2, 3]);
  assert.equal(route.frames[0].state.controls.fov, DEFAULT_STATE.controls.fov);
});

test('smooth timing eases into keyframes and fixed endpoints remain stable', () => {
  const route = path(); route.easing = 'smooth';
  const quarter = sampleMotionPath(route, .25);
  near(quarter.camera.distance, 3 + 2 * .15625);
  near(sampleMotionPath(route, 0).camera.distance, 3);
  near(sampleMotionPath(route, 1).camera.distance, 5);
  near(sampleMotionPath(route, -2).camera.distance, 3);
  near(sampleMotionPath(route, 4).camera.distance, 5);
});

test('motion imports enforce family, finite positions, frame limits and unique identities', () => {
  assert.equal(validateMotionPath(path()).frames.length, 2);
  const invalid = [
    { ...path(), version: 99 },
    { ...path(), duration: 91 },
    { ...path(), duration: Infinity },
    { ...path(), frames: [] },
    { ...path(), frames: [...path().frames, ...path().frames] },
    { ...path(), frames: [{ ...path().frames[0], state: { ...DEFAULT_STATE, scene: 'julia' } }] },
    { ...path(), frames: [{ ...path().frames[0], state: { ...DEFAULT_STATE, camera: { ...DEFAULT_STATE.camera, position: [Infinity, 0, 0] } } }] },
    { ...path(), frames: [{ ...path().frames[0], state: { ...DEFAULT_STATE, camera: { ...DEFAULT_STATE.camera, position: [14, 14, 14] } } }] },
  ];
  for (const item of invalid) assert.throws(() => validateMotionPath(item));
});
