import assert from 'node:assert/strict';
import { test } from 'node:test';
import { DEFAULT_CONTROLS, normalizeControls, projection, lightDirection, paletteColor, toneColor } from '../src/lib/controls.ts';
import { DEFAULT_STATE } from '../src/presets.ts';
import { ray } from '../src/engine/navigation.ts';
test('wide-angle projection changes off-axis rays but not center ray',()=>{
  const narrow=normalizeControls({fov:25}),wide=normalizeControls({fov:90});
  assert.ok(projection(wide)>projection(narrow));
  const camera=DEFAULT_STATE.camera;
  assert.deepEqual(ray(camera,0,0,projection(narrow)),ray(camera,0,0,projection(wide)));
  assert.notDeepEqual(ray(camera,.5,.25,projection(narrow)),ray(camera,.5,.25,projection(wide)));
});
test('light direction is normalized and tone controls produce bounded pixels',()=>{
  assert.ok(Math.abs(Math.hypot(...lightDirection(DEFAULT_CONTROLS))-1)<1e-12);
  assert.notDeepEqual(lightDirection(DEFAULT_CONTROLS),lightDirection(normalizeControls({lightAzimuth:100})));
  const rgb=paletteColor('glacier',.65);
  assert.ok(rgb[2]>rgb[1]&&rgb[1]>rgb[0]);
  const mono=toneColor(rgb,1,normalizeControls({saturation:0}));
  assert.equal(mono[0],mono[1]);assert.equal(mono[1],mono[2]);
  assert.notDeepEqual(toneColor(rgb,1,DEFAULT_CONTROLS),toneColor(rgb,1,normalizeControls({gamma:1.2})));
  assert.ok(toneColor(rgb,3,normalizeControls({saturation:2,contrast:1.8})).every(v=>v>=0&&v<=255));
});
