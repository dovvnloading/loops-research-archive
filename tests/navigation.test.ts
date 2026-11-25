import assert from 'node:assert/strict';
import {test} from 'node:test';
import {DEFAULT_STATE} from '../src/presets.ts';
import {basis,eye,ray,norm,add,mul,estimate,clearanceAt,iterationBudget,dolly,flightStep,precisionFloor} from '../src/engine/navigation.ts';
import {validateState} from '../src/lib/session.ts';
test('camera basis is orthonormal; center ray points forward',()=>{
  const c=DEFAULT_STATE.camera;const b=basis(c);
  assert.ok(Math.abs(norm(b.forward)-1)<1e-12);
  assert.ok(Math.abs(norm(b.right)-1)<1e-12);
  assert.deepEqual(ray(c,0,0),b.forward);
  assert.ok(norm(add(eye(c),mul(b.forward,c.distance)))<1e-12);
});
test('distance estimates distinguish a bounded origin from exterior',()=>{
  assert.equal(estimate(DEFAULT_STATE,[0,0,0]),0);
  assert.ok(estimate(DEFAULT_STATE,[0,0,3])>0);
  assert.ok(iterationBudget(DEFAULT_STATE,1e-5)>iterationBudget(DEFAULT_STATE,1));
  assert.equal(iterationBudget({...DEFAULT_STATE,iterations:64},1e-9),64);
});
test('dolly enters free flight, approaches the actual field, and can retreat',()=>{
  let s=validateState(DEFAULT_STATE);const start=clearanceAt(s,eye(s.camera));
  for(let i=0;i<24;i++)s={...s,camera:dolly(s,.8)};
  assert.ok(s.camera.position);
  const near=clearanceAt(s,eye(s.camera));
  assert.ok(near<start*.1);
  assert.ok(near>=precisionFloor(eye(s.camera))*2);
  const back={...s,camera:flightStep(s,'s')};
  assert.ok(clearanceAt(back,eye(back.camera))>near);
});
test('cursor flight rays differ and flight position survives session validation',()=>{
  const s=validateState(DEFAULT_STATE);
  assert.notDeepEqual(ray(s.camera,.3,.2),ray(s.camera,-.3,-.2));
  const c=dolly(s,.8,.25,.1);
  assert.deepEqual(validateState({...s,camera:c}).camera.position,c.position);
  assert.equal(validateState({...s,camera:{...c,position:[NaN,0,0]}}).camera.position,undefined);
  assert.equal(validateState({...s,scene:'julia',camera:c}).camera.position,undefined);
});
