import assert from 'node:assert/strict';
import {test} from 'node:test';
import {DEFAULT_STATE} from '../src/presets.ts';
import {basis,clearanceAt,dolly,eye,iterationBudget,precisionFloor,volumeMode} from '../src/engine/navigation.ts';
import {prepareVolume,traceVolume} from '../src/engine/volume64.ts';
import {validateState} from '../src/lib/session.ts';
test('binary64 navigation and evaluation allow a smaller floor than GPU',()=>{
  let s=validateState({...DEFAULT_STATE,volumePrecision:'float64'});
  const p=eye(s.camera);
  assert.ok(precisionFloor(p,'float64')<precisionFloor(p)*1e-5);
  assert.equal(volumeMode(s),'float64');
  assert.ok(iterationBudget(s,1e-10,'float64')>iterationBudget(s,1e-10,'gpu'));
  for(let i=0;i<80;i++)s={...s,camera:dolly(s,.6)};
  const d=clearanceAt(s,eye(s.camera));
  assert.ok(d<2e-6,'binary64 approach '+d);
  assert.ok(d>=precisionFloor(eye(s.camera),'float64')*2);
  assert.equal(validateState(s).volumePrecision,'float64');
});
test('binary64 raymarch produces actual field hits and spatially varied pixels',()=>{
  const s=validateState({...DEFAULT_STATE,volumePrecision:'float64'});
  const ro=eye(s.camera),rd=basis(s.camera).forward;
  const hit=traceVolume(s,ro,rd,32,1e-4);
  assert.ok(hit.hit);
  assert.ok(hit.travel>0);
  const frame=prepareVolume({state:s,width:20,height:16,preview:true});
  const colors=new Set<string>();
  for(let y=0;y<16;y++)for(let x=0;x<20;x++)colors.add(frame.pixel(x,y).join(','));
  assert.ok(colors.size>8);
});
test('automatic precision chooses binary64 close to the field; old sessions remain auto',()=>{
  let s=validateState({...DEFAULT_STATE,volumePrecision:'gpu'});
  for(let i=0;i<35;i++)s={...s,camera:dolly(s,.6)};
  assert.equal(volumeMode({...s,volumePrecision:'auto'}),'float64');
  assert.equal(validateState({}).volumePrecision,'auto');
});
