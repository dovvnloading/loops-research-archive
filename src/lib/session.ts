import type { EngineState, Workspace } from '../types';
import { DEFAULT_STATE } from '../presets.ts';
import { normalizeControls } from './controls.ts';

const scenes = ['mandelbulb','mandelbox','quaternion','mandelbrot','julia','landscape'];
const workspaces = ['explore','dynamics','atlas','lab','archive'];
function num(v: unknown, fallback: number, min: number, max: number) {return typeof v === 'number' && Number.isFinite(v) ? Math.min(max,Math.max(min,v)) : fallback;}
function pair(v: unknown, fallback:[number,number], min=-4, max=4):[number,number] {return Array.isArray(v)&&v.length===2 ? [num(v[0],fallback[0],min,max),num(v[1],fallback[1],min,max)] : [...fallback];}

export function validateState(value: unknown): EngineState {
  const x = value && typeof value==='object' ? value as Record<string,unknown> : {};
  const c = x.camera && typeof x.camera==='object' ? x.camera as Record<string,unknown> : {};
  const scene = typeof x.scene==='string' && scenes.includes(x.scene) ? x.scene as EngineState['scene'] : DEFAULT_STATE.scene;
  const plane = scene==='mandelbrot'||scene==='julia';
  const landscape = scene==='landscape';
  const position = !plane && !landscape && Array.isArray(c.position) && c.position.length===3 && c.position.every(v=>typeof v==='number'&&Number.isFinite(v)) && Math.hypot(...(c.position as number[]))<=14 ? [...c.position] as [number,number,number] : undefined;
  return {
    controls:normalizeControls(x.controls),
    scene, power:num(x.power,scene==='mandelbox'?2:8,scene==='mandelbox'?1.2:2,scene==='mandelbox'?3:16),
    iterations:Math.round(num(x.iterations,plane?384:landscape?160:12,plane||landscape?32:2,plane?4096:landscape?512:scene==='mandelbox'?40:64)),
    bailout:num(x.bailout,8,2,64),detail:num(x.detail,.65,0,1),exposure:num(x.exposure,1.1,.2,3),
    palette:typeof x.palette==='string' && ['glacier','ember','violet','mono'].includes(x.palette) ? x.palette as EngineState['palette'] : 'glacier',
    camera:{yaw:num(c.yaw,.35,-1e4,1e4),pitch:num(c.pitch,landscape?.75:.18,landscape?.3:-1.4,1.4),distance:num(c.distance,3.6,1.65,14),...(position?{position}:{})},
    center:pair(x.center,[-.5,0],-1e5,1e5),scale:num(x.scale,3.2,landscape?1e-4:1e-7,12),julia:pair(x.julia,[-.74543,.11301],-4,4),
    slice:num(x.slice,0,-2,2),autoRotate:!position&&scene!=='mandelbrot'&&x.autoRotate===true,showGrid:x.showGrid!==false,
    quality:typeof x.quality==='string' && ['auto','high','balanced','low'].includes(x.quality) ? x.quality as EngineState['quality'] : 'auto',orbitTrap:num(x.orbitTrap,.35,0,1),volumePrecision:x.volumePrecision==='float64'||x.volumePrecision==='gpu'?x.volumePrecision:'auto',
  };
}

export function readSession(): {state:EngineState;workspace:Workspace} {
  const params=new URLSearchParams(location.search);
  let state=DEFAULT_STATE;
  try {const raw=params.get('view');if(raw&&raw.length<10000){const data=JSON.parse(atob(raw.replace(/-/g,'+').replace(/_/g,'/')));if(data.v===1)state=validateState(data.state);}}catch{}
  const hash=location.hash.slice(1).split('?')[0];
  const legacy:Record<string,Workspace>={papers:'archive',formal:'archive',ledger:'archive',problems:'archive',model:'dynamics',archive:'archive'};
  const w=params.get('workspace') || legacy[hash] || hash;
  return {state,workspace:workspaces.includes(w) ? w as Workspace : 'explore'};
}

export function shareURL(state:EngineState,workspace:Workspace) {
  const u=new URL(location.href);u.hash='';u.search='';
  u.searchParams.set('view',btoa(JSON.stringify({v:1,state})).replace(/\+/g,'-').replace(/\//g,'_').replace(/=+$/,''));
  if(workspace!=='explore')u.searchParams.set('workspace',workspace);
  return u.toString();
}

export interface Bookmark {id:string;name:string;state:EngineState;created:string;}
export function readBookmarks():Bookmark[] {
  try {const x=JSON.parse(localStorage.getItem('loops.bookmarks.v1')||'[]');return Array.isArray(x)?x.filter(v=>typeof v?.name==='string').slice(0,24).map(v=>({...v,state:validateState(v.state)})):[];}catch{return [];}
}
export function writeBookmarks(values:Bookmark[]) {try{localStorage.setItem('loops.bookmarks.v1',JSON.stringify(values.slice(0,24)));return true;}catch{return false;}}

export function download(content:string,filename:string,type='application/json') {const link=document.createElement('a');link.href=content.startsWith('data:')?content:URL.createObjectURL(new Blob([content],{type}));link.download=filename;link.click();if(link.href.startsWith('blob:'))setTimeout(()=>URL.revokeObjectURL(link.href),1000);}
