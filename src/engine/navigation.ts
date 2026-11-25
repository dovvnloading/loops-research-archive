import type { EngineState, SceneId } from '../types';

export type Vec3 = [number, number, number];
type Camera = EngineState['camera'];
export const volumeScene = (s: SceneId) => s === 'mandelbulb' || s === 'mandelbox' || s === 'quaternion';
export const add = (a: Vec3,b: Vec3): Vec3 => [a[0]+b[0],a[1]+b[1],a[2]+b[2]];
export const mul = (a: Vec3,k: number): Vec3 => [a[0]*k,a[1]*k,a[2]*k];
export const norm = (a: Vec3) => Math.hypot(...a);
export const unit = (a: Vec3): Vec3 => mul(a,1/Math.max(norm(a),1e-30));
const cross = (a: Vec3,b: Vec3): Vec3 => [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];
export function basis(c: Camera) {
  const forward: Vec3 = [-Math.sin(c.yaw)*Math.cos(c.pitch),-Math.sin(c.pitch),-Math.cos(c.yaw)*Math.cos(c.pitch)];
  const right=unit(cross(forward,[0,1,0]));
  return {forward,right,up:cross(right,forward)};
}
export function eye(c: Camera): Vec3 {return c.position ? [...c.position] : mul(basis(c).forward,-c.distance);}
export function ray(c: Camera,x: number,y: number): Vec3 {
  const {forward,right,up}=basis(c);
  return unit(add(forward,add(mul(right,x*.97),mul(up,y*.97))));
}
// Conservative numerical floors, not a geometric error certificate.
export type VolumeMode = 'gpu' | 'float64';
export const DEEP_SWITCH = 2e-5;
export function precisionFloor(p: Vec3,mode:VolumeMode='gpu') {return (mode==='float64'?2e-12:2e-6)*Math.max(1,...p.map(Math.abs));}
export function volumeMode(s:EngineState,p=eye(s.camera)):VolumeMode {
  if(s.volumePrecision==='float64')return 'float64';
  if(s.volumePrecision==='gpu')return 'gpu';
  return estimate(s,p,s.iterations,'gpu')<DEEP_SWITCH*Math.max(1,...p.map(Math.abs))?'float64':'gpu';
}
export const navigationFloor=(s:EngineState,p:Vec3)=>precisionFloor(p,volumeMode(s,p));
export function iterationBudget(s: EngineState,clearance: number,mode:VolumeMode='gpu') {
  const cap=mode==='float64'?120:s.scene==='mandelbox'?40:64;
  const decades=Math.max(0,-Math.log10(Math.max(clearance,mode==='float64'?2e-12:2e-6)));
  return Math.min(cap,Math.max(s.iterations,Math.ceil(s.iterations+decades*(s.scene==='mandelbox'?4:6))));
}
// CPU copies of the numerical distance estimators. These are navigation heuristics,
// not certified lower bounds; the GPU is the final renderer.
export function estimate(s: EngineState,p: Vec3,iterations=s.iterations,mode:VolumeMode='gpu'): number {
  const cap=mode==='float64'?120:s.scene==='mandelbox'?40:64;
  const derivativeCap=mode==='float64'?1e150:1e30;
  let dr=1,r=0;
  if(s.scene==='mandelbox'){
    const c=mul(p,2);let z:Vec3=[...c];const scale=-Math.min(3,Math.max(1.2,s.power));
    for(let i=0;i<Math.min(cap,iterations);i++){
      z=z.map(x=>2*Math.max(-1,Math.min(1,x))-x) as Vec3;
      const f=Math.max(1,Math.min(4,1/Math.max(norm(z)**2,1e-5)));
      z=add(mul(z,scale*f),c);dr=Math.min(derivativeCap,dr*f*Math.abs(scale)+1);
    }
    return norm(z)/dr*.5;
  }
  if(s.scene==='quaternion'){
    let [x,y,z]=p,w=s.slice;
    for(let i=0;i<Math.min(cap,iterations);i++){
      r=Math.hypot(x,y,z,w);
      if(r>s.bailout)return .5*r*Math.log(r)/Math.max(dr,1e-12);
      dr=Math.min(derivativeCap,dr*Math.max(2*r,1e-6));
      [x,y,z,w]=[x*x-y*y-z*z-w*w+s.julia[0],2*x*y+s.julia[1],2*x*z+.18,2*x*w];
    }
    r=Math.hypot(x,y,z,w);
    return r>s.bailout?.5*r*Math.log(r)/Math.max(dr,1e-12):0;
  }
  let z:Vec3=[...p];
  const power=Math.min(16,Math.max(2,s.power));
  for(let i=0;i<Math.min(cap,iterations);i++){
    r=norm(z);
    if(r>s.bailout)return .5*r*Math.log(r)/Math.max(dr,1e-12);
    if(r<(mode==='float64'?1e-15:1e-7)){z=[...p];continue;}
    const theta=Math.acos(Math.max(-1,Math.min(1,z[2]/r)))*power;
    const phi=Math.atan2(z[1],z[0])*power;
    dr=Math.min(derivativeCap,power*r**(power-1)*dr+1);
    const zr=r**power;
    z=add([zr*Math.sin(theta)*Math.cos(phi),zr*Math.sin(theta)*Math.sin(phi),zr*Math.cos(theta)],p);
  }
  r=norm(z);
  return r>s.bailout?.5*r*Math.log(r)/Math.max(dr,1e-12):0;
}
export function clearanceAt(s: EngineState,p: Vec3) {
  const mode=volumeMode(s,p);
  let d=estimate(s,p,s.iterations,mode);
  d=estimate(s,p,iterationBudget(s,d,mode),mode);
  return Number.isFinite(d)?Math.max(0,d):0;
}
// March conservatively along the intended movement. Stop at the numerical surface
// instead of teleporting into a bounded orbit. This is not a collision proof.
export function travel(s: EngineState,direction: Vec3,amount: number): Camera {
  let p=eye(s.camera);const dir=unit(direction);
  let remaining=Math.max(0,Math.min(8,amount));
  for(let i=0;i<96&&remaining>0;i++){
    const d=clearanceAt(s,p),floor=navigationFloor(s,p);
    if(d<=floor*3) {
      // Allow retreat from a point very close to (or numerically on) a surface.
      const probe=Math.min(remaining,floor*8);
      const q=add(p,mul(dir,probe));
      if(norm(q)>14||clearanceAt(s,q)<=Math.max(d,floor*3))break;
      p=q;remaining-=probe;continue;
    }
    const step=Math.min(remaining,d*.45,.5);
    const q=add(p,mul(dir,step));
    if(norm(q)>14||clearanceAt(s,q)<navigationFloor(s,q)*2)break;
    p=q;remaining-=step;
  }
  return {...s.camera,position:p};
}
export function dolly(s: EngineState,multiplier: number,x=0,y=0): Camera {
  if(!Number.isFinite(multiplier)||multiplier<=0||multiplier===1)return s.camera;
  const p=eye(s.camera),d=clearanceAt(s,p);
  const direction=ray(s.camera,x,y);
  const amount=Math.min(3,Math.max(d,navigationFloor(s,p)*12)*Math.abs(Math.log(multiplier))*4);
  return travel(s,mul(direction,multiplier<1?1:-1),amount);
}
export function flightStep(s: EngineState,key: string): Camera {
  const {forward,right,up}=basis(s.camera);
  const dirs:Record<string,Vec3>={w:forward,s:mul(forward,-1),a:mul(right,-1),d:right,q:mul(up,-1),e:up};
  const dir=dirs[key];if(!dir)return s.camera;
  return travel(s,dir,Math.min(.6,Math.max(clearanceAt(s,eye(s.camera)),navigationFloor(s,eye(s.camera))*12)*.55));
}
