/** IEEE binary64 raymarcher. No tessellation, texture assets, or Float32 world coordinates. */
import type { EngineState } from '../types';
import { lightDirection, paletteColor, projection, toneColor } from '../lib/controls.ts';
import { add,basis,clearanceAt,estimate,eye,iterationBudget,mul,norm,precisionFloor,unit } from './navigation.ts';
import type { Vec3 } from './navigation.ts';

export interface VolumeFrame { state:EngineState; width:number; height:number; preview:boolean }
export interface VolumeSample { hit:boolean; travel:number; steps:number; epsilon:number; point:Vec3 }
const dot=(a:Vec3,b:Vec3)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2];
const clamp=(x:number,a=0,b=1)=>Math.max(a,Math.min(b,x));
export function traceVolume(s:EngineState,ro:Vec3,rd:Vec3,iterations:number,pixelAngle:number,maxSteps=420):VolumeSample {
  const radius=s.scene==='mandelbox'?6:s.scene==='quaternion'?Math.max(1.55,.5*(1+Math.sqrt(1+4*Math.hypot(...s.julia,.18)))+.05):Math.max(1.55,2**(1/(Math.max(s.power,2)-1))+.05);
  const b=dot(ro,rd),disc=b*b-dot(ro,ro)+radius*radius;
  let travel=0,epsilon=precisionFloor(ro,'float64'),point=ro;
  if(disc<=0)return {hit:false,travel,steps:0,epsilon,point};
  const far=-b+Math.sqrt(disc);travel=Math.max(0,-b-Math.sqrt(disc));
  for(let step=0;step<maxSteps&&travel<=far;step++){
    point=add(ro,mul(rd,travel));
    epsilon=Math.max(precisionFloor(point,'float64'),travel*pixelAngle);
    const d=estimate(s,point,iterations,'float64');
    if(!Number.isFinite(d))return {hit:false,travel,steps:step,epsilon,point};
    if(d<epsilon)return {hit:true,travel,steps:step+1,epsilon,point};
    travel+=Math.max(.58*d,epsilon*.5);
  }
  return {hit:false,travel,steps:maxSteps,epsilon,point};
}
function gradient(s:EngineState,p:Vec3,e:number,n:number,rd:Vec3):Vec3{
  const d=(x:number,y:number,z:number)=>estimate(s,add(p,[x,y,z]),n,'float64');
  const a=d(e,-e,-e),b=d(-e,-e,e),c=d(-e,e,-e),q=d(e,e,e);
  const g:Vec3=[a-b-c+q,-a-b+c+q,-a+b-c+q];
  return norm(g)>1e-28?unit(g):mul(rd,-1);
}
export function prepareVolume(frame:VolumeFrame){
  const s={...frame.state,volumePrecision:'float64' as const},ro=eye(s.camera),axes=basis(s.camera);
  const clearance=clearanceAt(s,ro),iterations=iterationBudget(s,clearance,'float64');
  const key=lightDirection(s.controls),rim=unit([3,1,-2]);
  const lens=projection(s.controls);
  const pixelAngle=lens/frame.height*(.85-.59*s.detail);
  const maxSteps=frame.preview?180:520;
  const pixel=(x:number,y:number):[number,number,number,number]=>{
    const u=(x+.5-frame.width/2)/frame.height,v=(frame.height/2-y-.5)/frame.height;
    const rd=unit(add(axes.forward,add(mul(axes.right,lens*u),mul(axes.up,lens*v))));
    const hit=traceVolume(s,ro,rd,iterations,pixelAngle,maxSteps);
    let rgb:Vec3=[.008,.012,.022];
    if(hit.hit){
      const e=hit.epsilon,p=hit.point;
      const n=gradient(s,p,e*1.8,iterations,rd),head=clamp(-dot(n,rd));
      let ao=1;
      if(!frame.preview){for(let i=1;i<=3;i++){
        const h=e*i*i*8;
        const d=estimate(s,add(p,mul(n,h)),iterations,'float64');
        ao-=Math.max(0,h-d)/Math.max(h,e)*.16;
      }}
      const light= .18*s.controls.ambientIntensity+.75*s.controls.lightIntensity*clamp(dot(n,key))+.58*head/(1+hit.travel*4)+.15*clamp(dot(n,rim));
      const material=clamp(.54+.24*n[1]+s.orbitTrap*.16*Math.cos(Math.log10(Math.max(hit.travel,e))*5));
      rgb=mul(paletteColor(s.palette,material),light*clamp(ao,.25,1));
    }
    return [...toneColor(rgb,s.exposure,s.controls),255] as [number,number,number,number];
  };
  return {pixel,iterations,clearance};
}
