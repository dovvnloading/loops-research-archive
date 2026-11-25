import { useEffect, useRef, useImperativeHandle, forwardRef } from 'react';
import { FractalEngine } from '../engine/FractalEngine';
import type { EngineHooks, EngineState } from '../types';

export interface ViewportHandle { capture:()=>string; zoom:(factor:number)=>void; fly:(key:string)=>void; }
export const FractalViewport=forwardRef<ViewportHandle,{state:EngineState;hooks:EngineHooks;className?:string}>(({state,hooks,className},ref)=>{
  const canvas=useRef<HTMLCanvasElement>(null);const engine=useRef<FractalEngine|null>(null);const latest=useRef(hooks);latest.current=hooks;
  useImperativeHandle(ref,()=>({capture:()=>engine.current?.capture()||'',zoom:factor=>engine.current?.zoom(factor),fly:key=>engine.current?.fly(key)}),[]);
  useEffect(()=>{
    if(!canvas.current)return;
    const e=new FractalEngine(canvas.current,state,{onChange:p=>latest.current.onChange?.(p),onStats:s=>latest.current.onStats?.(s),onSelectParameter:c=>latest.current.onSelectParameter?.(c),onError:s=>latest.current.onError?.(s)});engine.current=e;
    return()=>{e.destroy();engine.current=null;};
  },[]);
  useEffect(()=>{engine.current?.setState(state);},[state]);
  return <canvas ref={canvas} className={className||'fractal-canvas'} aria-label={`Interactive ${state.scene} fractal. Drag to navigate, scroll toward the cursor, use WASD and Q/E to fly in 3D.`} role="img"/>;
});
