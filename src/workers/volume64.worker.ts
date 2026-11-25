import {prepareVolume} from '../engine/volume64';
import type {VolumeFrame} from '../engine/volume64';
const scope=self as unknown as DedicatedWorkerGlobalScope;
scope.onmessage=(event:MessageEvent<VolumeFrame>)=>{
  try{
    const frame=event.data,{pixel,iterations,clearance}=prepareVolume(frame);
    const offsets=Array.from({length:Math.ceil(frame.height/4)},(_,i)=>i*4).sort((a,b)=>Math.abs(a+2-frame.height/2)-Math.abs(b+2-frame.height/2));
    let completedRows=0;
    for(const y of offsets){
      const rows=Math.min(4,frame.height-y),data=new Uint8ClampedArray(frame.width*rows*4);
      for(let dy=0;dy<rows;dy++)for(let x=0;x<frame.width;x++)data.set(pixel(x,y+dy),(dy*frame.width+x)*4);
      completedRows+=rows;
      scope.postMessage({type:'strip',y,rows,completedRows,width:frame.width,height:frame.height,buffer:data.buffer},[data.buffer]);
    }
    scope.postMessage({type:'complete',iterations,clearance});
  }catch(error){scope.postMessage({type:'error',message:String(error)});}
};
