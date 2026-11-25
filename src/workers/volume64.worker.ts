import {prepareVolume} from '../engine/volume64';
import type {VolumeFrame} from '../engine/volume64';
const scope=self as unknown as DedicatedWorkerGlobalScope;
scope.onmessage=(event:MessageEvent<VolumeFrame>)=>{
  try{
    const frame=event.data,{pixel,iterations,clearance}=prepareVolume(frame);
    for(let y=0;y<frame.height;y+=4){
      const rows=Math.min(4,frame.height-y),data=new Uint8ClampedArray(frame.width*rows*4);
      for(let dy=0;dy<rows;dy++)for(let x=0;x<frame.width;x++)data.set(pixel(x,y+dy),(dy*frame.width+x)*4);
      scope.postMessage({type:'strip',y,rows,width:frame.width,height:frame.height,buffer:data.buffer},[data.buffer]);
    }
    scope.postMessage({type:'complete',iterations,clearance});
  }catch(error){scope.postMessage({type:'error',message:String(error)});}
};
