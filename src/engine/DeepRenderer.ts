import type {EngineState} from '../types';
import type {VolumeFrame} from './volume64';
/** A cancellable binary64 worker pipeline. Preview stays visible until the next
 * image completes; fine tiles are staged offscreen to prevent a blank flash. */
export class DeepRenderer {
  private worker:Worker|null=null;
  private generation=0;
  private complete=false;
  private stage=document.createElement('canvas');
  private disposed=false;
  constructor(private canvas:HTMLCanvasElement,private onUpdate:(status:string)=>void,private onError:(message:string)=>void){}
  get ready(){return this.complete;}
  get size(){return this.canvas.width+' × '+this.canvas.height;}
  hide(){this.cancel();this.canvas.hidden=true;this.complete=false;}
  cancel(){this.generation++;this.worker?.terminate();this.worker=null;}
  destroy(){this.disposed=true;this.hide();}
  capture(){return this.complete?this.canvas.toDataURL('image/png'):'';}
  render(state:EngineState,aspect:number,preview:boolean){
    if(this.disposed)return;
    this.cancel();const generation=this.generation;this.complete=false;
    const max=preview?120:state.quality==='high'?640:state.quality==='low'?256:448;
    const width=Math.max(1,Math.round(max*Math.min(1,aspect))),height=Math.max(1,Math.round(max/Math.max(1,aspect)));
    this.stage.width=width;this.stage.height=height;
    const ctx=this.stage.getContext('2d');if(!ctx){this.onError('Float64 canvas unavailable');return;}
    const display=preview?this.canvas.getContext('2d'):null;
    if(preview){this.canvas.width=width;this.canvas.height=height;if(display){display.fillStyle='#10181a';display.fillRect(0,0,width,height);}this.canvas.hidden=false;}
    const frame:VolumeFrame={state,width,height,preview};
    let worker:Worker;
    try{worker=new Worker(new URL('../workers/volume64.worker.ts',import.meta.url),{type:'module'});}
    catch(error){this.onError(String(error));return;}
    this.worker=worker;this.onUpdate(preview?'Float64 preview':'Float64 refining');
    worker.onmessage=event=>{
      if(this.disposed||generation!==this.generation)return;
      const m=event.data;
      if(m.type==='strip'){
        const image=new ImageData(new Uint8ClampedArray(m.buffer),m.width,m.rows);
        ctx.putImageData(image,0,m.y);display?.putImageData(image,0,m.y);
        this.onUpdate((preview?'Preview ':'Refining ')+Math.round(100*m.completedRows/height)+'%');
      }else if(m.type==='complete'){
        this.canvas.width=width;this.canvas.height=height;
        this.canvas.getContext('2d')?.drawImage(this.stage,0,0);
        this.canvas.hidden=false;this.complete=true;
        this.onUpdate(preview?'Float64 preview ready':'Float64 settled');
        worker.terminate();if(this.worker===worker)this.worker=null;
      }else if(m.type==='error'){worker.terminate();this.onError(m.message);}
    };
    worker.onerror=event=>{if(generation===this.generation)this.onError(event.message||'Float64 worker failed');worker.terminate();};
    worker.postMessage(frame);
  }
}
