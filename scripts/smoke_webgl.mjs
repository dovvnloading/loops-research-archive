// Real browser, actual WebGL2 draw and pixel readback, no DOM-only mocks.
// Uses the runner's Chrome/Chromium and the Node 24 built-in CDP WebSocket.
import assert from 'node:assert/strict';
import {spawn,spawnSync} from 'node:child_process';
import {mkdtemp,mkdir,rm,writeFile} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
const output=process.env.SMOKE_OUTPUT??'browser-smoke';
await mkdir(output,{recursive:true});
const browser=process.env.CHROME_BIN??['google-chrome','chromium','chromium-browser'].find(x=>spawnSync('which',[x],{stdio:'ignore'}).status===0);
assert.ok(browser,'Chrome or Chromium is required');
const dir=await mkdtemp(join(tmpdir(),'loops-chrome-'));
const server=spawn('npm',['run','preview','--','--host','127.0.0.1','--port','4173','--strictPort'],{stdio:'inherit',detached:true});
const chrome=spawn(browser,['--headless=new','--no-sandbox','--disable-dev-shm-usage','--use-gl=angle','--use-angle=swiftshader','--enable-unsafe-swiftshader','--remote-debugging-port=9222','--user-data-dir='+dir,'--window-size=1200,760','about:blank'],{stdio:'ignore'});
const pause=ms=>new Promise(r=>setTimeout(r,ms));
async function until(fn,label,ms=90000){const end=Date.now()+ms;let last;while(Date.now()<end){try{const x=await fn();if(x)return x;}catch(e){last=e;}await pause(350);}throw Error('Timed out: '+label+(last?' ('+last+')':''));}
let ws;const errors=[];const pending=new Map();let id=0;
function cdp(method,params={}){return new Promise((resolve,reject)=>{const i=++id;const timeout=setTimeout(()=>{pending.delete(i);reject(Error('CDP timeout: '+method));},90000);pending.set(i,{resolve:v=>{clearTimeout(timeout);resolve(v);},reject:e=>{clearTimeout(timeout);reject(e);}});ws.send(JSON.stringify({id:i,method,params}));});}
async function evaluate(expression){const r=await cdp('Runtime.evaluate',{expression,returnByValue:true,awaitPromise:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.exception?.description??r.exceptionDetails.text);return r.result.value;}
async function snap(name){const r=await cdp('Page.captureScreenshot',{format:'png',captureBeyondViewport:false});await writeFile(join(output,name+'.png'),Buffer.from(r.data,'base64'));}
const pixels=(selector,kind)=>evaluate(`(()=>{const c=document.querySelector(${JSON.stringify(selector)});if(!c||c.hidden||c.width<40||c.height<40)return null;let p;
if(${JSON.stringify(kind)}==='gpu'){const gl=c.getContext('webgl2');if(!gl)return null;p=new Uint8Array(c.width*c.height*4);gl.readPixels(0,0,c.width,c.height,gl.RGBA,gl.UNSIGNED_BYTE,p);if(gl.getError()!==gl.NO_ERROR)return null;}
else{p=c.getContext('2d').getImageData(0,0,c.width,c.height).data;}
let min=255,max=0,sum=0,bright=0,hash=2166136261;for(let i=0;i<p.length;i+=4){const v=(p[i]+p[i+1]+p[i+2])/3;min=Math.min(min,v);max=Math.max(max,v);sum+=v;if(v>65)bright++;hash=Math.imul(hash^p[i],16777619);hash=Math.imul(hash^p[i+1],16777619);hash=Math.imul(hash^p[i+2],16777619);}
return {width:c.width,height:c.height,range:max-min,mean:sum/(p.length/4),bright:bright/(p.length/4),hash:hash>>>0};})()`);
const visibleImage=async(kind,prior)=>until(async()=>{const p=await pixels(kind==='gpu'?'.fractal-canvas':'.deep-volume-canvas',kind);return p&&p.range>25&&p.bright>.005&&p.hash!==prior?p:null;},kind+' actual nonuniform rendered pixels');
try{
  await until(async()=>{const r=await fetch('http://127.0.0.1:4173/');return r.ok;},'Vite preview',30000);
  const target=await until(async()=>{const r=await fetch('http://127.0.0.1:9222/json/list');return (await r.json()).find(x=>x.type==='page');},'Chrome debugger',30000);
  ws=new WebSocket(target.webSocketDebuggerUrl);
  await new Promise((resolve,reject)=>{ws.addEventListener('open',resolve,{once:true});ws.addEventListener('error',reject,{once:true});});
  ws.onmessage=e=>{const m=JSON.parse(e.data);if(m.id&&pending.has(m.id)){const p=pending.get(m.id);pending.delete(m.id);m.error?p.reject(Error(m.error.message)):p.resolve(m.result);}
  if(m.method==='Runtime.exceptionThrown')errors.push(m.params.exceptionDetails.exception?.description??m.params.exceptionDetails.text);};
  await cdp('Runtime.enable');await cdp('Page.enable');
  await cdp('Emulation.setDeviceMetricsOverride',{width:1200,height:760,deviceScaleFactor:1,mobile:false});
  const view=Buffer.from(JSON.stringify({v:1,state:{scene:'mandelbulb',volumePrecision:'gpu',quality:'low',detail:.65}})).toString('base64url');
  await cdp('Page.navigate',{url:'http://127.0.0.1:4173/?view='+view});
  await until(()=>evaluate("document.querySelector('.fractal-canvas')?.getContext('webgl2')!==null && !!document.querySelector('.fractal-canvas')"),'WebGL2 canvas');
  let image=await visibleImage('gpu');
  console.log('Mandelbulb GPU:',image);await snap('01-mandelbulb');
  const old=image.hash;
  await evaluate(`(()=>{const c=document.querySelector('.fractal-canvas'),r=c.getBoundingClientRect();c.dispatchEvent(new WheelEvent('wheel',{deltaY:-160,clientX:r.left+r.width*.55,clientY:r.top+r.height*.48,cancelable:true}));})()`);
  await until(()=>evaluate("document.querySelector('.flight-panel')?.innerText.includes('FLIGHT')"),'camera enters flight');
  image=await visibleImage('gpu',old);console.log('After real wheel flight:',image);await snap('02-flight');
  for(const [label,name] of [['Mandelbox','03-mandelbox'],['Quaternion Julia','04-quaternion']]){
    const prior=image.hash;
    await evaluate(`[...document.querySelectorAll('.scene-item')].find(b=>b.querySelector('strong')?.textContent===${JSON.stringify(label)}).click()`);
    // Avoid comparing the previous image during the deferred React update.
    await pause(900);image=await visibleImage('gpu',prior);
    assert.equal(await evaluate("!!document.querySelector('.engine-error')"),false);
    console.log(label,image);await snap(name);
  }
  await evaluate("[...document.querySelectorAll('.scene-item')].find(b=>b.querySelector('strong')?.textContent==='Mandelbulb').click()");
  await until(()=>evaluate("document.querySelector('.precision-choice select')?.value==='auto'"),'Mandelbulb reset');
  await evaluate("(()=>{const s=document.querySelector('.precision-choice select');s.value='float64';s.dispatchEvent(new Event('change',{bubbles:true}));})()");
  await until(()=>evaluate("document.querySelector('.flight-panel')?.innerText.includes('Float64 settled')"),'binary64 worker full pass',180000);
  const cpu=await visibleImage('cpu');console.log('Float64 actual worker pixels:',cpu);await snap('05-float64');
  assert.equal(await evaluate("!!document.querySelector('.engine-error')"),false);
  assert.deepEqual(errors,[]);
  await writeFile(join(output,'results.json'),JSON.stringify({gpu:image,cpu,errors},null,2));
  console.log('PASS: WebGL2 shaders, volume pixels, camera input, Float64 worker, and no runtime exceptions.');
}finally{
  ws?.close();chrome.kill('SIGTERM');try{process.kill(-server.pid,'SIGTERM');}catch{server.kill('SIGTERM');}
  await pause(300);await rm(dir,{recursive:true,force:true,maxRetries:3,retryDelay:200}).catch(()=>{});
}
