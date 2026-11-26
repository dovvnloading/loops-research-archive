// GitHub CI smoke test: real Chrome, actual rendered pixels, real application UI.
// This script is for the CI runner. Managed Site previews are verified through CUA.
// CI sets SMOKE_SCREENSHOTS=1 for permanent visual evidence; failures always capture.
import assert from 'node:assert/strict';
import { spawn, spawnSync } from 'node:child_process';
import { mkdtemp, mkdir, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const output = process.env.SMOKE_OUTPUT ?? 'browser-smoke';
const screenshots = process.env.SMOKE_SCREENSHOTS === '1';
await mkdir(output, { recursive: true });
const browser = process.env.CHROME_BIN ?? ['google-chrome', 'chromium', 'chromium-browser'].find(name => spawnSync('which', [name], { stdio: 'ignore' }).status === 0);
assert.ok(browser, 'Chrome or Chromium is required');
const profile = await mkdtemp(join(tmpdir(), 'loops-chrome-'));
const server = spawn('npm', ['run', 'preview', '--', '--host', '127.0.0.1', '--port', '4173', '--strictPort'], { stdio: 'inherit', detached: true });
const chrome = spawn(browser, ['--headless=new', '--no-sandbox', '--disable-dev-shm-usage', '--use-gl=angle', '--use-angle=swiftshader', '--enable-unsafe-swiftshader', '--disable-background-timer-throttling', '--disable-renderer-backgrounding', '--disable-backgrounding-occluded-windows', '--remote-debugging-port=9222', '--user-data-dir=' + profile, '--window-size=1200,760', 'about:blank'], { stdio: ['ignore', 'ignore', 'pipe'] });
let chromeLog = '';
chrome.stderr.setEncoding('utf8');
chrome.stderr.on('data', chunk => { chromeLog = (chromeLog + chunk).slice(-64000); });
const pause = ms => new Promise(resolve => setTimeout(resolve, ms));
async function until(fn, label, ms = 90000) {
  const end = Date.now() + ms;
  let last;
  while (Date.now() < end) { try { const value = await fn(); if (value) return value; } catch (error) { last = error; } await pause(300); }
  throw Error('Timed out: ' + label + (last ? ' (' + last + ')' : ''));
}
let ws, id = 0, lastPixels = null;
const errors = [], browserMessages = [], pending = new Map(), results = {}, captures = [];
function cdp(method, params = {}) {
  return new Promise((resolve, reject) => {
    const request = ++id;
    const timer = setTimeout(() => { pending.delete(request); reject(Error('CDP timeout: ' + method)); }, 90000);
    pending.set(request, { resolve: value => { clearTimeout(timer); resolve(value); }, reject: error => { clearTimeout(timer); reject(error); } });
    ws.send(JSON.stringify({ id: request, method, params }));
  });
}
async function evaluate(expression) {
  const result = await cdp('Runtime.evaluate', { expression, returnByValue: true, awaitPromise: true });
  if (result.exceptionDetails) throw Error(result.exceptionDetails.exception?.description ?? result.exceptionDetails.text);
  return result.result.value;
}
async function snap(name, force = false) {
  if (!screenshots && !force) return;
  const result = await cdp('Page.captureScreenshot', { format: 'png', captureBeyondViewport: false });
  await writeFile(join(output, name + '.png'), Buffer.from(result.data, 'base64'));
  const page = await evaluate("({width:innerWidth,height:innerHeight,route:location.hash||'#explore',dialog:document.querySelector('dialog[open] h2')?.textContent??null})").catch(() => ({}));
  captures.push({ file: name + '.png', ...page });
  await writeFile(join(output, 'capture-index.json'), JSON.stringify(captures, null, 2));
}
async function uiSnap(name) {
  if (!screenshots) return;
  await evaluate("document.querySelector('button[aria-label=\"Dismiss notification\"]')?.click()");
  await evaluate(`(async()=>{
    await Promise.race([document.fonts.ready,new Promise(resolve=>setTimeout(resolve,2000))]);
    const visible=[...document.images].filter(image=>{const r=image.getBoundingClientRect();return r.bottom>0&&r.top<innerHeight&&r.right>0&&r.left<innerWidth;});
    await Promise.all(visible.map(image=>Promise.race([image.decode().catch(()=>{}),new Promise(resolve=>setTimeout(resolve,1500))])));
    await new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)));
  })()`);
  await cdp('Input.dispatchMouseEvent', { type: 'mouseMoved', x: 1, y: 1 });
  await snap(name);
}
const canvasSelector = '.ob-main-viewport > .ob-fractal-canvas';
const statusSelector = '.ob-statusbar';
const encoded = value => Buffer.from(JSON.stringify(value)).toString('base64url');
async function navigate(state, exact) {
  const query = exact ? 's=' + encoded({ v: 2, engine: state, exact }) : 'view=' + encoded({ v: 1, state });
  await cdp('Page.navigate', { url: 'http://127.0.0.1:4173/?' + query });
  await cdp('Page.bringToFront');
  await until(() => evaluate(`location.search===${JSON.stringify('?' + query)} && document.readyState==='complete' && !document.hidden && !!document.querySelector('.observatory')`), 'observatory application');
}
async function clickText(selector, text) {
  await evaluate(`(()=>{const element=[...document.querySelectorAll(${JSON.stringify(selector)})].find(e=>e.textContent.trim()===${JSON.stringify(text)});if(!element)throw Error('Missing control: '+${JSON.stringify(text)});element.click();})()`);
}
async function clickLabel(label) {
  await evaluate(`(()=>{const element=[...document.querySelectorAll('button[aria-label]')].find(e=>e.getAttribute('aria-label')===${JSON.stringify(label)});if(!element)throw Error('Missing button: '+${JSON.stringify(label)});element.click();})()`);
}
async function workspace(label, selector) {
  await evaluate(`(()=>{const button=[...document.querySelectorAll('.ob-header nav button')].find(e=>e.querySelector('span')?.textContent===${JSON.stringify(label)});if(!button)throw Error('Missing workspace');button.click();})()`);
  await until(() => evaluate(`!!document.querySelector(${JSON.stringify(selector)})`), label + ' workspace');
}
async function fill(selector, value) {
  await evaluate(`(()=>{const input=document.querySelector(${JSON.stringify(selector)});if(!input)throw Error('Missing form field');const prototype=input instanceof HTMLTextAreaElement?HTMLTextAreaElement.prototype:HTMLInputElement.prototype;Object.getOwnPropertyDescriptor(prototype,'value').set.call(input,${JSON.stringify(value)});input.dispatchEvent(new Event('input',{bubbles:true}));input.dispatchEvent(new Event('change',{bubbles:true}));})()`);
}
async function chooseField(scope, label, value) {
  await evaluate(`(()=>{const select=[...document.querySelectorAll(${JSON.stringify(scope + ' label')})].find(e=>e.querySelector('span')?.textContent===${JSON.stringify(label)})?.querySelector('select');if(!select)throw Error('Missing select: '+${JSON.stringify(label)});Object.getOwnPropertyDescriptor(HTMLSelectElement.prototype,'value').set.call(select,String(${JSON.stringify(value)}));select.dispatchEvent(new Event('change',{bubbles:true}));})()`);
}
async function inspectorTab(text) {
  if (!await evaluate("!!document.querySelector('.ob-inspector')")) await clickLabel('Show inspector');
  await until(() => evaluate("!!document.querySelector('.ob-inspector')"), 'visible inspector');
  await clickText('.ob-inspector [role=tab]', text);
  await until(() => evaluate(`document.querySelector('.ob-inspector [role=tab][aria-selected=true]')?.textContent.trim()===${JSON.stringify(text)}`), text + ' inspector tab');
}
async function setRange(label, value, scope = '.ob-inspector') {
  await evaluate(`(()=>{const field=[...document.querySelectorAll(${JSON.stringify(scope + ' .ob-range')})].find(e=>e.querySelector('label')?.textContent===${JSON.stringify(label)});const input=field?.querySelector('input[type=range]');if(!input)throw Error('Missing range: '+${JSON.stringify(label)});Object.getOwnPropertyDescriptor(HTMLInputElement.prototype,'value').set.call(input,String(${JSON.stringify(value)}));input.dispatchEvent(new Event('input',{bubbles:true}));input.dispatchEvent(new Event('change',{bubbles:true}));})()`);
  await until(() => evaluate(`Number([...document.querySelectorAll(${JSON.stringify(scope + ' .ob-range')})].find(e=>e.querySelector('label')?.textContent===${JSON.stringify(label)})?.querySelector('input')?.value)===${JSON.stringify(value)}`), label + ' committed');
}
async function setSelect(label, value) {
  await evaluate(`(()=>{const field=[...document.querySelectorAll('.ob-inspector label.ob-field')].find(e=>e.querySelector('span')?.textContent===${JSON.stringify(label)});const select=field?.querySelector('select');if(!select)throw Error('Missing select: '+${JSON.stringify(label)});Object.getOwnPropertyDescriptor(HTMLSelectElement.prototype,'value').set.call(select,${JSON.stringify(value)});select.dispatchEvent(new Event('change',{bubbles:true}));})()`);
  await until(() => evaluate(`[...document.querySelectorAll('.ob-inspector label.ob-field')].find(e=>e.querySelector('span')?.textContent===${JSON.stringify(label)})?.querySelector('select')?.value===${JSON.stringify(value)}`), label + ' committed');
}
async function sharedPayload() {
  await clickLabel('Export image or session');
  await until(() => evaluate("!!document.querySelector('.ob-export-dialog[open]')"), 'export dialog');
  await clickText('.ob-export-dialog .ob-segments button', 'Share link');
  const link = await until(() => evaluate("document.querySelector('.ob-export-dialog textarea')?.value"), 'version 2 share link');
  const snapshot = JSON.parse(Buffer.from(new URL(link).searchParams.get('s'), 'base64url').toString());
  assert.equal(snapshot.v, 2);
  await clickLabel('Close dialog');
  return snapshot;
}
async function pixels(selector, kind) {
  return evaluate(`(()=>{const canvas=document.querySelector(${JSON.stringify(selector)});if(!canvas||canvas.hidden||canvas.width<40||canvas.height<40)return null;let bytes;
    // The observation hook records the application's first context request.
    // Never claim an uninitialized canvas with test-default context attributes.
    if(${JSON.stringify(kind)}==='gpu'){
      if(canvas.dataset.smokeContext!=='webgl2')return null;
      const gl=canvas.getContext('webgl2');if(!gl||gl.isContextLost()||!gl.getContextAttributes()?.preserveDrawingBuffer)return null;
      bytes=new Uint8Array(canvas.width*canvas.height*4);gl.readPixels(0,0,canvas.width,canvas.height,gl.RGBA,gl.UNSIGNED_BYTE,bytes);if(gl.getError()!==gl.NO_ERROR)return null;
    }else{
      if(canvas.dataset.smokeContext!=='2d')return null;
      const context=canvas.getContext('2d');if(!context)return null;bytes=context.getImageData(0,0,canvas.width,canvas.height).data;
    }
    let min=255,max=0,sum=0,bright=0,hash=2166136261;for(let i=0;i<bytes.length;i+=4){const v=(bytes[i]+bytes[i+1]+bytes[i+2])/3;min=Math.min(min,v);max=Math.max(max,v);sum+=v;if(v>65)bright++;hash=Math.imul(hash^bytes[i],16777619);hash=Math.imul(hash^bytes[i+1],16777619);hash=Math.imul(hash^bytes[i+2],16777619);}
    return {width:canvas.width,height:canvas.height,range:max-min,mean:sum/(bytes.length/4),bright:bright/(bytes.length/4),hash:hash>>>0};})()`);
}
async function visibleImage(kind, prior, selector = kind === 'volume64' ? '.ob-main-viewport > .deep-volume-canvas' : canvasSelector) {
  let signature = '', stableSince = 0;
  return until(async () => {
    const sample = await pixels(selector, kind); lastPixels = { kind, prior, selector, sample };
    if (!sample || sample.range <= 25 || sample.bright <= .005 || sample.hash === prior) return null;
    if (kind === 'gpu') {
      const next = `${sample.width}:${sample.height}:${sample.hash}`;
      if (next !== signature) { signature = next; stableSince = Date.now(); return null; }
      if (Date.now() - stableSince < 850) return null;
    }
    return sample;
  }, kind + ' nonuniform rendered pixels');
}
async function settledPlane() {
  await until(() => evaluate("!!document.querySelector('.ob-main-viewport>.ob-fractal-canvas') && !document.querySelector('.ob-refinement') && /Float64 worker|Perturbation/.test(document.querySelector('.ob-statusbar')?.innerText??'')"), 'completed precision frame');
}
async function settledVolume64() {
  await until(() => evaluate("(()=>{const canvas=document.querySelector('.ob-main-viewport>.deep-volume-canvas');return canvas&&!canvas.hidden&&Math.max(canvas.width,canvas.height)>=256&&document.querySelector('.ob-statusbar')?.innerText.includes('CPU worker · Float64');})()"), 'Float64 volume full pass', 180000);
}
async function chooseWorld(title) {
  if (!await evaluate("!!document.querySelector('.ob-world-library')")) await clickLabel('Show index');
  await evaluate(`(()=>{const title=[...document.querySelectorAll('.ob-world-list strong')].find(e=>e.textContent===${JSON.stringify(title)});if(!title)throw Error('Missing world');title.closest('button').click();})()`);
  await until(() => evaluate(`document.querySelector('.ob-context-active')?.textContent===${JSON.stringify(title)}`), title + ' selected');
  await inspectorTab('View'); await setSelect('Rendering quality', 'low');
}

const observationTitle = 'Imaginary gateway field note';
async function saveVisualObservation() {
  await evaluate("document.querySelector('.ob-header .ob-save-button').click()");
  await until(() => evaluate("!!document.querySelector('.ob-save-dialog[open]')"), 'save observation dialog');
  await fill('.ob-save-dialog input[name="title"]', observationTitle);
  await fill('.ob-save-dialog textarea', 'Nearby escape contours remain distinct at extremely small scales. Compare this window with the exact c = i reference.');
  await fill('.ob-save-dialog input[name="tags"]', 'deep zoom, field note');
  await clickText('.ob-save-dialog button[type=submit]', 'Save to journal');
  await until(() => evaluate("!document.querySelector('.ob-save-dialog') && Number([...document.querySelectorAll('.ob-header nav button')].find(e=>e.querySelector('span')?.textContent==='Journal')?.querySelector('i')?.textContent)>=1"), 'observation saved through the UI');
}
async function captureDialogs(prefix, compose = false) {
  await clickLabel('Export image or session');
  await until(() => evaluate("!!document.querySelector('.ob-export-dialog[open] select')"), 'PNG export options visible');
  await uiSnap(prefix + '-export');
  await clickLabel('Close dialog');
  await inspectorTab('View');
  await clickText('.ob-inspector button', 'Open motion studio');
  await until(() => evaluate("!!document.querySelector('.ob-motion[open] .ob-motion-view canvas')"), 'motion studio visible');
  await visibleImage('precision', undefined, '.ob-motion-view canvas');
  if (compose) {
    await setRange('Yaw', 35, '.ob-motion');
    await visibleImage('gpu');
    await clickText('.ob-motion-frames-heading button', 'Capture current view');
    await until(() => evaluate("document.querySelectorAll('.ob-motion-frames article').length>=2 && document.querySelectorAll('.ob-motion-frame-preview img').length>=2"), 'two captured motion keyframes');
  }
  await uiSnap(prefix + '-motion');
  await clickLabel('Close dialog');
}
async function captureWorkspaces(prefix, populate) {
  await workspace('Atlas', '.ob-atlas');
  await until(() => evaluate("document.querySelectorAll('.ob-destination-card').length>=6"), 'atlas destinations');
  await uiSnap(prefix + '-atlas');
  await evaluate("document.querySelector('.ob-destination-grid').scrollIntoView({block:'start'})");
  await uiSnap(prefix + '-atlas-places');
  await workspace('Laboratory', '.laboratory-workspace');
  if (populate) {
    await chooseField('#lab-panel-discovery', 'Sampling grid', 48);
    await chooseField('#lab-panel-discovery', 'Iteration budget', 512);
    await chooseField('#lab-panel-discovery', 'Maximum period', 8);
    await clickText('#lab-panel-discovery .lab-settings button', 'Start expedition');
    await until(() => evaluate("document.querySelector('[aria-label=\"Expedition progress\"]')?.getAttribute('aria-valuenow')==='100' && [...document.querySelectorAll('#lab-panel-discovery button')].some(e=>e.textContent.trim()==='Run expedition again')"), 'short expedition completed', 30000);
    results.visualExpedition = await evaluate("({progress:document.querySelector('[aria-label=\"Expedition progress\"]').getAttribute('aria-valuenow'),candidateRows:document.querySelectorAll('#lab-panel-discovery tbody tr').length})");
    await uiSnap(prefix + '-laboratory-expedition');
    await clickText('#lab-panel-discovery .lab-findings-footer button', 'Save experiment');
    await until(() => evaluate("[...document.querySelectorAll('#lab-panel-discovery .lab-findings-footer button')].some(e=>e.textContent.trim()==='Saved to journal')"), 'completed expedition saved');
  }
  await clickText('.lab-tabs button', 'Orbit microscope');
  await clickText('#lab-panel-orbit .lab-orbit-presets button', 'Airplane');
  await until(() => evaluate("document.querySelector('#lab-panel-orbit .lab-orbit-conclusion h3')?.textContent.includes('Period 3')"), 'Airplane orbit analysis complete');
  await uiSnap(prefix + '-laboratory-orbit');
  if (!populate) {
    await evaluate("document.querySelector('#lab-panel-orbit .lab-orbit-main').scrollIntoView({block:'start'})");
    await uiSnap(prefix + '-laboratory-orbit-chart');
  }
  await workspace('Journal', '.journal-workspace');
  await until(() => evaluate(`!![...document.querySelectorAll('.journal-card h2')].find(e=>e.textContent===${JSON.stringify(observationTitle)})`), 'populated journal');
  if (populate) {
    const previousDocument = await evaluate('performance.timeOrigin');
    await cdp('Page.reload', { ignoreCache: false });
    await until(() => evaluate(`performance.timeOrigin!==${JSON.stringify(previousDocument)} && document.readyState==='complete' && location.hash==='#journal' && document.querySelectorAll('.journal-card').length>=2 && [...document.querySelectorAll('.journal-card h2')].some(e=>e.textContent===${JSON.stringify(observationTitle)})`), 'journal observations retained after reload');
    results.journalPersisted = true;
  }
  await uiSnap(prefix + '-journal');
  if (populate) {
    await clickLabel('View ' + observationTitle);
    await until(() => evaluate("!!document.querySelector('.journal-detail')"), 'saved observation details');
    await uiSnap(prefix + '-journal-detail');
    await clickLabel('Close observation details');
  }
  await workspace('Research', '.ob-research');
  await until(() => evaluate("!!document.querySelector('.ro-source-bar a code') && !document.querySelector('.ro-load-error')"), 'research inventory loaded');
  await uiSnap(prefix + '-research');
}

try {
  await until(async () => (await fetch('http://127.0.0.1:4173/')).ok, 'Vite preview', 30000);
  const target = await until(async () => (await (await fetch('http://127.0.0.1:9222/json/list')).json()).find(tab => tab.type === 'page'), 'Chrome debugger', 30000);
  ws = new WebSocket(target.webSocketDebuggerUrl);
  await new Promise((resolve, reject) => { ws.addEventListener('open', resolve, { once: true }); ws.addEventListener('error', reject, { once: true }); });
  ws.onmessage = event => {
    const message = JSON.parse(event.data);
    if (message.id && pending.has(message.id)) { const request = pending.get(message.id); pending.delete(message.id); message.error ? request.reject(Error(message.error.message)) : request.resolve(message.result); }
    if (message.method === 'Runtime.exceptionThrown') errors.push(message.params.exceptionDetails.exception?.description ?? message.params.exceptionDetails.text);
    if (message.method === 'Log.entryAdded') { const { level, source, text } = message.params.entry; browserMessages.push({ level, source, text }); if (browserMessages.length > 100) browserMessages.shift(); }
  };
  await cdp('Runtime.enable'); await cdp('Page.enable'); await cdp('Log.enable');
  await cdp('Emulation.setDeviceMetricsOverride', { width: 1200, height: 760, deviceScaleFactor: 1, mobile: false });
  await cdp('Page.addScriptToEvaluateOnNewDocument', { source: `(()=>{const original=HTMLCanvasElement.prototype.getContext;HTMLCanvasElement.prototype.getContext=function(kind,...args){const context=original.call(this,kind,...args);if(context)this.dataset.smokeContext=String(kind);return context;};})()` });

  await navigate({ scene: 'mandelbulb', volumePrecision: 'gpu', quality: 'low', detail: .6, autoRotate: false });
  await until(() => evaluate("document.querySelector('.ob-statusbar')?.innerText.includes('WebGL2')"), 'application WebGL2 initialization');
  results.mandelbulb = await visibleImage('gpu');
  const context = await evaluate(`document.querySelector(${JSON.stringify(canvasSelector)}).getContext('webgl2')?.getContextAttributes()`);
  assert.equal(context?.preserveDrawingBuffer, true);
  console.log('Mandelbulb actual GPU pixels:', results.mandelbulb);
  await snap('01-mandelbulb');

  await inspectorTab('Material'); await setRange('Gamma', 3.1);
  results.gamma = await visibleImage('gpu', results.mandelbulb.hash);
  await inspectorTab('View'); await setRange('Field of view', 70);
  results.fov = await visibleImage('gpu', results.gamma.hash);
  const snapshot = await sharedPayload();
  assert.equal(snapshot.engine.controls.gamma, 3.1); assert.equal(snapshot.engine.controls.fov, 70);

  await evaluate(`(()=>{const canvas=document.querySelector(${JSON.stringify(canvasSelector)}),r=canvas.getBoundingClientRect();canvas.dispatchEvent(new WheelEvent('wheel',{deltaY:-160,clientX:r.left+r.width*.55,clientY:r.top+r.height*.48,cancelable:true}));})()`);
  results.flight = await visibleImage('gpu', results.fov.hash);
  assert.ok(Array.isArray((await sharedPayload()).engine.camera.position), 'Real wheel input enters free flight.');
  if (screenshots) await captureDialogs('desktop', true);
  let previousImage = results.flight;
  for (const [title, key] of [['Folded space', 'mandelbox'], ['Fourth dimension', 'quaternion'], ['Contours of escape', 'landscape']]) {
    await chooseWorld(title);
    results[key] = await visibleImage('gpu', previousImage.hash);
    previousImage = results[key];
    assert.equal(await evaluate("!!document.querySelector('.ob-render-error')"), false);
    console.log(title + ' actual GPU pixels:', results[key]);
  }

  await chooseWorld('The whole map'); await settledPlane();
  results.mandelbrot = await visibleImage('precision');
  const bounds = await evaluate(`(()=>{const r=document.querySelector(${JSON.stringify(canvasSelector)}).getBoundingClientRect();return {x:r.left+r.width*.62,y:r.top+r.height*.43};})()`);
  for (const type of ['mousePressed', 'mouseReleased']) await cdp('Input.dispatchMouseEvent', { type, ...bounds, button: 'left', clickCount: 1 });
  assert.equal(await evaluate("!!document.querySelector('.ob-linked-viewport')"), false, 'Ordinary clicks do not unexpectedly split the canvas.');
  for (const type of ['mousePressed', 'mouseReleased']) await cdp('Input.dispatchMouseEvent', { type, ...bounds, button: 'left', clickCount: 1, modifiers: 8 });
  await until(() => evaluate("!!document.querySelector('.ob-linked-viewport')"), 'Shift-click linked Julia view');
  results.linkedJulia = await visibleImage('precision', undefined, '.ob-linked-viewport > .ob-fractal-canvas');
  await clickLabel('Close linked view');

  const deep = { family: 'mandelbrot', center: { re: '0', im: '1' }, span: '1e-60', julia: { re: '0', im: '1' }, iterations: 1024, palette: 'aurora' };
  await navigate({ scene: 'mandelbrot', center: [0, 1], scale: 1e-7, quality: 'low', iterations: 1024, autoRotate: false }, deep);
  assert.equal(await evaluate("document.querySelector('.ob-context-active')?.textContent"), 'Mandelbrot set', 'A custom shared view must use its own family title.');
  await settledPlane(); results.deep = await visibleImage('precision');
  assert.ok(await evaluate("document.querySelector('.ob-statusbar').innerText.includes('Perturbation')"));
  await snap('02-deep-precision');
  await evaluate(`(()=>{const canvas=document.querySelector(${JSON.stringify(canvasSelector)}),r=canvas.getBoundingClientRect();canvas.dispatchEvent(new WheelEvent('wheel',{deltaY:-160,clientX:r.left+r.width*.6,clientY:r.top+r.height*.35,cancelable:true}));})()`);
  await until(() => evaluate("Number(document.querySelector('.ob-statusbar code')?.textContent)<1e-60"), 'deep wheel state committed');
  await settledPlane();
  const moved = await sharedPayload();
  await settledPlane();
  assert.ok(Number(moved.exact.span) < 1e-60, 'Exact navigation passes the old numerical zoom floor.');
  assert.notEqual(moved.exact.center.im, '1');
  assert.equal(Number(moved.exact.center.im), 1, 'The serialized coordinate retains information below binary64 resolution.');
  results.deepNavigated = await visibleImage('precision', results.deep.hash);
  await clickLabel('Reset view (R)');
  await settledPlane();
  const resetSnapshot = await sharedPayload();
  assert.deepEqual(resetSnapshot.exact.center, deep.center, 'Reset returns to the shared starting coordinates.');
  assert.equal(resetSnapshot.exact.span, deep.span, 'Reset preserves the shared starting scale.');

  // Keep visual evidence in the same real user flow and ephemeral CI browser profile.
  if (screenshots) {
    await saveVisualObservation();
    await captureWorkspaces('desktop', true);
  } else {
    for (const [label, selector] of [['Atlas', '.ob-atlas'], ['Laboratory', '.laboratory-workspace'], ['Journal', '.journal-workspace'], ['Research', '.ob-research']]) await workspace(label, selector);
  }

  await cdp('Emulation.setDeviceMetricsOverride', { width: 390, height: 844, deviceScaleFactor: 1, mobile: true });
  await navigate({ scene: 'mandelbulb', volumePrecision: 'gpu', quality: 'low', detail: .5, autoRotate: false });
  results.portraitGpu = await visibleImage('gpu');
  assert.ok(results.portraitGpu.height > results.portraitGpu.width, 'Portrait projection produces a portrait framebuffer.');
  if (screenshots) await captureDialogs('mobile');
  await inspectorTab('View'); await setSelect('Volume precision', 'float64');
  await settledVolume64(); results.float64 = await visibleImage('volume64');
  if (screenshots) await clickLabel('Hide inspector');
  await snap('03-float64-portrait');
  if (screenshots) await captureWorkspaces('mobile', false);

  // Fault injection is installed only in the CI page, before application startup.
  const blockedGpu = await cdp('Page.addScriptToEvaluateOnNewDocument', { source: `(()=>{const original=HTMLCanvasElement.prototype.getContext;HTMLCanvasElement.prototype.getContext=function(kind,...args){return kind==='webgl2'?null:original.call(this,kind,...args);};})()` });
  await navigate({ scene: 'mandelbulb', volumePrecision: 'gpu', quality: 'low', detail: .45, autoRotate: false });
  await settledVolume64(); results.noGpuFallback = await visibleImage('volume64');
  assert.equal((await sharedPayload()).engine.scene, 'mandelbulb', 'Losing WebGL must preserve the requested 3D family.');
  await cdp('Page.removeScriptToEvaluateOnNewDocument', { identifier: blockedGpu.identifier });

  const blockedWorker = await cdp('Page.addScriptToEvaluateOnNewDocument', { source: `window.Worker=class {constructor(){throw new Error('Worker unavailable in deliberate CI fault injection');}};` });
  await navigate({ scene: 'mandelbrot', quality: 'low' }, { ...deep, center: { re: '-0.5', im: '0' }, span: '3.2' });
  await until(() => evaluate("document.querySelector('.ob-render-error')?.textContent.includes('worker') || document.querySelector('.ob-render-error')?.textContent.includes('Worker')"), 'visible worker startup error');
  assert.ok(await evaluate("!!document.querySelector('.ob-header nav')"), 'A worker failure must not crash the application shell.');
  await cdp('Page.removeScriptToEvaluateOnNewDocument', { identifier: blockedWorker.identifier });

  assert.deepEqual(errors, []);
  await writeFile(join(output, 'results.json'), JSON.stringify({ results, captures, checks: ['GPU fractal pixels', 'Gamma and projection controls', 'Version 2 snapshot fidelity', 'Wheel flight', 'Mandelbox, quaternion, and landscape shaders', 'Float64 Mandelbrot canvas', 'Intentional linked Julia selection', '60-digit exact navigation', 'Workspace lifecycle', 'Portrait projection', 'Float64 refinement', 'Missing GPU fallback', 'Worker startup error recovery', ...(screenshots ? ['Desktop and mobile workspace screenshots', 'Completed short laboratory expedition', 'Journal persistence after reload', 'PNG export and populated motion dialogs'] : [])], errors }, null, 2));
  console.log('PASS: actual GPU, precision, and Float64 images; exact snapshots; linked dynamics; fallbacks; no uncaught exceptions.');
} catch (error) {
  const diagnostic = { error: String(error), lastPixels, results, errors, browserMessages, chromeLog };
  if (ws?.readyState === WebSocket.OPEN) {
    try { diagnostic.page = await evaluate(`(()=>{const canvas=document.querySelector(${JSON.stringify(canvasSelector)}),r=canvas?.getBoundingClientRect();return {url:location.href,visibility:document.visibilityState,ready:document.readyState,renderer:document.querySelector(${JSON.stringify(statusSelector)})?.innerText,renderError:document.querySelector('.ob-render-error')?.innerText,refinement:document.querySelector('.ob-refinement')?.innerText,canvas:canvas?{width:canvas.width,height:canvas.height,context:canvas.dataset.smokeContext,cssWidth:r.width,cssHeight:r.height}:null};})()`); } catch (cause) { diagnostic.pageError = String(cause); }
    try { await snap('failure', true); } catch (cause) { diagnostic.screenshotError = String(cause); }
  }
  await writeFile(join(output, 'failure.json'), JSON.stringify(diagnostic, null, 2));
  console.error('Browser rendering failure:', JSON.stringify(diagnostic, null, 2));
  throw error;
} finally {
  ws?.close(); chrome.kill('SIGTERM');
  try { process.kill(-server.pid, 'SIGTERM'); } catch { server.kill('SIGTERM'); }
  await pause(300); await rm(profile, { recursive: true, force: true, maxRetries: 3, retryDelay: 200 }).catch(() => {});
}
