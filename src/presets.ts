import type { EngineState, ScenePreset } from './types';

export const DEFAULT_STATE: EngineState = {
  scene: 'mandelbulb', power: 8, iterations: 12, bailout: 8, detail: .65,
  exposure: 1.1, palette: 'glacier', camera: { yaw: .35, pitch: .18, distance: 3.6 },
  center: [-.5, 0], scale: 3.2, julia: [-.74543, .11301], slice: 0,
  autoRotate: false, showGrid: true, quality: 'auto', orbitTrap: .35,
};

export const PRESETS: ScenePreset[] = [
  { id: 'mandelbulb', name: 'Mandelbulb', subtitle: 'Spherical power fractal', kind: '3D FRACTAL', state: {scene:'mandelbulb',power:8,iterations:12,camera:{yaw:.35,pitch:.18,distance:3.6}}, description: 'An intricate world built from a single repeated operation. Explore the eightfold symmetry of a three-dimensional power map.', formula: 'zₙ₊₁ = zₙ⁸ + c' },
  { id: 'mandelbox', name: 'Mandelbox', subtitle: 'Infinite folded architecture', kind: '3D FRACTAL', state: {scene:'mandelbox',power:2,iterations:14,camera:{yaw:.65,pitch:.35,distance:5.3}}, description: 'A lattice of nested rooms and impossible corridors, formed by alternating box and sphere folds.', formula: 'zₙ₊₁ = s · sphereFold(boxFold(zₙ)) + c' },
  { id: 'quaternion', name: 'Quaternion Julia', subtitle: 'A slice through four dimensions', kind: '3D FRACTAL', state: {scene:'quaternion',iterations:14,julia:[-.3,.52],slice:0,camera:{yaw:.7,pitch:.22,distance:3.8}}, description: 'Move a three-dimensional slice through a four-dimensional Julia set. A different cross-section reveals a different world.', formula: 'qₙ₊₁ = qₙ² + c,  q ∈ ℍ' },
  { id: 'mandelbrot', name: 'Mandelbrot plane', subtitle: 'The map of quadratic dynamics', kind: 'COMPLEX DYNAMICS', state: {scene:'mandelbrot',iterations:384,center:[-.5,0],scale:3.2}, description: 'Every point is a parameter. Shift-click a location to select c, then compare its Julia set alongside the parameter plane.', formula: 'z₀ = 0,  zₙ₊₁ = zₙ² + c' },
  { id: 'julia', name: 'Julia set', subtitle: 'One parameter. Endless structure.', kind: 'COMPLEX DYNAMICS', state: {scene:'julia',iterations:384,julia:[-.74543,.11301],center:[0,0],scale:3.2}, description: 'Fix the parameter and explore the fate of every starting point. Change c to watch the boundary reorganize.', formula: 'zₙ₊₁ = zₙ² + c' },
  { id: 'landscape', name: 'Escape landscape', subtitle: 'Complex dynamics in relief', kind: 'COMPLEX DYNAMICS', state: {scene:'landscape',iterations:160,center:[-.5,0],scale:3.2,camera:{yaw:.25,pitch:.75,distance:4.6}}, description: 'Escape time lifted into a sculptural height field. A numerical landscape of the complex parameter plane.', formula: 'h(c) = log-scaled escape time' },
];

export const CURATED: ScenePreset[] = [
  {...PRESETS[0],id:'eightfold',name:'Eightfold',subtitle:'The original bulb',state:{...PRESETS[0].state,palette:'glacier'}},
  {...PRESETS[0],id:'coral',name:'Coral bloom',subtitle:'Power 5 · Ember',state:{...PRESETS[0].state,power:5,palette:'ember',camera:{yaw:1.2,pitch:.5,distance:3.1}}},
  {...PRESETS[0],id:'cathedral',name:'Cathedral',subtitle:'Power 12 · Silver',state:{...PRESETS[0].state,power:12,palette:'mono',camera:{yaw:1.6,pitch:.28,distance:3.5}}},
  {...PRESETS[1],id:'folded',name:'Folded space',subtitle:'Mandelbox · Glacier',state:{...PRESETS[1].state,palette:'glacier'}},
  {...PRESETS[2],id:'fourth',name:'Fourth dimension',subtitle:'Quaternion · Violet',state:{...PRESETS[2].state,palette:'violet',slice:.2}},
  {...PRESETS[0],id:'bulb-descent',name:'Surface descent',subtitle:'Mandelbulb · close flight',state:{...PRESETS[0].state,camera:{yaw:.35,pitch:.18,distance:3.6,position:[.3810285605586059,.20220481498623247,1.043832374608493]},showGrid:false,detail:.85}},
  {...PRESETS[1],id:'box-cavern',name:'Into the folds',subtitle:'Mandelbox · close flight',state:{...PRESETS[1].state,camera:{yaw:.65,pitch:.35,distance:5.3,position:[.7767875104338589,.46853262573187776,1.0218140164922487]},iterations:12,showGrid:false,detail:.85}},
  {...PRESETS[2],id:'quaternion-descent',name:'Beyond the slice',subtitle:'Quaternion · close flight',state:{...PRESETS[2].state,camera:{yaw:.7,pitch:.22,distance:3.8,position:[.386710680823634,.13423415788485044,.4591190972040058]},iterations:12,showGrid:false,detail:.85,palette:'violet'}},
  {...PRESETS[0],id:'bulb-micro',name:'Microstructure',subtitle:'Mandelbulb · deep flight',state:{...PRESETS[0].state,camera:{yaw:.35,pitch:.18,distance:3.6,position:[.36865741643119526,.19563967743910538,1.0099414748496738]},showGrid:false,detail:1}},
  {...PRESETS[3],id:'seahorse',name:'Seahorse valley',subtitle:'Mandelbrot · 640 iterations',state:{scene:'mandelbrot',center:[-.7435,.1314],scale:.006,iterations:640,palette:'ember'}},
  {...PRESETS[3],id:'period27',name:'Period 27',subtitle:'The airplane tuning cascade',kind:'RESEARCH ATLAS',state:{scene:'mandelbrot',center:[-1.786429858055761,0],scale:.0012,iterations:768,palette:'glacier'}},
];

export const isPlane = (scene: EngineState['scene']) => scene === 'mandelbrot' || scene === 'julia';
export function applyPreset(p: ScenePreset, previous = DEFAULT_STATE): EngineState {
  return {...DEFAULT_STATE,quality:previous.quality,showGrid:previous.showGrid,...p.state};
}
