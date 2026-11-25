export type SceneId = 'mandelbulb' | 'mandelbox' | 'quaternion' | 'mandelbrot' | 'julia' | 'landscape';
export type Palette = 'glacier' | 'ember' | 'violet' | 'mono';
export type Quality = 'auto' | 'high' | 'balanced' | 'low';
export type Workspace = 'explore' | 'dynamics' | 'atlas' | 'lab' | 'archive';

export interface EngineState {
  scene: SceneId;
  power: number;
  iterations: number;
  bailout: number;
  detail: number;
  exposure: number;
  palette: Palette;
  camera: { yaw: number; pitch: number; distance: number; position?: [number, number, number] };
  center: [number, number];
  scale: number;
  julia: [number, number];
  slice: number;
  autoRotate: boolean;
  showGrid: boolean;
  quality: Quality;
  orbitTrap: number;
}

export interface EngineStats {
  fps: number;
  resolution: string;
  precision: string;
  renderer: string;
  iterations?: number;
  clearance?: number;
  refinement?: string;
}

export interface EngineHooks {
  onStats?: (stats: EngineStats) => void;
  onChange?: (patch: Partial<EngineState>) => void;
  onSelectParameter?: (c: [number, number]) => void;
  onError?: (message: string) => void;
}

export interface ScenePreset {
  id: string;
  name: string;
  subtitle: string;
  kind: '3D FRACTAL' | 'COMPLEX DYNAMICS' | 'RESEARCH ATLAS';
  state: Partial<EngineState>;
  description: string;
  formula: string;
}
