import type { Palette } from '../types';

// These values are shared by the GPU, Float64 ray marcher, navigation and session decoder.
export const CONTROL_LIMITS = {
  fov: [51.75, 20, 95],
  flightSpeed: [1, .1, 3],
  animationSpeed: [1, .1, 4],
  gamma: [2.2, 1, 3.5],
  contrast: [1, .5, 1.8],
  saturation: [1, 0, 2],
  lightAzimuth: [-32, -180, 180],
  lightElevation: [37, 5, 85],
  lightIntensity: [1, 0, 2.5],
  ambientIntensity: [1, 0, 3],
  bandFrequency: [.21, .02, 1.5],
  bandPhase: [.15, 0, 6.283185307179586],
  planeBailout: [16, 2, 64],
  reliefHeight: [1, .1, 3],
  contourDensity: [20, 0, 60],
} as const;
export type ControlKey = keyof typeof CONTROL_LIMITS;
export type InstrumentControls = Record<ControlKey, number>;
export const DEFAULT_CONTROLS = Object.fromEntries(
  Object.entries(CONTROL_LIMITS).map(([key, [value]]) => [key, value])
) as InstrumentControls;
export function normalizeControls(value: unknown): InstrumentControls {
  const source = value && typeof value === 'object' ? value as Record<string, unknown> : {};
  return Object.fromEntries(Object.entries(CONTROL_LIMITS).map(([key, [fallback, min, max]]) => {
    const n = source[key];
    return [key, typeof n === 'number' && Number.isFinite(n) ? Math.max(min, Math.min(max, n)) : fallback];
  })) as InstrumentControls;
}
export const projection = (c: InstrumentControls) => 2 * Math.tan(c.fov * Math.PI / 360);
export function lightDirection(c: InstrumentControls): [number, number, number] {
  const a = c.lightAzimuth * Math.PI / 180, e = c.lightElevation * Math.PI / 180;
  return [Math.sin(a)*Math.cos(e), Math.sin(e), Math.cos(a)*Math.cos(e)];
}
const clamp = (v: number) => Math.max(0, Math.min(1, v));
export function paletteColor(palette: Palette, t: number): [number, number, number] {
  const colors: Record<Palette, [[number,number,number],[number,number,number]]> = {
    glacier: [[.055,.105,.23],[.73,.84,1]],
    ember: [[.18,.025,.018],[1,.73,.36]],
    violet: [[.12,.055,.22],[.81,.73,1]],
    mono: [[.12,.12,.12],[.94,.94,.94]],
  };
  const [a,b] = colors[palette] || colors.glacier;
  return a.map((v,i) => v+(b[i]-v)*clamp(t)) as [number,number,number];
}
export function toneColor(rgb: [number,number,number], exposure: number, c: InstrumentControls): [number,number,number] {
  const mapped = rgb.map(v => clamp(((1-Math.exp(-Math.max(0,v)*exposure))**(1/c.gamma)-.5)*c.contrast+.5));
  const luma = mapped[0]*.2126+mapped[1]*.7152+mapped[2]*.0722;
  return mapped.map(v => Math.round(255*clamp(luma+(v-luma)*c.saturation))) as [number,number,number];
}
