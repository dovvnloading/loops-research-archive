/** Decimal strings are the source of truth. Never round them through Number. */
export interface ExactComplex {
  re: string;
  im: string;
}
export type PrecisionPalette = 'glacier' | 'ember' | 'violet' | 'mono' | 'aurora';
export interface ExactView {
  family: 'mandelbrot' | 'julia';
  center: ExactComplex;
  /** Vertical span of the complex plane, independently of screen aspect ratio. */
  span: string;
  julia: ExactComplex;
  iterations: number;
  palette: PrecisionPalette;
}
export type PrecisionQuality = 'auto' | 'high' | 'balanced' | 'low';
export interface PrecisionStats {
  fps: number;
  resolution: string;
  precision: string;
  renderer: string;
  phase: 'preview' | 'refining' | 'repairing' | 'complete' | 'error';
  progress: number;
  elapsedMs: number;
  referenceBits: number;
  repairedPixels: number;
  precisionDigits: number;
}
export interface PrecisionViewportHandle {
  capture(): string;
  zoom(multiplier: number): void;
  reset(): void;
}
export interface PrecisionRenderRequest {
  type: 'render';
  id: number;
  view: ExactView;
  width: number;
  height: number;
  quality: PrecisionQuality;
  exposure: number;
}
export type PrecisionWorkerRequest = PrecisionRenderRequest | { type: 'cancel'; id: number };
export type PrecisionWorkerResponse =
  | {
      type: 'tile';
      id: number;
      x: number;
      y: number;
      width: number;
      height: number;
      frameWidth: number;
      frameHeight: number;
      pixels: Uint8ClampedArray;
      stats: PrecisionStats;
    }
  | { type: 'complete'; id: number; stats: PrecisionStats }
  | { type: 'error'; id: number; message: string };
