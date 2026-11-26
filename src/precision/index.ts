export { PrecisionViewport } from './PrecisionViewport.tsx';
export type { PrecisionViewportProps } from './PrecisionViewport.tsx';
export type {
  ExactComplex,
  ExactView,
  PrecisionPalette,
  PrecisionQuality,
  PrecisionStats,
  PrecisionViewportHandle,
} from './types.ts';
export {
  DEFAULT_EXACT_VIEW,
  MIN_SPAN,
  MAX_SPAN,
  normalizeDecimal,
  validateExactView,
  exactViewFromEngine,
  pointAtPixel,
  panExactView,
  zoomExactView,
  viewDepth,
  precisionBits,
  decimalToFixed,
  fixedToDecimal,
  fixedToNumber,
} from './coordinates.ts';
