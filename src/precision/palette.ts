import type { PrecisionPalette } from './types.ts';
type Color = [number, number, number];
export const PALETTE_STOPS: Record<PrecisionPalette, Color[]> = {
  glacier: [
    [8, 17, 30],
    [23, 48, 73],
    [53, 116, 150],
    [131, 201, 211],
    [240, 244, 218],
    [111, 151, 172],
    [16, 38, 62],
  ],
  ember: [
    [19, 11, 24],
    [64, 19, 37],
    [161, 48, 39],
    [237, 114, 54],
    [255, 225, 159],
    [107, 45, 53],
    [25, 12, 33],
  ],
  violet: [
    [16, 12, 35],
    [43, 31, 87],
    [99, 70, 157],
    [176, 145, 206],
    [244, 222, 229],
    [92, 126, 161],
    [18, 28, 56],
  ],
  mono: [
    [8, 12, 17],
    [41, 48, 56],
    [115, 123, 130],
    [232, 237, 240],
    [130, 141, 149],
    [30, 39, 47],
    [7, 12, 18],
  ],
  aurora: [
    [7, 16, 26],
    [14, 69, 78],
    [44, 160, 148],
    [173, 230, 173],
    [250, 232, 179],
    [164, 108, 167],
    [41, 32, 80],
  ],
};
export function colorSample(
  smooth: number,
  palette: PrecisionPalette,
  exposure: number,
  seed: number,
): Color {
  if (smooth < 0) return [5, 9, 15];
  const stops = PALETTE_STOPS[palette];
  const position = (((smooth * 0.019 + 0.15 + Math.sin(smooth * 0.002) * 0.1) % 1) + 1) % 1;
  const index = position * stops.length;
  const a = stops[Math.floor(index) % stops.length],
    b = stops[(Math.floor(index) + 1) % stops.length];
  const blend = index - Math.floor(index);
  const ease = blend * blend * (3 - 2 * blend);
  const grain = (((seed * 16807) % 127) / 127 - 0.5) * 0.65;
  return a.map((c, channel) =>
    Math.max(0, Math.min(255, (c + (b[channel] - c) * ease) * exposure + grain)),
  ) as Color;
}
export function colorTile(
  samples: Float32Array,
  palette: PrecisionPalette,
  exposure: number,
  offset = 0,
): Uint8ClampedArray {
  const pixels = new Uint8ClampedArray(samples.length * 4);
  for (let i = 0; i < samples.length; i++) {
    const color = colorSample(samples[i], palette, exposure, i + offset);
    pixels[4 * i] = color[0];
    pixels[4 * i + 1] = color[1];
    pixels[4 * i + 2] = color[2];
    pixels[4 * i + 3] = 255;
  }
  return pixels;
}
