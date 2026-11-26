/** Reproducible exhibit thumbnails computed from the same numerical fields as LOOPS. */
import fs from 'node:fs';
import { prepareVolume } from '../src/engine/volume64.ts';
import { DEFAULT_STATE, PRESETS, CURATED, applyPreset } from '../src/presets.ts';
const width = 440,
  height = 300;
const volumes = [
  ['eightfold', 'eightfold'],
  ['coral', 'coral'],
  ['cathedral', 'cathedral'],
  ['folded', 'folded'],
  ['quaternion', 'fourth'],
];
const dir = new URL('../public/exhibits/', import.meta.url);
fs.mkdirSync(dir, { recursive: true });
function ppm(name, pixels) {
  fs.writeFileSync(
    new URL(name + '.ppm', dir),
    Buffer.concat([Buffer.from(`P6\n${width} ${height}\n255\n`), pixels]),
  );
  console.log('Rendered', name);
}
for (const [name, preset] of volumes) {
  const p = CURATED.find((x) => x.id === preset);
  const state = { ...applyPreset(p), showGrid: false, detail: 0.8 };
  const frame = prepareVolume({ state, width, height, preview: false });
  const pixels = Buffer.alloc(width * height * 3);
  for (let y = 0; y < height; y++)
    for (let x = 0; x < width; x++) {
      const rgba = frame.pixel(x, y);
      pixels.set(rgba.slice(0, 3), (y * width + x) * 3);
    }
  ppm(name, pixels);
}
const planes = [
  ['mandelbrot', -0.5, 0, 3.2, 768, false, 0, 0, 'glacier'],
  ['seahorse', -0.7435, 0.1314, 0.006, 960, false, 0, 0, 'ember'],
  ['julia', 0, 0, 3.1, 768, true, -0.74543, 0.11301, 'violet'],
  ['airplane', -1.786429858055761, 0, 0.0012, 1536, false, 0, 0, 'glacier'],
  ['deep-spiral', -0.743643887037151, 0.131825904205312, 3e-10, 2000, false, 0, 0, 'glacier'],
  ['dendrite', 0, 0, 3.2, 1024, true, 0, 1, 'ember'],
  ['landscape', -0.5, 0, 3.2, 768, false, 0, 0, 'glacier'],
];
for (const [name, re, im, span, iterations, julia, jre, jim, palette] of planes) {
  const pixels = Buffer.alloc(width * height * 3);
  for (let y = 0; y < height; y++)
    for (let x = 0; x < width; x++) {
      const cr = julia ? jre : re + ((x + 0.5 - width / 2) / height) * span,
        ci = julia ? jim : im + ((height / 2 - y - 0.5) / height) * span;
      let zr = julia ? re + ((x + 0.5 - width / 2) / height) * span : 0,
        zi = julia ? im + ((height / 2 - y - 0.5) / height) * span : 0,
        n = 0;
      for (; n < iterations && zr * zr + zi * zi < 256; n++) {
        const nz = zr * zr - zi * zi + cr;
        zi = 2 * zr * zi + ci;
        zr = nz;
      }
      let rgb = [5, 8, 15];
      if (n < iterations) {
        const mu = n + 1 - Math.log2(Math.max(1e-8, Math.log2(Math.hypot(zr, zi))));
        const t = 0.5 + 0.5 * Math.cos(0.09 * mu + 0.8);
        const s = t * t * (3 - 2 * t);
        const stops =
          palette === 'ember'
            ? [
                [19, 15, 22],
                [236, 171, 108],
              ]
            : palette === 'violet'
              ? [
                  [15, 14, 36],
                  [205, 184, 240],
                ]
              : [
                  [8, 22, 40],
                  [187, 217, 230],
                ];
        rgb = stops[0].map((a, i) => Math.round(a + (stops[1][i] - a) * s));
      }
      pixels.set(rgb, (y * width + x) * 3);
    }
  ppm(name, pixels);
}
