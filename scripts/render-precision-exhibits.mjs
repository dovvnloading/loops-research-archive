/** Recreate exact, deep-window thumbnails with the actual precision renderer. */
import fs from 'node:fs';
import { prepareKernel } from '../src/precision/kernel.ts';
import { colorTile } from '../src/precision/palette.ts';
const views = [
  {
    id: 'deep-spiral',
    center: {
      re: '-0.743643887037151007923796441120318475',
      im: '0.131825904205311970493132056385139818',
    },
    span: '0.000000000003',
    iterations: 2400,
    palette: 'glacier',
  },
  {
    id: 'imaginary-gateway',
    center: { re: '0', im: '1' },
    span: '1e-120',
    iterations: 2048,
    palette: 'aurora',
  },
];
for (const source of views) {
  const width = 440,
    height = 300;
  const view = { family: 'mandelbrot', julia: { re: '-0.74543', im: '0.11301' }, ...source };
  const kernel = prepareKernel(view);
  const samples = new Float32Array(width * height);
  for (let y = 0; y < height; y++)
    for (let x = 0; x < width; x++)
      samples[y * width + x] = kernel.sample(x, y, width, height).smooth;
  const rgba = colorTile(samples, view.palette, 1.1),
    rgb = Buffer.alloc(width * height * 3);
  for (let i = 0; i < samples.length; i++) rgb.set(rgba.subarray(i * 4, i * 4 + 3), i * 3);
  fs.writeFileSync(
    new URL(`../public/exhibits/${source.id}.ppm`, import.meta.url),
    Buffer.concat([Buffer.from(`P6\n${width} ${height}\n255\n`), rgb]),
  );
  console.log('Computed exact thumbnail', source.id);
}
