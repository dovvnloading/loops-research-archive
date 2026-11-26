/// <reference lib="webworker" />
// A small, cancellable-by-replacement numerical preview. The main engine owns
// full resolution GPU rendering; these pixels never claim proof status.
self.onmessage = ({ data }: MessageEvent<{ id: number; mode: 'julia' | 'parameter'; width: number; height: number; c: [number, number] }>) => {
  const { id, mode, width, height, c } = data;
  const pixels = new Uint8ClampedArray(width * height * 4);
  for (let y = 0; y < height; y++) for (let x = 0; x < width; x++) {
    const px = mode === 'parameter' ? x / width * 3.2 - 2.3 : (x / width - 0.5) * 3.7;
    const py = mode === 'parameter' ? (0.5 - y / height) * 2.2 : (0.5 - y / height) * 3.7 * height / width;
    const cr = mode === 'parameter' ? px : c[0], ci = mode === 'parameter' ? py : c[1];
    let zr = mode === 'parameter' ? 0 : px, zi = mode === 'parameter' ? 0 : py;
    let iteration = 0;
    const limit = 180;
    for (; iteration < limit && zr * zr + zi * zi <= 256; iteration++) {
      const next = zr * zr - zi * zi + cr; zi = 2 * zr * zi + ci; zr = next;
    }
    const index = (y * width + x) * 4;
    if (iteration >= limit) { pixels[index] = 10; pixels[index + 1] = 10; pixels[index + 2] = 9; }
    else {
      const smooth = iteration + 1 - Math.log2(Math.max(1, Math.log2(zr * zr + zi * zi) / 2));
      const t = Math.min(1, Math.max(0, smooth / 50));
      const v = 0.15 + 0.85 * (0.5 + 0.5 * Math.cos(4.4 + t * 13));
      pixels[index] = 12 + v * 112;
      pixels[index + 1] = 12 + v * 108;
      pixels[index + 2] = 11 + v * 98;
    }
    pixels[index + 3] = 255;
  }
  self.postMessage({ id, width, height, pixels }, { transfer: [pixels.buffer] });
};
export {};
