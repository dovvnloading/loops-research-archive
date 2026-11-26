/** Add portable, UTF-8 JSON provenance to a PNG iTXt chunk, preserving all image data. */
const encoder = new TextEncoder();
function crc32(bytes: Uint8Array): number {
  let crc = 0xffffffff;
  for (const byte of bytes) {
    crc ^= byte;
    for (let k = 0; k < 8; k++) crc = (crc >>> 1) ^ (crc & 1 ? 0xedb88320 : 0);
  }
  return (crc ^ 0xffffffff) >>> 0;
}
export function pngWithMetadata(png: Uint8Array, metadata: unknown): Uint8Array {
  if (png.length < 20 || png[0] !== 137 || String.fromCharCode(...png.subarray(1, 4)) !== 'PNG')
    throw new Error('A valid PNG image is required.');
  const payload = encoder.encode(`LOOPS\0\0\0\0\0${JSON.stringify(metadata)}`);
  const type = encoder.encode('iTXt');
  const chunk = new Uint8Array(12 + payload.length);
  const dv = new DataView(chunk.buffer);
  dv.setUint32(0, payload.length);
  chunk.set(type, 4);
  chunk.set(payload, 8);
  dv.setUint32(chunk.length - 4, crc32(chunk.subarray(4, chunk.length - 4)));
  let offset = 8,
    insert = -1;
  const source = new DataView(png.buffer, png.byteOffset, png.byteLength);
  while (offset + 12 <= png.length) {
    const length = source.getUint32(offset);
    if (offset + 12 + length > png.length) throw new Error('The PNG has a truncated chunk.');
    if (String.fromCharCode(...png.subarray(offset + 4, offset + 8)) === 'IEND') {
      insert = offset;
      break;
    }
    offset += 12 + length;
  }
  if (insert < 0) throw new Error('The PNG is missing its end marker.');
  const result = new Uint8Array(png.length + chunk.length);
  result.set(png.subarray(0, insert));
  result.set(chunk, insert);
  result.set(png.subarray(insert), insert + chunk.length);
  return result;
}
export function saveBlob(blob: Blob, name: string) {
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = name;
  a.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
