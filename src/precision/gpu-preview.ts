import type { ExactView } from './types.ts';
import { PALETTE_STOPS } from './palette.ts';
const vertex = `#version 300 es
void main(){vec2 p=vec2(float((gl_VertexID<<1)&2),float(gl_VertexID&2));gl_Position=vec4(p*2.0-1.0,0,1);}`;
const fragment = `#version 300 es
precision highp float;
out vec4 color;
uniform vec2 resolution, centerHi, centerLo, juliaHi, juliaLo;
uniform float span, exposure, escapeRadius;
uniform int iterations, family;
uniform vec3 stops[7];
vec2 add(vec2 a,vec2 b){float s=a.x+b.x;float v=s-a.x;float e=(a.x-(s-v))+(b.x-v)+a.y+b.y;float h=s+e;return vec2(h,e-(h-s));}
vec2 mul(vec2 a,vec2 b){float p=a.x*b.x;float ca=4097.0*a.x,cb=4097.0*b.x;float ah=ca-(ca-a.x),al=a.x-ah,bh=cb-(cb-b.x),bl=b.x-bh;float e=((ah*bh-p)+ah*bl+al*bh)+al*bl+a.x*b.y+a.y*b.x;float h=p+e;return vec2(h,e-(h-p));}
void main(){
 vec2 uv=(gl_FragCoord.xy-resolution*.5)/resolution.y;
 vec2 px=add(vec2(centerHi.x,centerLo.x),vec2(uv.x*span,0));
 vec2 py=add(vec2(centerHi.y,centerLo.y),vec2(uv.y*span,0));
 vec2 cx=family==1?vec2(juliaHi.x,juliaLo.x):px,cy=family==1?vec2(juliaHi.y,juliaLo.y):py;
 vec2 zx=family==1?px:vec2(0),zy=family==1?py:vec2(0);
 float q=(cx.x-.25)*(cx.x-.25)+cy.x*cy.x;
 bool interior=family==0&&(q*(q+cx.x-.25)<.25*cy.x*cy.x-.000001||(cx.x+1.0)*(cx.x+1.0)+cy.x*cy.x<.0625-.000001);
 float magnitude=zx.x*zx.x+zy.x*zy.x,count=0.0;bool escaped=magnitude>escapeRadius*escapeRadius;
 for(int n=1;n<=2048;n++){
  if(n>iterations||interior||escaped)break;
  vec2 xx=mul(zx,zx),yy=mul(zy,zy),xy=mul(zx,zy);
  zx=add(add(xx,-yy),cx);zy=add(xy*2.0,cy);
  magnitude=zx.x*zx.x+zy.x*zy.x;count=float(n);escaped=magnitude>escapeRadius*escapeRadius;
 }
 vec3 rgb=vec3(5,9,15)/255.0;
 if(escaped){
  float smoothN=max(0.0,count+1.0-log2(log2(max(1.000001,sqrt(magnitude)))));
  float position=fract(smoothN*.019+.15+sin(smoothN*.002)*.1)*7.0;
  int a=int(floor(position));float t=fract(position);t=t*t*(3.0-2.0*t);
  rgb=mix(stops[a],stops[(a+1)%7],t)/255.0*exposure;
 }
 color=vec4(clamp(rgb,0.0,1.0),1);
}`;

/** GPU preview only. Final samples are always recomputed by the Float64/BigInt worker. */
export class GpuPreview {
  private canvas: OffscreenCanvas;
  private gl: WebGL2RenderingContext;
  private program: WebGLProgram;
  private locations = new Map<string, WebGLUniformLocation | null>();
  private constructor(canvas: OffscreenCanvas, gl: WebGL2RenderingContext, program: WebGLProgram) {
    this.canvas = canvas;
    this.gl = gl;
    this.program = program;
  }
  static create(): GpuPreview | null {
    if (typeof OffscreenCanvas === 'undefined') return null;
    try {
      const canvas = new OffscreenCanvas(32, 32);
      const gl = canvas.getContext('webgl2', {
        antialias: false,
        alpha: false,
        depth: false,
        preserveDrawingBuffer: true,
      });
      if (!gl) return null;
      const debug = gl.getExtension('WEBGL_debug_renderer_info');
      if (
        debug &&
        /swiftshader|llvmpipe|software/i.test(
          String(gl.getParameter(debug.UNMASKED_RENDERER_WEBGL)),
        )
      ) {
        gl.getExtension('WEBGL_lose_context')?.loseContext();
        return null;
      }
      function shader(type: number, source: string) {
        const shader = gl!.createShader(type);
        if (!shader) throw new Error('Shader allocation failed.');
        gl!.shaderSource(shader, source);
        gl!.compileShader(shader);
        if (!gl!.getShaderParameter(shader, gl!.COMPILE_STATUS)) {
          gl!.deleteShader(shader);
          throw new Error('GPU preview unavailable.');
        }
        return shader;
      }
      const program = gl.createProgram();
      if (!program) return null;
      const vs = shader(gl.VERTEX_SHADER, vertex),
        fs = shader(gl.FRAGMENT_SHADER, fragment);
      gl.attachShader(program, vs);
      gl.attachShader(program, fs);
      gl.linkProgram(program);
      gl.deleteShader(vs);
      gl.deleteShader(fs);
      if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
        gl.deleteProgram(program);
        return null;
      }
      return new GpuPreview(canvas, gl, program);
    } catch {
      return null;
    }
  }
  render(
    view: ExactView,
    width: number,
    height: number,
    exposure: number,
  ): Uint8ClampedArray | null {
    try {
      const gl = this.gl;
      if (gl.isContextLost() || Number(view.span) < 1e-7) return null;
      this.canvas.width = width;
      this.canvas.height = height;
      gl.viewport(0, 0, width, height);
      gl.useProgram(this.program);
      const location = (name: string) => {
        if (!this.locations.has(name))
          this.locations.set(name, gl.getUniformLocation(this.program, name));
        return this.locations.get(name)!;
      };
      const re = Number(view.center.re),
        im = Number(view.center.im),
        jr = Number(view.julia.re),
        ji = Number(view.julia.im);
      gl.uniform2f(location('resolution'), width, height);
      gl.uniform2f(location('centerHi'), Math.fround(re), Math.fround(im));
      gl.uniform2f(location('centerLo'), re - Math.fround(re), im - Math.fround(im));
      gl.uniform2f(location('juliaHi'), Math.fround(jr), Math.fround(ji));
      gl.uniform2f(location('juliaLo'), jr - Math.fround(jr), ji - Math.fround(ji));
      gl.uniform1f(location('span'), Number(view.span));
      gl.uniform1f(location('exposure'), exposure);
      gl.uniform1f(
        location('escapeRadius'),
        view.family === 'julia' ? Math.max(4, Math.hypot(jr, ji) + 1) : 4,
      );
      gl.uniform1i(location('iterations'), Math.min(2048, view.iterations));
      gl.uniform1i(location('family'), view.family === 'julia' ? 1 : 0);
      gl.uniform3fv(location('stops[0]'), PALETTE_STOPS[view.palette].flat());
      gl.drawArrays(gl.TRIANGLES, 0, 3);
      const pixels = new Uint8Array(width * height * 4);
      gl.readPixels(0, 0, width, height, gl.RGBA, gl.UNSIGNED_BYTE, pixels);
      if (gl.getError() !== gl.NO_ERROR) return null;
      const flipped = new Uint8ClampedArray(pixels.length);
      for (let y = 0; y < height; y++)
        flipped.set(
          pixels.subarray(y * width * 4, (y + 1) * width * 4),
          (height - y - 1) * width * 4,
        );
      return flipped;
    } catch {
      return null;
    }
  }
}
