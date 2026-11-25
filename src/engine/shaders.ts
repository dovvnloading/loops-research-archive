/** All scenes are generated from mathematical iterations, never image assets. */
export const fullscreenVertex = `#version 300 es
precision highp float;
void main() {
  vec2 p = vec2(float((gl_VertexID << 1) & 2), float(gl_VertexID & 2));
  gl_Position = vec4(p * 2.0 - 1.0, 0.0, 1.0);
}`;

const palette = `
vec3 palette(float t) {
  if (uPalette == 1) return mix(vec3(0.18,0.025,0.018),vec3(1.0,0.73,0.36),clamp(t,0.0,1.0));
  if (uPalette == 2) return mix(vec3(0.12,0.055,0.22),vec3(0.81,0.73,1.0),clamp(t,0.0,1.0));
  if (uPalette == 3) return vec3(0.12+0.82*clamp(t,0.0,1.0));
  return mix(vec3(0.075,0.20,0.20),vec3(0.85,0.93,0.87),clamp(t,0.0,1.0));
}
float hash21(vec2 p) { return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453); }
vec3 finishColor(vec3 color) {
  color = vec3(1.0)-exp(-max(color,vec3(0.0))*uExposure);
  color = pow(color,vec3(1.0/2.2));
  return color + (hash21(gl_FragCoord.xy)-0.5)/255.0;
}
`;

export const volumeFragment = `#version 300 es
precision highp float;
out vec4 outColor;
uniform vec2 uResolution;
uniform vec3 uCamera;
uniform vec3 uEye;
uniform int uScene;
uniform int uIterations;
uniform int uPalette;
uniform float uPower;
uniform float uBailout;
uniform float uDetail;
uniform float uExposure;
uniform float uSlice;
uniform float uTrap;
uniform vec2 uJuliaHi;
uniform bool uGrid;
${palette}

vec2 bulb(vec3 p) {
  vec3 z=p;
  float dr=1.0, r=0.0, trap=10.0;
  float power=clamp(uPower,2.0,16.0);
  for(int i=0;i<64;i++) {
    if(i>=uIterations) break;
    float component=max(max(abs(z.x),abs(z.y)),abs(z.z));
    r=component>0.0 ? length(z/component)*component : 0.0;
    trap=min(trap,abs(z.y)+0.12*r);
    if(r>uBailout) break;
    if(r<0.0000001) { z=p; continue; }
    float theta=acos(clamp(z.z/r,-1.0,1.0));
    float phi=atan(z.y,z.x);
    float zr=pow(r,power-1.0);
    dr=zr*power*dr+1.0;
    zr*=r;
    theta*=power; phi*=power;
    z=zr*vec3(sin(theta)*cos(phi),sin(phi)*sin(theta),cos(theta))+p;
  }
  float m=max(max(abs(z.x),abs(z.y)),abs(z.z));
  r=m>0.0?length(z/m)*m:0.0;
  return vec2(r>uBailout?0.5*log(r)*r/max(dr,0.00001):0.0,trap);
}

vec2 boxFractal(vec3 p) {
  // The rendered coordinate is half the conventional box-fold coordinate.
  vec3 z=p*2.0, c=z;
  float dr=1.0, trap=10.0;
  float scale=-clamp(uPower,1.2,3.0);
  for(int i=0;i<40;i++) {
    if(i>=uIterations) break;
    z=clamp(z,-1.0,1.0)*2.0-z;
    float r2=dot(z,z);
    trap=min(trap,abs(z.y)*0.45+0.06*r2);
    float fold=clamp(1.0/max(r2,0.00001),1.0,4.0);
    z*=fold; dr*=fold;
    z=scale*z+c; dr=min(1e30,dr*abs(scale)+1.0);
  }
  return vec2(length(z)/abs(dr)*0.5,trap);
}

vec2 quaternion(vec3 p) {
  vec4 z=vec4(p,uSlice);
  vec4 c=vec4(uJuliaHi,0.18,0.0);
  float r2=dot(z,z), dr=1.0, trap=10.0;
  for(int i=0;i<64;i++) {
    if(i>=uIterations) break;
    trap=min(trap,length(z.yz));
    if(r2>uBailout*uBailout) break;
    dr=min(1e30,dr*max(2.0*sqrt(r2),0.000001));
    z=vec4(z.x*z.x-dot(z.yzw,z.yzw),2.0*z.x*z.yzw)+c;
    r2=dot(z,z);
  }
  float r=sqrt(r2);
  return vec2(r>uBailout?0.5*r*log(r)/max(dr,0.000000000001):0.0,trap);
}

vec2 mapScene(vec3 p) {
  if(uScene==1) return boxFractal(p);
  if(uScene==2) return quaternion(p);
  return bulb(p);
}

vec3 normalAt(vec3 p,float eps) {
  vec2 e=vec2(1.0,-1.0)*eps;
  vec3 g=e.xyy*mapScene(p+e.xyy).x + e.yyx*mapScene(p+e.yyx).x
    +e.yxy*mapScene(p+e.yxy).x+e.xxx*mapScene(p+e.xxx).x;
  return length(g)>1e-20?normalize(g):vec3(0,1,0);
}

float ambientOcclusion(vec3 p,vec3 n,float eps) {
  float occlusion=0.0, weight=1.0;
  for(int i=1;i<=4;i++) {
    float h=eps*float(i*i)*6.0;
    occlusion+=(h-mapScene(p+n*h).x)*weight;
    weight*=0.55;
  }
  return clamp(1.0-0.28*occlusion/max(eps*8.0,0.000001),0.15,1.0);
}

float shadow(vec3 p,vec3 light,float eps) {
  float result=1.0,t=eps*6.0;
  for(int i=0;i<18;i++) {
    float h=mapScene(p+light*t).x;
    result=min(result,10.0*h/t);
    t+=clamp(h*0.7,eps,0.18);
    if(result<0.05 || t>2.8) break;
  }
  return clamp(result,0.08,1.0);
}

void main() {
  vec2 uv=(gl_FragCoord.xy-uResolution*0.5)/uResolution.y;
  vec3 ro=uEye;
  vec3 forward=-vec3(sin(uCamera.x)*cos(uCamera.y),sin(uCamera.y),cos(uCamera.x)*cos(uCamera.y));
  vec3 right=normalize(cross(forward,vec3(0,1,0)));
  vec3 up=cross(right,forward);
  vec3 rd=normalize(forward+0.97*(uv.x*right+uv.y*up));
  vec3 color=vec3(0.008,0.014,0.017);
  color+=vec3(0.007,0.011,0.011)*exp(-3.0*dot(uv,uv));
  float radius=uScene==1 ? 6.0 : max(1.55,pow(2.0,1.0/(max(uPower,2.0)-1.0))+0.05);
  if(uScene==2) radius=max(1.55,0.5*(1.0+sqrt(1.0+4.0*length(vec4(uJuliaHi,0.18,0.0))))+0.05);
  float b=dot(ro,rd), disc=b*b-dot(ro,ro)+radius*radius;
  float travel=0.0, trap=0.0, epsilon=0.0003;
  bool hit=false;
  if(disc>0.0) {
    travel=max(0.0,-b-sqrt(disc));
    float exitT=-b+sqrt(disc);
    for(int i=0;i<420;i++) {
      if(i>=int(mix(110.0,420.0,uDetail))) break;
      vec3 p=ro+rd*travel;
      vec2 sampleValue=mapScene(p);
      float worldFloor=2e-7*max(1.0,max(abs(p.x),max(abs(p.y),abs(p.z))));
      epsilon=max(worldFloor,travel/uResolution.y*mix(0.85,0.26,uDetail));
      if(sampleValue.x<epsilon) { hit=true; trap=sampleValue.y; break; }
      travel+=max(sampleValue.x*0.62,epsilon*0.5);
      if(travel>exitT) break;
    }
  }
  if(hit) {
    vec3 p=ro+rd*travel;
    vec3 n=normalAt(p,epsilon*1.5);
    vec3 key=normalize(vec3(-2.5,3.5,4.0));
    vec3 rim=normalize(vec3(3.0,1.0,-2.0));
    float diffuse=max(dot(n,key),0.0);
    float ao=ambientOcclusion(p,n,epsilon);
    float shade=shadow(p+n*epsilon*5.0,key,epsilon);
    float orbit=clamp(exp(-3.5*trap),0.0,1.0);
    float material=clamp(0.54+(0.06+0.32*uTrap)*sin(trap*8.0)+0.18*n.y,0.0,1.0);
    vec3 base=palette(material);
    if(uPalette==0) base=mix(base,vec3(0.72,0.51,0.27),orbit*uTrap*0.48);
    float specular=pow(max(dot(n,normalize(key-rd)),0.0),38.0);
    float edge=pow(1.0-max(dot(n,-rd),0.0),3.5);
    float headlight=max(dot(n,-rd),0.0);
    float nearLight=1.0-smoothstep(0.02,0.65,travel);
    color=base*(0.16*ao+diffuse*shade*1.15*ao+headlight*nearLight*0.65);
    color+=vec3(0.78,0.9,0.94)*specular*shade*0.34;
    color+=palette(0.75)*pow(max(dot(n,rim),0.0),2.0)*0.22*ao;
    color+=vec3(0.20,0.32,0.30)*edge*0.30;
    color*=mix(0.8,1.0,ao);
  } else if(uGrid && rd.y<-0.001) {
    float t=(-1.35-ro.y)/rd.y;
    if(t>0.0) {
      vec3 point=ro+rd*t;
      vec2 coord=point.xz*2.0;
      vec2 derivative=max(fwidth(coord),vec2(0.0001));
      vec2 grid=abs(fract(coord-0.5)-0.5)/derivative;
      float line=1.0-min(min(grid.x,grid.y),1.0);
      float fade=exp(-0.14*dot(point.xz,point.xz))*exp(-0.05*t);
      color+=vec3(0.025,0.055,0.052)*line*fade;
    }
  }
  color*=1.0-0.3*smoothstep(0.25,1.2,length(uv));
  outColor=vec4(finishColor(color),1.0);
}`;

export const complexFragment = `#version 300 es
precision highp float;
out vec4 outColor;
uniform vec2 uResolution;
uniform vec2 uCenterHi;
uniform vec2 uCenterLo;
uniform vec2 uJuliaHi;
uniform vec2 uJuliaLo;
uniform float uScale;
uniform int uScene;
uniform int uIterations;
uniform int uPalette;
uniform float uExposure;
uniform float uTrap;
uniform bool uGrid;
${palette}

// Unevaluated sums of two float32 values; high and low coordinates arrive
// separately from JavaScript. This is finite-precision numerical exploration.
vec2 dsAdd(vec2 a,vec2 b) {
  float s=a.x+b.x;
  float v=s-a.x;
  float e=(a.x-(s-v))+(b.x-v)+a.y+b.y;
  float hi=s+e;
  return vec2(hi,e-(hi-s));
}
vec2 dsMul(vec2 a,vec2 b) {
  float product=a.x*b.x;
  float ca=4097.0*a.x;
  float cb=4097.0*b.x;
  float ah=ca-(ca-a.x), al=a.x-ah;
  float bh=cb-(cb-b.x), bl=b.x-bh;
  float error=((ah*bh-product)+ah*bl+al*bh)+al*bl;
  error+=a.x*b.y+a.y*b.x;
  float hi=product+error;
  return vec2(hi,error-(hi-product));
}

void main() {
  vec2 uv=(gl_FragCoord.xy-uResolution*0.5)/uResolution.y;
  vec2 px=dsAdd(vec2(uCenterHi.x,uCenterLo.x),vec2(uv.x*uScale,0));
  vec2 py=dsAdd(vec2(uCenterHi.y,uCenterLo.y),vec2(uv.y*uScale,0));
  vec2 cx=uScene==4 ? vec2(uJuliaHi.x,uJuliaLo.x) : px;
  vec2 cy=uScene==4 ? vec2(uJuliaHi.y,uJuliaLo.y) : py;
  vec2 zx=uScene==4 ? px : vec2(0);
  vec2 zy=uScene==4 ? py : vec2(0);
  float mag2=0.0, count=0.0, orbit=10.0;
  bool escaped=false;
  int limit=clamp(uIterations,32,4096);
  float ccx=cx.x-0.25, ccy2=cy.x*cy.x;
  float q=ccx*ccx+ccy2;
  // Keep an explicit margin: do not decide a fine boundary with float32 tests.
  bool interior=uScene!=4 && (q*(q+ccx)<0.25*ccy2-0.000001 || (cx.x+1.0)*(cx.x+1.0)+ccy2<0.0625-0.000001);
  for(int i=0;i<4096;i++) {
    if(i>=limit || interior) break;
    vec2 xx=dsMul(zx,zx), yy=dsMul(zy,zy), xy=dsMul(zx,zy);
    zx=dsAdd(dsAdd(xx,-yy),cx);
    zy=dsAdd(xy*2.0,cy);
    mag2=zx.x*zx.x+zy.x*zy.x;
    orbit=min(orbit,abs(zy.x)+0.05*abs(zx.x));
    count=float(i);
    if(mag2>256.0) { escaped=true; break; }
  }
  vec3 color=vec3(0.008,0.016,0.018);
  if(escaped) {
    float smoothN=count+1.0-log2(max(log2(max(sqrt(mag2),1.00001)),0.0001));
    float bands=0.5+0.5*cos(smoothN*0.21+0.15);
    float light=0.22+0.78*bands;
    color=palette(light);
    color*=0.25+0.75*(1.0-exp(-smoothN*0.07));
    color=mix(color,palette(0.95),exp(-orbit*4.0)*uTrap*0.16);
  }
  if(uGrid && uScale>0.0001) {
    vec2 p=vec2(px.x,py.x);
    float spacing=pow(10.0,floor(log(uScale)/log(10.0))-0.5);
    vec2 q=p/spacing;
    vec2 grid=abs(fract(q-0.5)-0.5)/max(fwidth(q),vec2(0.00001));
    float line=1.0-min(min(grid.x,grid.y),1.0);
    color+=vec3(0.018,0.033,0.032)*line;
    vec2 axes=abs(p)/max(fwidth(p),vec2(0.0000001));
    color+=vec3(0.07,0.12,0.10)*(1.0-min(min(axes.x,axes.y),1.0));
  }
  outColor=vec4(finishColor(color),1.0);
}`;

export const landscapeVertex = `#version 300 es
precision highp float;
layout(location=0) in vec2 aPosition;
uniform vec2 uResolution;
uniform vec2 uCenterHi;
uniform float uScale;
uniform vec3 uCamera;
uniform int uIterations;
uniform float uBailout;
out vec3 vPosition;
out float vHeight;
out float vOrbit;
out vec2 vUv;
void main() {
  vec2 c=uCenterHi+aPosition*uScale/3.2;
  vec2 z=vec2(0.0);
  float n=0.0;
  float orbit=10.0;
  bool escaped=false;
  int limit=clamp(uIterations,32,512);
  for(int i=0;i<512;i++) {
    if(i>=limit) break;
    z=vec2(z.x*z.x-z.y*z.y,2.0*z.x*z.y)+c;
    orbit=min(orbit,abs(z.y)+0.05*abs(z.x));
    n=float(i);
    if(dot(z,z)>uBailout*uBailout) {escaped=true; break;}
  }
  float h=0.94;
  if(escaped) {
    float smoothN=max(0.0,n+1.0-log2(max(log2(max(length(z),1.0001)),0.0001)));
    h=min(0.9,log2(1.0+smoothN)*0.17);
  }
  vec3 pos=vec3(aPosition.x,(h-0.48)*1.2,-aPosition.y);
  vPosition=pos;
  vHeight=h;
  vOrbit=orbit;
  vUv=aPosition;
  float pitch=clamp(uCamera.y,0.3,1.4);
  vec3 eye=uCamera.z*vec3(sin(uCamera.x)*cos(pitch),sin(pitch),cos(uCamera.x)*cos(pitch));
  vec3 forward=normalize(-eye);
  vec3 right=normalize(cross(forward,vec3(0,1,0)));
  vec3 up=cross(right,forward);
  vec3 relative=pos-eye;
  float depth=dot(relative,forward);
  float zNear=0.05, zFar=40.0;
  gl_Position=vec4(dot(relative,right)/(uResolution.x/uResolution.y*0.54),
    dot(relative,up)/0.54, (zFar+zNear)/(zFar-zNear)*depth-2.0*zFar*zNear/(zFar-zNear),depth);
}`;

export const landscapeFragment = `#version 300 es
precision highp float;
out vec4 outColor;
in vec3 vPosition;
in float vHeight;
in float vOrbit;
in vec2 vUv;
uniform int uPalette;
uniform float uExposure;
uniform float uTrap;
uniform bool uGrid;
${palette}
void main() {
  vec3 normal=normalize(cross(dFdx(vPosition),dFdy(vPosition)));
  if(normal.y<0.0) normal=-normal;
  float light=0.22+0.9*max(dot(normal,normalize(vec3(-1,3,2))),0.0);
  vec3 color=palette(0.12+vHeight*0.85)*light;
  color=mix(color,palette(0.95)*light,exp(-vOrbit*4.0)*uTrap*0.25);
  float contour=abs(fract(vHeight*20.0)-0.5)/max(fwidth(vHeight*20.0),0.02);
  color*=0.78+0.22*clamp(contour,0.0,1.0);
  if(uGrid) {
    vec2 grid=abs(fract(vUv*6.0-0.5)-0.5)/max(fwidth(vUv*6.0),vec2(0.0001));
    color+=palette(0.9)*0.08*(1.0-min(min(grid.x,grid.y),1.0));
  }
  outColor=vec4(finishColor(color),1.0);
}`;
