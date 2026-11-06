#!/usr/bin/env node
/**
 * Generate README figures from this repository's own exact period-nine manifest.
 *
 * Run: node code/generate_readme_research_figures.mjs [--check]
 * Inputs: results/period27_tip_ray_portrait.json
 * Not a renderer of Julia sets, physical ray paths or KL puzzle geometry.
 * Mathematical input: independently checked finite angle data; the landing
 * interpretation invokes the separately cited classical Zakeri theorem,
 * and the Levin correspondence invokes imported analytic results.
 */
import fs from 'node:fs';
function svgEsc(s){return String(s).replaceAll("&","&amp;").replaceAll("<","&lt;").replaceAll(">","&gt;").replaceAll('"',"&quot;");}
function fmt(n){return n.toFixed(2);}
function getP3Map(data){
 const pairs=data.nine_landing_pairs;
 if(pairs.length!==9 || pairs.map(p=>p.phase).join(",")!=="10,11,12,13,14,15,16,17,18") throw Error("Unexpected nine-cycle manifest");
 const allowed=pairs.filter(p=>p.phase%3===0).flatMap(p=>[Number(p.lower.split("/")[0]),Number(p.upper.split("/")[0])]).sort((a,b)=>a-b);
 if(allowed.join(",")!=="110,114,142,369,397,401") throw Error("Unexpected portrait P3 candidate angles");
 const desc=v=>v.reduce((a,x,i)=>a+(x>v[(i+1)%v.length]?1:0),0);
 const sols=[];
 for(let a=0;a<7;a++)for(let b=0;b<7;b++){
   const r=[a,b,4*b%7,2*a%7,4*a%7,2*b%7];
   if(desc(r)<=1) sols.push({a,b,r});
 }
 const nonzero=sols.filter(({a,b})=>a!==0 && b!==0);
 if(nonzero.length!==1 || nonzero[0].a!==4 || nonzero[0].b!==5 || nonzero[0].r.join(",")!=="4,5,6,1,2,3") throw Error("Unexpected Levin finite order data");
 return Object.fromEntries(allowed.map((n,i)=>[n,nonzero[0].r[i]]));
}
function renderPortrait(data){
 const p3=getP3Map(data);
 const pairs=data.nine_landing_pairs.map(x=>({...x,l:Number(x.lower.split("/")[0]),u:Number(x.upper.split("/")[0])}));
 const all=pairs.flatMap(p=>[p.l,p.u]);
 if(new Set(all).size!==18 || !all.every(n=>n>0 && n<511)) throw Error("Portrait point data unexpected");
 const selected={12:"#4fe0c1",15:"#f5b765",18:"#8daeff"};
 const position=n=>({x:300+182*Math.cos(2*Math.PI*n/511),y:337-182*Math.sin(2*Math.PI*n/511)});
 const s=[];
 s.push(`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1160 620" role="img" aria-labelledby="ttl desc">
<title id="ttl">Exact nine-pair external-angle portrait at the archive's nonattracting Misiurewicz tip</title>
<desc id="desc">Nine disjoint straight chords join 18 rational external ray angles with denominator 511 from the repository's period-nine portrait manifest. Chord endpoints use their exact angular positions. Three highlighted pairs at phases 12, 15 and 18 also participate in the later two-scale Levin correspondence. The chords are combinatorial pairings, not drawn dynamical rays. Landing uses an imported theorem of Zakeri; finite pairing and noncrossing arithmetic are checked in this archive.</desc>
<defs><linearGradient id="bg" x1="0" x2="1" y1="0" y2="1"><stop stop-color="#111e32"/><stop offset="1" stop-color="#08121f"/></linearGradient></defs>
<rect width="1160" height="620" rx="22" fill="url(#bg)"/>
<text x="40" y="47" font-size="14" font-family="Arial,sans-serif" letter-spacing="2.4" font-weight="700" fill="#58dcc2">A RESULT YOU CAN RECOMPUTE</text>
<text x="40" y="88" font-size="31" font-family="Arial,sans-serif" font-weight="700" fill="#f4f7fb">Nine pairs of external angles at a nonattracting tip</text>
<text x="40" y="117" font-size="17" font-family="Arial,sans-serif" fill="#acbed0">Actual exact-angle data, not a generic Mandelbrot illustration or a proof-completion score</text>
<rect x="30" y="140" width="555" height="417" rx="17" fill="#12243a" stroke="#2d425c"/>
<rect x="601" y="140" width="529" height="417" rx="17" fill="#12243a" stroke="#2d425c"/>
<circle cx="300" cy="337" r="182" fill="#0c1b2e" stroke="#627f9c" stroke-width="2"/>
<path d="M118 337H482 M300 155V519" stroke="#33475f" stroke-dasharray="4 7"/>
<text x="489" y="342" font-size="14" font-family="Arial,sans-serif" fill="#a8bfd4">0</text>
<text x="117" y="165" font-size="13" font-family="Arial,sans-serif" fill="#9bafc5">θ ↺</text>`);
 for(const p of pairs.filter(x=>!selected[x.phase]).concat(pairs.filter(x=>selected[x.phase]))){
   const a=position(p.l),b=position(p.u),c=selected[p.phase]||"#4f6884";
   const heavy=Boolean(selected[p.phase]); 
   s.push(`<line data-phase="${p.phase}" data-lower="${p.lower}" data-upper="${p.upper}" x1="${fmt(a.x)}" y1="${fmt(a.y)}" x2="${fmt(b.x)}" y2="${fmt(b.y)}" stroke="${c}" stroke-width="${heavy?4:2.2}" stroke-linecap="round" opacity="${heavy?1:0.78}"><title>phase x${p.phase}: ${p.lower} and ${p.upper}</title></line>`);
   for(const q of [a,b])s.push(`<circle cx="${fmt(q.x)}" cy="${fmt(q.y)}" r="${heavy?5:3.3}" fill="${c}" stroke="#10243a" stroke-width="1.5"/>`);
 }
 s.push(`<circle cx="300" cy="337" r="3" fill="#d4e2f3"/>
<text x="50" y="540" font-size="13" font-family="Arial,sans-serif" fill="#9db0c3">Angular position = 2π × (numerator / 511)</text>
<text x="631" y="185" font-family="Arial,sans-serif" font-size="18" font-weight="700" fill="#f4f7fb">Three highlighted landing-point pairs</text>
<text x="631" y="212" font-family="Arial,sans-serif" font-size="14" fill="#a7b9cd">The other six checked pairs appear in slate.</text>`);
 const cards=[
  {p:12,label:"PERIOD-3 PHASE  x₁₂",low:"110/511",up:"401/511",color:selected[12]},
  {p:15,label:"PERIOD-3 PHASE  x₁₅",low:"142/511",up:"369/511",color:selected[15]},
  {p:18,label:"COMMON 3/9 PHASE  x₁₈",low:"114/511",up:"397/511",color:selected[18]}
 ];
 for(let i=0;i<cards.length;i++){
   const q=cards[i],y=238+100*i;
   s.push(`<rect x="628" y="${y}" width="473" height="85" rx="13" fill="#1b3049"/>
<rect x="628" y="${y}" width="5" height="85" rx="2" fill="${q.color}"/>
<text x="653" y="${y+28}" font-family="Arial,sans-serif" letter-spacing="1.1" font-size="12" font-weight="700" fill="${q.color}">${svgEsc(q.label)}</text>
<text x="653" y="${y+61}" font-family="Arial,sans-serif" font-size="23" fill="#eff6ff">${q.low} <tspan fill="#859cb8">and</tspan> ${q.up}</text>`);
 }
 s.push(`<path d="M39 578H1122" stroke="#30445a"/>
<text x="40" y="602" font-family="Arial,sans-serif" font-size="13" fill="#b0c4d6">Exact chord pairing and noncrossing: archive verification code · Ray landing: imported Zakeri theorem</text>
</svg>`);
 return s.join("\n")+"\n";
}
function renderAngleMap(data){
 const p3=getP3Map(data), keys=Object.keys(p3).map(Number).sort((a,b)=>a-b);
 const pairs=data.nine_landing_pairs;
 const inner=pairs.filter(x=>x.phase%9===0).flatMap(x=>[Number(x.lower.split("/")[0]),Number(x.upper.split("/")[0])]).sort((a,b)=>a-b);
 if(inner.join(",")!=="114,397" || inner.some(a=>(512*a)%511!==a)) throw Error("Unexpected P9 ray fiber");
 const phaseFor=n=>pairs.find(p=>p.lower.startsWith(n+"/")||p.upper.startsWith(n+"/")).phase;
 const s=[];
 s.push(`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1160 585" role="img" aria-labelledby="ttl desc">
<title id="ttl">Distinct source-defined Levin ray-angle maps at periods three and nine</title>
<desc id="desc">Among the 18 known external rays in the repository's certified tip portrait, six are eligible for the period-three Levin map and have exact angle correspondence 110 to 4 sevenths, 114 to 5 sevenths, 142 to 6 sevenths, 369 to 1 seventh, 397 to 2 sevenths, and 401 to 3 sevenths. At period nine, the two eligible portrait angles, 114 and 397 divided by 511, both map to internal angle zero. These maps depend on imported classical analytic theorems and the archive's Carathéodory p2 argument, and no map between the internal circle codomains is claimed.</desc>
<defs>
 <linearGradient id="bg" x1="0" x2="1" y1="0" y2="1"><stop stop-color="#111e32"/><stop offset="1" stop-color="#08121f"/></linearGradient>
 <marker id="arr" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#7d9fba"/></marker>
 <marker id="arrGold" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#f5b765"/></marker>
</defs>
<rect width="1160" height="585" rx="22" fill="url(#bg)"/>
<text x="39" y="47" font-size="14" font-family="Arial,sans-serif" letter-spacing="2.3" font-weight="700" fill="#58dcc2">A TWO-SCALE DISTINCTION</text>
<text x="39" y="87" font-size="30" font-family="Arial,sans-serif" font-weight="700" fill="#f4f7fb">The same two rays behave differently at returns 3 and 9</text>
<text x="39" y="116" font-size="16" font-family="Arial,sans-serif" fill="#acbed0">Computed values of two genuine Levin correspondences on the known tip-ray subportrait</text>
<rect x="29" y="142" width="684" height="372" rx="16" fill="#12243a" stroke="#2d425c"/>
<rect x="728" y="142" width="402" height="372" rx="16" fill="#12243a" stroke="#2d425c"/>
<text x="53" y="177" font-size="19" font-family="Arial,sans-serif" font-weight="700" fill="#f4f7fb">Period 3 · Π₃</text>
<text x="53" y="202" font-size="13" font-family="Arial,sans-serif" fill="#a9bed2">Ambient θ</text>
<text x="505" y="202" font-size="13" font-family="Arial,sans-serif" fill="#a9bed2">Internal angle</text>`);
 for(let i=0;i<keys.length;i++){
   const n=keys[i],val=p3[n],y=224+i*43, focus=(n===114||n===397),accent=n===114?"#8daeff":n===397?"#f5b765":"#7c9aae";
   s.push(`<g data-ambient="${n}/511" data-period3="${val}/7" data-phase="${phaseFor(n)}">
<rect x="51" y="${y}" width="190" height="34" rx="9" fill="${focus?"#253d60":"#1b3049"}"/>
<text x="145" y="${y+24}" font-family="Arial,sans-serif" text-anchor="middle" font-size="19" font-weight="${focus?"700":"500"}" fill="${focus?accent:"#d4e2f1"}">${n}/511</text>
<path d="M257 ${y+17}H479" fill="none" stroke="${focus?accent:"#5c7996"}" stroke-width="${focus?2.4:1.7}" marker-end="url(#arr)"/>
<rect x="504" y="${y}" width="165" height="34" rx="9" fill="${focus?"#253d60":"#1b3049"}"/>
<text x="586" y="${y+24}" font-family="Arial,sans-serif" text-anchor="middle" font-size="19" font-weight="${focus?"700":"500"}" fill="${focus?accent:"#d4e2f1"}">${val}/7</text>
</g>`);
 }
 s.push(`<text x="754" y="178" font-size="19" font-family="Arial,sans-serif" font-weight="700" fill="#f4f7fb">Period 9 · Π₉</text>
<text x="754" y="202" font-size="13" font-family="Arial,sans-serif" fill="#a9bed2">Two eligible rays from x₁₈</text>
<g data-ambient="114/511" data-period9="0"><rect x="755" y="241" width="143" height="46" rx="11" fill="#253d60" stroke="#8daeff"/>
<text x="826" y="270" text-anchor="middle" font-size="19" font-family="Arial,sans-serif" fill="#a9c5ff">114/511</text></g>
<g data-ambient="397/511" data-period9="0"><rect x="755" y="355" width="143" height="46" rx="11" fill="#42392e" stroke="#f5b765"/>
<text x="826" y="384" text-anchor="middle" font-size="19" font-family="Arial,sans-serif" fill="#ffca82">397/511</text></g>
<path d="M899 264C935 264 941 309 971 309M899 378C935 378 941 309 971 309" fill="none" stroke="#f5b765" stroke-width="2.5" marker-end="url(#arrGold)"/>
<rect x="981" y="276" width="124" height="67" rx="14" fill="#285852" stroke="#61e0c2"/>
<text x="1043" y="321" text-anchor="middle" font-size="36" font-weight="700" font-family="Arial,sans-serif" fill="#e7fff6">0</text>
<text x="755" y="452" font-size="15" font-family="Arial,sans-serif" fill="#ccdded">A genuine two-to-one fiber</text>
<text x="755" y="474" font-size="13" font-family="Arial,sans-serif" fill="#91aabd">within the known portrait rays</text>
<path d="M39 540H1121" stroke="#30445a"/>
<text x="40" y="562" font-size="13" font-family="Arial,sans-serif" fill="#b0c4d6">Levin (p1)+(p2) use imported classical analysis; finite values are checked here. No all-ray classification or KL sheet map.</text>
</svg>`);
 return s.join("\n")+"\n";
}

const pathTo = (p) => new URL('../' + p, import.meta.url);
const data = JSON.parse(fs.readFileSync(pathTo('results/period27_tip_ray_portrait.json'), 'utf8'));
const expected = {
  'figs/readme/tip-ray-portrait.svg': renderPortrait(data),
  'figs/readme/two-scale-angle-map.svg': renderAngleMap(data)
};
const check = process.argv.includes('--check');
let failed = false;
for (const [path, content] of Object.entries(expected)) {
  if (check) {
    if (!fs.existsSync(pathTo(path)) || fs.readFileSync(pathTo(path), 'utf8') !== content) {
      console.error('OUTDATED: ' + path + ' (run node code/generate_readme_research_figures.mjs)');
      failed = true;
    } else {
      console.log('PASS ' + path);
    }
  } else {
    fs.writeFileSync(pathTo(path), content, 'utf8');
    console.log('generated ' + path);
  }
}
if (failed) process.exitCode = 1;
