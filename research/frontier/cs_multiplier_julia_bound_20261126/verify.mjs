// Exact rational regression; not a proof of a dynamical realization.
import { readFileSync } from "node:fs";
function verify(data) {
  const assert=(v,msg)=>{if(!v)throw Error(msg)};
  const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b){const t=a%b;a=b;b=t}return a};
  const R=(a,b=1n)=>{a=BigInt(a);b=BigInt(b);assert(b!==0n,"zero denominator");if(b<0n){a=-a;b=-b}const g=gcd(a,b);return [a/g,b/g]};
  const add=(a,b)=>R(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
  const neg=a=>R(-a[0],a[1]); const sub=(a,b)=>add(a,neg(b));
  const mul=(a,b)=>R(a[0]*b[0],a[1]*b[1]);
  const div=(a,b)=>R(a[0]*b[1],a[1]*b[0]);
  const sq=a=>mul(a,a);const le=(a,b)=>a[0]*b[1]<=b[0]*a[1];const eq=(a,b)=>le(a,b)&&le(b,a);
  const zero=R(0),one=R(1),two=R(2);
  const abs2=(x,y)=>add(sq(x),sq(y));
  const decimal=s=>{const [a,b=""]=s.split(".");return R(BigInt(a+b),10n**BigInt(b.length))};
  const show=a=>`${a[0]}/${a[1]}`;
  const P=(x,y)=>div(sub(one,abs2(x,y)),abs2(sub(one,x),y));
  const A=(x,y)=>div(one,P(x,y));
  const normOK=(v,d)=>{ // v in [sqrt(1+d^2)-d,sqrt(1+d^2)+d]
    const lower=add(v,d),upper=sub(v,d),ds=add(one,sq(d));
    return le(ds,sq(lower))&&(le(upper,zero)||le(sq(upper),ds));
  };
  let diskChecks=0, thresholdChecks=0, witnesses=0;
  for(const q of [3,4,9,50,100]) {
    const n=R(q*q*q),a=div(R(q),n),q2=R(q*q);
    for(const m of [7,13])for(let i=-m;i<=m;i++)for(let j=-m;j<=m;j++){
      const x=R(i,m),y=R(j,m); if(le(one,abs2(x,y)))continue;
      const re=add(a,mul(div(q2,two),P(x,y)));
      const im=add(div(mul(q2,y),abs2(sub(one,x),y)),R(7,3));
      const s=abs2(re,im),hx=div(re,s),hy=div(neg(im),s),h2=abs2(hx,hy);
      assert(le(mul(add(a,mul(div(q2,two),P(x,y))),h2),hx),"shifted Julia disk");
      assert(eq(div(h2,hx),div(one,re)),"inversion identity");
      assert(le(div(h2,hx),div(n,R(q))),"stronger than PLY");
      const d=div(A(x,y),R(6*q)); // pi > 3
      if(le(d,R(19,180))){
        assert(le(add(sq(R(9,10)),mul(R(9,5),d)),one),"lower norm cutoff");
        assert(le(one,sub(sq(R(6,5)),mul(R(12,5),d))),"upper norm cutoff");
        assert(le(mul(two,sq(d)),sq(sub(one,d))),"sector cutoff");
        thresholdChecks++;
      }
      // Re(h/(T+h)) >= 1/2 whenever |h| >= T.
      for(const T of [R(1,10),R(1,100),R(1,1000)])if(le(sq(T),h2)){
        const u=div(add(mul(T,hx),h2),abs2(add(T,hx),hy));
        assert(le(R(1,2),u),"bad-set harmonic majorant");
      }
      diskChecks++;
    }
    for(const [x,y] of [[R(0),R(1)],[R(3,5),R(4,5)],[R(99,101),R(20,101)]]){
      assert(eq(abs2(x,y),one),"boundary test point");
      const b=neg(div(mul(q2,y),abs2(sub(one,x),y)));
      const re=add(a,mul(div(q2,two),P(x,y)));
      const im=add(div(mul(q2,y),abs2(sub(one,x),y)),b);
      assert(eq(im,zero)&&eq(div(one,re),div(n,R(q))),"boundary peak exact");
      witnesses++;
    }
  }
  const chart=[["root",null],["center",[zero,zero]],["minus",[R(-95,100),zero]],["plusI",[zero,R(95,100)]],["minusI",[zero,R(-95,100)]],["plus",[R(99,100),zero]]];
  assert(data.own_primary_order.join(",")===chart.map(a=>a[0]).join(","),"sample columns");
  const rows=[];let numericalChecks=0;
  for(const row of data.levels){
    const q=row[data.columns.indexOf("q")],vals=row[data.columns.indexOf("own_primary")];
    for(let i=1;i<chart.length;i++){
      const d=div(A(...chart[i][1]),R(6*q));
      const v=decimal(vals[i]); // printed decimal, with +/- 1e-12 allowance
      const tol=R(1,10n**12n);
      // The interval intersects the enlarged theoretical annular bound.
      assert(le(sq(sub(add(v,tol),neg(d))),add(one,sq(d)))===false||normOK(add(v,tol),d)||eq(sq(add(add(v,tol),d)),add(one,sq(d))),"lower comparison");
      const low=sub(v,tol),high=add(v,tol);
      assert(le(add(one,sq(d)),sq(add(high,d))),"observed interval not wholly below bound");
      const u=sub(low,d);
      assert(le(u,zero)||le(sq(u),add(one,sq(d))),"observed interval not wholly above bound");
      numericalChecks++;
    }
    rows.push({q,guaranteed_centered_chart_radius:show(R(19*q-30,19*q+30)),center_scaled_norm:vals[1]});
  }
  return {diskChecks,thresholdChecks,witnesses,numericalChecks,rows};
}
const data = JSON.parse(readFileSync(new URL("../cs_multiplier_locus_extended_20261126/results.json", import.meta.url), "utf8"));
console.log(JSON.stringify(verify(data),null,2));
