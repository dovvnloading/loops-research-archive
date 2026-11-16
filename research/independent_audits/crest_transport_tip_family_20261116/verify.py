#!/usr/bin/env python3
"""Outward fixed-point certificate for selected physical-tip four-push collars.

Certified: rational root brackets and signs, all radius bins, real endpoint
itineraries, unique angular gates, typed finite atoms, rational width bounds.
Not certified by Python: prime ends, KKL path survival, conformal extremal width.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
S = 1 << 384
PARAMETER = {
 3: -11214108439445784980951565438958061530896939533591746653709,
 4: -12193610160972405830120367485459353629138957223175502573913,
 5: -12463362319716585005872989311512332060925612005103192709893,
 6: -12531496128803264686629812787093463121894480287952440515685,
 7: -12548529462359236409168186108132124778502513816111687694548,
 8: -12552785306501968995178380515935992615386967495660640540189,
}
# Slabs are strict subcollars of the actual p=3 Wave / chosen p>=4 Wave.
COLLARS = {
 3: (F(1,80), F(1,77)), # absolute, center=-9/64
 4: (F(63,1000), F(667,10000)),
 5: (F(313,5000), F(663,10000)),
 6: (F(1,16), F(663,10000)),
 7: (F(1,16), F(663,10000)),
 8: (F(1,16), F(663,10000)),
}
BLOCKS=[[18,19,0,1,2],[3,4],[5],[6],[7,8,9],[10],
        [11,12,13],[14],[15],[16,17]]

def check(c,reason):
    if not c: raise AssertionError(reason)
def ceildiv(a,b): return -((-a)//b)

@dataclass(frozen=True)
class I:
    lo:int
    hi:int
    def __post_init__(self): check(self.lo<=self.hi,'inverted interval')
    @staticmethod
    def point(v):
        t=F(v)*S
        return I(t.numerator//t.denominator,ceildiv(t.numerator,t.denominator))
    @staticmethod
    def hull(a,b):
        check(a<=b,'inverted rational enclosure')
        return I(I.point(a).lo,I.point(b).hi)
    def __add__(self,b): return I(self.lo+b.lo,self.hi+b.hi)
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,b): return self+-b
    def __mul__(self,b):
        v=(self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi)
        return I(min(v)//S,ceildiv(max(v),S))
    def square(self):
        bot=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
        return I(bot//S,ceildiv(max(self.lo*self.lo,self.hi*self.hi),S))
    def lt(self,b): return self.hi<b.lo
    def meet(self,b): return self.lo<=b.hi and b.lo<=self.hi
    def positive(self): return self.lo>0
    def abs_bound(self): return F(max(abs(self.lo),abs(self.hi)),S)
    def mid(self): return F(self.lo+self.hi,2*S)
    def low(self): return F(self.lo,S)
    def high(self): return F(self.hi,S)

Z,O,T=I.point(0),I.point(1),I.point(2)

def iterate(z,c,p):
    for _ in range(p): z=z.square()+c
    return z

def orbit(c,n,derivative=False):
    x=[Z]; ds=[Z]
    for k in range(n):
        if derivative: ds.append(T*x[-1]*ds[-1]+O)
        x.append(x[-1].square()+c)
    return x,ds

def parameter(p):
    n=PARAMETER[p]; a=F(n,2**192); b=F(n+1,2**192)
    lo,_=orbit(I.point(a),6*p);hi,_=orbit(I.point(b),6*p)
    check((lo[6*p]+lo[3*p]).positive() and (hi[6*p]+hi[3*p]).hi<0,'parameter signs')
    c=I.hull(a,b);x,dx=orbit(c,6*p,True)
    check((dx[6*p]+dx[3*p]).hi<0,'parameter monotonicity')
    check((x[6*p]+x[3*p]).meet(Z),'parameter relation')
    check(x[p].positive(),'nonpositive critical return')
    return c,x

def alpha_root(c,p,x):
    a=x[6*p].high();b=x[4*p].low()
    check(a<b and (iterate(I.point(a),c,p)-I.point(a)).positive() and
          (iterate(I.point(b),c,p)-I.point(b)).hi<0,'alpha bracket signs')
    for _ in range(130):
        m=(a+b)/2;f=iterate(I.point(m),c,p)-I.point(m)
        if f.positive():a=m
        elif f.hi<0:b=m
        else:break
    return I.hull(a,b)

def re_im(zx,y2,c,p):
    """Re f^p(x+iy), Im f^p(x+iy)/y with y^2=y2 (no square roots)."""
    v,h=zx,O
    for _ in range(p):
        nxt=v.square()-y2*h.square()+c
        h=T*v*h
        v=nxt
    return v,h

def real_on_arc(d,r,u,c,p):
    x=d+r*u
    y2=r.square()*(O-u.square())
    return re_im(x,y2,c,p)

def polynomial_coefficients(d,r,c,p):
    """Exact interval Taylor coefficients of f^p(d+r*w), for |w|<=1."""
    v=[d,r]
    for _ in range(p):
        out=[Z]*(2*len(v)-1)
        for j,a in enumerate(v):
            for k,b in enumerate(v):out[j+k]=out[j+k]+a*b
        out[0]=out[0]+c
        v=out
    return v

def monotonicity(d,maxr,c,p):
    coeff=polynomial_coefficients(d,maxr,c,p)
    err=sum(coeff[k].abs_bound()*k*k for k in range(2,len(coeff)))
    check(coeff[1].low()>err,'Taylor angular derivative not dominant')
    # Also Im(G(z))/Im(z) is positive for all 0<r<=maxr.
    return coeff[1].low()-err

def gate(d,r,c,p):
    """Strict across a full radius bin; unique u in [-1/8,1/4]."""
    low,high=F(-1,8),F(1,4)
    check(real_on_arc(d,r,I.point(low),c,p)[0].hi<0,'gate left sign')
    check(real_on_arc(d,r,I.point(high),c,p)[0].lo>0,'gate right sign')
    for _ in range(44):
        mid=(low+high)/2
        z=real_on_arc(d,r,I.point(mid),c,p)[0]
        if z.hi<0:low=mid
        elif z.lo>0:high=mid
        else:break
    return I.hull(low,high)

def log_interval(q,n=18):
    """Exact rational lower/upper for log(q)>0 using atanh and a tail bound."""
    check(q>1,'nonpositive logarithm')
    z=(q-1)/(q+1)
    low=2*sum((z**(2*k+1))/F(2*k+1) for k in range(n))
    tail=2*z**(2*n+1)/((2*n+1)*(1-z*z))
    return low,low+tail

def atan_interval(q,n=12):
    term=lambda k:((-1)**k)*q**(2*k+1)/F(2*k+1)
    sm=sum((term(k) for k in range(n)),F(0))
    return (sm,sm+term(n)) if n%2==0 else (sm+term(n),sm)

def pi_bounds():
    # Machin identity pi/4=4 atan(1/5)-atan(1/239), alternating bounds.
    a0,a1=atan_interval(F(1,5));b0,b1=atan_interval(F(1,239))
    lo,hi=4*(4*a0-b1),4*(4*a1-b0)
    check(lo<hi and F(333,106)<lo and hi<F(355,113),'rational pi enclosure invalid')
    return F(333,106),F(355,113)

def index_of(y,side,cuts):
    n=len(cuts)
    if y.lt(cuts[0]): return 0
    if cuts[-1].lt(y): return n
    for j in range(1,n):
        if cuts[j-1].lt(y) and y.lt(cuts[j]):
            return j if side==1 else 2*n-j
    raise AssertionError('point on a marking cut')

def sample_atom(s,cuts,left,right):
    n=len(cuts)
    if s==0:aa,bb,side=left,cuts[0],1
    elif s==n:aa,bb,side=cuts[-1],right,1
    else:
        j,side=(s,1) if s<n else (2*n-s,-1)
        aa,bb=cuts[j-1],cuts[j]
    check(aa.lt(bb),'source atom empty')
    return I.point((2*aa.mid()+bb.mid())/3),side

def actions_from_physical_cuts(c,p,x,alpha):
    target=[x[5*p],x[3*p],x[6*p],alpha,x[4*p]]
    cuts=[-x[4*p],x[2*p],x[5*p],-alpha,x[3*p],x[6*p],
          alpha,-x[5*p],-x[2*p],x[4*p]]
    check(all(a.lt(b) for a,b in zip(cuts,cuts[1:])), 'ordered source cuts')
    covering=[];immersion=[]
    for s in range(20):
        z,side=sample_atom(s,cuts,-x[p],x[p])
        img=iterate(z,c,p)
        covering.append(index_of(img,side if z.high()<0 else -side,target))
        immersion.append(0 if z.lt(x[2*p]) else index_of(z,side,target))
    blocks=[]
    for t in range(10):
        starts=[s for s in range(20) if immersion[s]==t and immersion[(s-1)%20]!=t]
        check(len(starts)==1,'disconnected iota* block')
        j=starts[0];block=[]
        while immersion[j]==t:
            check(len(block)<20,'immersion block loop')
            block.append(j);j=(j+1)%20
        blocks.append(block)
    check(covering==[s%10 for s in range(20)],'cover G* map changed')
    check(blocks==BLOCKS,'iota* partition changed')
    check([s for s in range(20) if immersion[s]==0 and
           sample_atom(s,cuts,-x[p],x[p])[0].lt(x[2*p])]==[0,1,19],
          'three attached sides changed')
    return covering,blocks

def round_down(q):
    return F((q.numerator*S)//q.denominator,S)
def round_up(q):
    return F(ceildiv(q.numerator*S,q.denominator),S)

def disk_four(c,p,d,maxr,target,xp):
    """Whole closed disk, rounded every f step on the fixed 2^-384 grid."""
    c0,cr=c.mid(),(c.high()-c.low())/2
    ctr=round_down(d.mid())
    rad=round_up(maxr.high()+d.high()-ctr)
    check(abs(ctr)+rad<target,'original disk not in U')
    check((-xp).high()<ctr<xp.low(),'original center not in central component selector')
    rows=[]
    for k in range(1,4*p+1):
        newc=ctr*ctr+c0
        rounded=round_down(newc)
        rad=round_up(2*abs(ctr)*rad+rad*rad+cr+(newc-rounded))
        ctr=rounded
        if k%p==0:
            check(abs(ctr)+rad<target,f'full disk exits U at push {k//p}')
            if k//p<=3:
                check((-xp).high()<ctr<xp.low(),'disk center left real central selector')
            if k//p==2:check(ctr>rad,'second support is not on positive half-plane')
            if k//p==3:check(ctr+rad<0,'third support is not on negative half-plane')
            rows.append(k//p)
    return rows

def run(p,nbins=512):
    check(nbins>=64,'too few whole bins')
    c,x=parameter(p)
    xp=x[p];alpha=alpha_root(c,p,x)
    order=[x[2*p],x[5*p],x[3*p],Z,x[6*p],alpha,x[4*p],xp]
    check(all(a.lt(b) for a,b in zip(order,order[1:])), 'target tree orbit cut order')
    source=[-xp,-x[4*p],x[2*p],x[5*p],-alpha,x[3*p],x[6*p],alpha,
            -x[5*p],-x[2*p],x[4*p],xp]
    check(all(a.lt(b) for a,b in zip(source,source[1:])),'source cut order')
    cover,blocks=actions_from_physical_cuts(c,p,x,alpha)
    source_cuts=source[1:-1]
    host={atom:parent for parent,block in enumerate(blocks) for atom in block}
    # Four successive *typed* proper restrictions, before applying G_*.
    # Intermediate arrays are source accesses; only the indicated last
    # q-side paths survive the third-step w-endpoint cut crossing.
    stage_pairs=( ((3,1),(19,17)), ((6,4),(16,14)),
                  ((9,11),), ((0,3),(17,0)) )
    for pairs in stage_pairs:
        for left,right in pairs:
            check(host[left]!=host[right],'proper iota* hosts coincident')
            check(1+min((right-left)%20,(left-right)%20)>2,
                  'source short-path KKL deletion')
            a0,b0=cover[left],cover[right]
            check(1+min((b0-a0)%10,(a0-b0)%10)>2,
                  'cover-pushed target short-path deletion')
    a,b=COLLARS[p]
    if p==3:
        d=I.point(F(-9,64));ra,rb=I.point(a),I.point(b)
        parent=F(4,3)
        check(ra.low()>F(3,256) and rb.high()<F(1,64),'p3 original collar containment')
    else:
        d=I.point(F(-3,4))*xp
        ra,rb=I.point(a)*xp,I.point(b)*xp
        parent=F(2*(p-1),p)
        check(a>F(1,16) or a==F(1,16),'radius below original')
        check(b<F(p-1,8*p),'radius above original')
    target=F(1,4) if p==3 else F(1,2**p)
    disk=disk_four(c,p,d,rb,target,xp)
    monot=monotonicity(d,rb,c,p)
    pi_lo,pi_hi=pi_bounds()
    theta_bound=pi_hi/2
    logsum=F(0); logsum_upper=F(0); u_min=F(1);u_max=F(-1)
    for j in range(nbins):
        l=a+(b-a)*j/nbins; h=a+(b-a)*(j+1)/nbins
        r=I.hull(l,h) if p==3 else I.hull(l,h)*xp
        u=gate(d,r,c,p)
        u_min=min(u_min,u.low());u_max=max(u_max,u.high())
        re,factor=real_on_arc(d,r,u,c,p)
        check(factor.positive(),'imaginary-axis crossing lost upper sign')
        y2=r.square()*(O-u.square())*factor.square()
        check(y2.positive(),'imaginary crossing height vanished')
        # G(i*sqrt(y2)) is exactly real, by evenness of the first f step.
        r2=iterate(c-y2,c,p-1)
        r3=iterate(r2,c,p)
        r4=iterate(r3,c,p)
        check(xp.lt(r2) and r2.lt(I.point(target)),'second meeting not outside T prime tip')
        check((-xp).lt(r3) and r3.lt(-x[4*p]),f'terminal S0 gate fails p={p}, bin={j}')
        check(x[2*p].lt(r4) and r4.lt(x[5*p]),'fourth image outside K2')
        q,w=d+r,d-r
        check(x[5*p].lt(q) and q.lt(-alpha),'initial q access changed')
        check((-x[4*p]).lt(w) and w.lt(x[2*p]),'initial w access changed')
        check((index_of(q,1,source_cuts),index_of(w,1,source_cuts),
               index_of(w,-1,source_cuts),index_of(q,-1,source_cuts))==
              (3,1,19,17),'step 0 source accesses changed')
        for k in range(1,5):
            q,w=iterate(q,c,p),iterate(w,c,p)
            if k==1:
                check(x[6*p].lt(q) and q.lt(alpha) and (-alpha).lt(w) and w.lt(x[3*p]),'first push endpoint gates')
                check((index_of(q,1,source_cuts),index_of(w,1,source_cuts),
                       index_of(w,-1,source_cuts),index_of(q,-1,source_cuts))==
                      (6,4,16,14),'step 1 source accesses changed')
            if k==2:
                check((-x[2*p]).lt(q) and q.lt(x[4*p]) and (-x[2*p]).lt(w) and w.lt(x[4*p]),'second push endpoint gates')
                check((index_of(q,1,source_cuts),index_of(w,1,source_cuts),
                       index_of(w,-1,source_cuts),index_of(q,-1,source_cuts))==
                      (9,9,11,11),'step 2 source accesses changed')
            if k==3:
                check(x[5*p].lt(q) and q.lt(-alpha) and x[5*p].lt(w) and w.lt(x[3*p]),'third push q-side gates')
                # The other w-side can cross -alpha, so DO NOT assign it a
                # globally fixed source atom at this stage.
                check((index_of(q,1,source_cuts),index_of(q,-1,source_cuts))==
                      (3,17),'step 3 selected q-side changed')
                check(index_of(r3,1,source_cuts)==0,
                      'step 3 terminal real gate lost source S0')
            if k==4:
                check(x[6*p].lt(q) and q.lt(alpha),'fourth push q access')
        ulo=u.low()
        check(ulo>=F(-1,8) and u.high()<=F(1,8),'angular enclosure exceeds arcsin bound')
        if ulo>=0:
            theta=theta_bound-ulo  # asin(u)>=u
        else:
            theta=theta_bound-F(65,64)*ulo # |asin(u)|<= (65/64)|u| on [-1/8,0]
        check(theta>0,'invalid upper angular bound')
        if u.high()<=0:
            theta_lower=pi_lo/2-u.high()
        else:
            theta_lower=pi_lo/2-F(65,64)*u.high()
        check(theta_lower>0,'negative lower height')
        loglow,loghigh=log_interval(h/l,6)
        logsum+=loglow/theta
        logsum_upper+=loghigh/theta_lower
    parent_low,parent_high=log_interval(parent)
    ratio=2*pi_lo*logsum/parent_high
    ratio_upper=2*pi_hi*logsum_upper/parent_low
    # Largest certified multiple of 1/10000 for the declared bin method.
    c4=(ratio.numerator*10000)//ratio.denominator
    c4_up=ceildiv(ratio_upper.numerator*10000,ratio_upper.denominator)
    check(0<c4<c4_up,'bad ratio bounds')
    host={s:i for i,blk in enumerate(blocks) for s in blk}
    check(len(host)==20 and (host[0],host[3],host[17])==(0,1,9),'iota blocks')
    check((cover[0],cover[3],cover[17])==(0,3,7),'cover labels')
    check(all(1+min((v-u)%n,(u-v)%n)>2 for u,v,n in [(0,3,20),(17,0,20),(0,3,10)]),'KKL short deletion')
    # Reconstruct old-edge carriers *from real coordinates*, not just
    # from a predeclared I1/I9 label: slit sides of the same real edge
    # count as one edge, while K0/K1/K2 atoms remain zero-edge.
    target_cuts=[x[5*p],x[3*p],x[6*p],alpha,x[4*p]]
    edges=[(x[5*p],x[3*p]),(x[6*p],alpha),(alpha,x[4*p])]
    incidence={}
    for i in range(10):
        point,side=sample_atom(i,target_cuts,x[2*p],xp)
        incidence[i]=[j for j,(lo,hi) in enumerate(edges) if lo.lt(point) and point.lt(hi)]
    check([i for i in range(10) if incidence[i]]==[1,3,4,6,7,9],
          'physical target old-edge incidence drift')
    check(incidence[1]==[0] and incidence[9]==[0],
          'two closed crests do not share one genuine E0 edge')
    check(sample_atom(1,target_cuts,x[2*p],xp)[1]==1 and
          sample_atom(9,target_cuts,x[2*p],xp)[1]==-1,
          'the E0 sides are not opposite prime-end accesses')
    # The selected terminal source endpoints belong to distinct iota*
    # hosts, survive the short-span deletion, then *cover* to I0/I3/I7.
    return {
      'p':p,'parameter_bracket_2pow192':[PARAMETER[p],PARAMETER[p]+1],
      'parent_wave':{'center':'-9/64' if p==3 else '-3*x_p/4',
        'radius':'(3/256,1/64)' if p==3 else '(x_p/16,(p-1)*x_p/(8*p))',
        'width':'log('+str(parent)+')/(2*pi)'},
      'collar':{'radius':'('+str(a)+','+str(b)+')' if p==3 else 'x_p*('+str(a)+','+str(b)+')',
         'whole_bins':nbins,'u_min_lower':str(u_min),'u_max_upper':str(u_max)},
      'first_image_angular_derivative_margin_positive':True,
      'full_disk_images_in_target':True,
      'old_edge_crest_descendants':['upper q side: S0->S3, crest closure I1,I2 (I1=E0 upper)',
                                    'lower q side: S17->S0, crest closure I8,I9 (I9=E0 lower)'],
      'certified_ratio_lower':f'{c4}/10000',
      'certified_ratio_upper':f'{c4_up}/10000',
      'lower_bound_is_for_declared_collar_only':True,
      'width_formula':'(2*pi/log(parent ratio))*integral_collar dr/(r*acos(u_p(r)))',
      'analytic_status':'conditional on prime-end KKL proper restriction, univalence and exact strip width',
    }

def main():
    pa=argparse.ArgumentParser(description=__doc__)
    pa.add_argument('--write',action='store_true')
    pa.add_argument('--bins',type=int,default=512)
    args=pa.parse_args()
    o={'schema':'crest-tip-family-binned-v1',
       'finite_scope':'p=3..8, full radius bins, outward fixed point 2^-384',
       'uniform_all_p':'open under PR80 hypotheses',
       'covering_G_star':'S_s -> I_(s mod 10)',
       'immersion_iota_star_blocks':BLOCKS,
       'results':[run(p,args.bins) for p in range(3,9)]}
    payload=json.dumps(o,sort_keys=True,indent=2)+'\n'
    result=HERE/'results.json'
    if args.write:result.write_text(payload);print('wrote',result)
    else:
        check(result.read_text()==payload,'locked results drift')
        print('PASS 6 periods: all radius bins, typed four-push gate, rational width lower bounds')
        for r in o['results']:print('p',r['p'],'ratio in [',r['certified_ratio_lower'],r['certified_ratio_upper'],']')


if __name__=="__main__": main()
