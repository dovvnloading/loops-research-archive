#!/usr/bin/env python3
"""Exact rational certificate for the 27 depth-three words in {3,4,5}^3.

Search output is never trusted: endpoint separation, uniform derivative,
kneading, complete disk remainders, nesting, cuts, gates and envelopes are
recomputed with integer/Fraction arithmetic. The Lean declarations are the
proof deliverable; this checker independently reproduces their input data.
"""
from __future__ import annotations
import importlib.util
import itertools
import json
from pathlib import Path
import sys
from fractions import Fraction as Q
from math import isqrt

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec)
    sys.modules[name]=mod
    spec.loader.exec_module(mod)
    return mod

D3=load('depth3_exact_source',ROOT/'research/independent_audits/tip_family_all_depths_20261116/verify.py')
D2=load('depth2_exact_source',ROOT/'research/independent_audits/tip_family_renormalization_depth_20261116/verify.py')
I,S,check=D3.Interval,D3.S,D3.check

def rational_pair(q):
    q=Q(q)
    return [q.numerator,q.denominator]

def parse_ratio(q):
    check(isinstance(q,list) and len(q)==2 and all(isinstance(v,int) for v in q) and q[1]>0,
          'invalid rational denominator or encoding')
    return Q(*q)

def bounds(seed, radius=Q(1,10**80)):
    q=Q(seed)
    return I.hull(q-radius,q+radius)

def make_row(search):
    p,q,r=search['word'];n=p*q*r
    c=bounds(search['seed'])
    x,d,a=D3.iterate(c,6*n)
    nearest=D3.floor(Q(a[n].abslo()+a[n].abshi(),2*S)+Q(1,2))
    R1=Q(1,4) if p==3 else Q(1,2**p)
    R2=Q(1,10*4**(p-3)*(4 if q==3 else 2**q))
    alpha=bounds(search['alpha'],Q(1,10**30))
    ref2=bounds(D2.SEEDS[q,r],Q(1,10**75))
    ref1=bounds(D2.REFERENCE_TIPS[r],Q(1,10**75))
    row={'word':[p,q,r], 'parameter':[c.lo,c.hi],
      'radii':[rational_pair(R1),rational_pair(R2),[0,1]],
      'alpha':[alpha.lo,alpha.hi],
      'reference2':[ref2.lo,ref2.hi], 'reference1':[ref1.lo,ref1.hi]}
    reasons=[]
    # Choose explicit rational radius witnesses; every candidate is checked
    # from its complete complex-disk remainder, never a sampled circle.
    for k in range(125,161):
        row['radii'][2]=rational_pair(Q(k,40*nearest))
        try:
            result=verify_row(row)
            row['width']=make_width_witness(row)
            check_width_witness(row)
            return row,result
        except AssertionError as e:
            reasons.append((k,str(e)))
    raise AssertionError(f'no radius for {p,q,r}: {reasons}')

def verify_row(row):
    p,q,r=row['word'];n1,n2,n3=p,p*q,p*q*r
    check(p in (3,4,5) and q in (3,4,5) and r in (3,4,5),'word outside grid')
    expected2=bounds(D2.SEEDS[q,r],Q(1,10**75))
    expected1=bounds(D2.REFERENCE_TIPS[r],Q(1,10**75))
    check(row['reference2']==[expected2.lo,expected2.hi],'depth-two reference identity')
    check(row['reference1']==[expected1.lo,expected1.hi],'depth-one reference identity')
    c=I(*row['parameter']);al=I(*row['alpha'])
    periods=(n1,n2,n3)
    radii=tuple(map(parse_ratio,row['radii']))
    check(c.lo<c.hi and al.lo<al.hi and all(R>0 for R in radii),'invalid chart')
    x,d,a=D3.iterate(c,6*n3)
    derivative=d[3*n3]+d[6*n3]
    check(derivative.lo>0 or derivative.hi<0,'nonmonotone root chart')
    xl,_,_=D3.iterate(I(c.lo,c.lo),6*n3)
    xr,_,_=D3.iterate(I(c.hi,c.hi),6*n3)
    pl,pr=xl[3*n3]+xl[6*n3],xr[3*n3]+xr[6*n3]
    check((pl.hi<0 and pr.lo>0) or (pl.lo>0 and pr.hi<0),'endpoint root signs')
    check(x[1].hi<0 and all(x[j].lo>0 for j in range(2,p+1)),'outer primitive prefix')
    check(a[n1].hi<0 and a[n2].lo>0 and a[n3].hi<0,'quadratic orientations')
    check((a[n3]*x[3*n3]).lo>0 and (a[n3]*x[6*n3]).hi<0,'terminal tip branch')
    for m,ref,steps in ((n1,row['reference2'],6*q*r),(n2,row['reference1'],6*r)):
        reference,_,_=D3.iterate(I(*ref),steps)
        for j in range(1,steps+1):
            actual=a[m]*x[j*m];wanted=reference[j]
            check((actual.lo>0 and wanted.lo>0) or (actual.hi<0 and wanted.hi<0),
                  f'kneading mismatch {m} {j}')
    gaps=[]
    for n,R in zip(periods,radii):
        check(D3.scaled(x[n].abshi())<R,f'return critical value {n}')
        gap=D3.gap(x,a,n,R);gaps.append(gap)
        check(gap>0,f'Rouche disk {n}')
    for indices,R in ((list(range(p)),radii[0]),
                      ([j*n1 for j in range(q)],radii[1]),
                      ([j*n2 for j in range(r)],radii[2])):
        D3.disjoint_phases(x,a,indices,R)
    for parent,child,m,repeats in ((0,1,n1,q),(1,2,n2,r)):
        R,rr=radii[parent],radii[child]
        t=D3.errors(x,a,rr,m*(repeats-1))
        rr2=I.point(rr*rr).hi
        for j in range(repeats):
            i=j*m
            delta=I.point(rr).hi if i==0 else D3.upper_product(a[i].abshi(),rr2)+t[i]
            after=D3.upper_disk_image(x,i,m,delta)
            check(D3.scaled(x[i+m].abshi()+after)<R,f'child containment parent {m} phase {j}')
        D3.real_connector(x,c,m,R,6*n3//m)
    y=[I.point(0)]+[-(a[n3]*x[j*n3]) for j in range(1,7)]
    check(D3.fixed_residual(c,a[n3],D3.scaled(al.lo),n3).lo>0 and
          D3.fixed_residual(c,a[n3],D3.scaled(al.hi),n3).hi<0,'fixed-point bracket')
    z=I.point(0)
    o1=[y[2],y[5],y[3],z,y[6],al,y[4],y[1]]
    o2=[-y[1],-y[4],y[2],y[5],-al,y[3],y[6],al,-y[5],-y[2],y[4],y[1]]
    check(all(u.lt(v) for u,v in zip(o1,o1[1:])),'O1 cuts')
    check(all(u.lt(v) for u,v in zip(o2,o2[1:])),'O2 cuts')
    A=a[n3]
    nearest=D3.floor(Q(A.abslo()+A.abshi(),2*S)+Q(1,2))
    check(nearest>0 and D3.scaled(A.abslo())>nearest-Q(1,2) and
          D3.scaled(A.abshi())<nearest+Q(1,2),'A rounding')
    r4=Q(3,10*nearest)
    gap4=D3.gap(x,a,3*n3,r4)
    normalized=D3.scaled(A.abslo())*gap4
    check(normalized>Q(1,8),'terminal normalized gap')
    check(r4<radii[2] and D3.scaled(x[3*n3].abshi())<r4,'terminal disk embedded')
    D3.disjoint_phases(x,a,[0,n3,2*n3],r4)
    t4=D3.errors(x,a,r4,3*n3);r4sq=I.point(r4*r4).hi
    for j in (1,2,3):
        dev=D3.upper_product(a[j*n3].abshi(),r4sq)+t4[j*n3]
        check(D3.scaled(x[j*n3].abshi()+dev)<radii[2],'terminal phases contained')
    D3.real_connector(x,c,n3,radii[2],6)
    half=I.point(Q(1,2))
    center=(y[2]+y[5])*half
    inner=(y[5]-y[2])*half
    gplus=-al-center;gminus=y[4]+center
    check(gplus.lt(gminus) and inner.lt(gplus),'nonempty radial gate')
    inv=I.hull(1/D3.scaled(A.hi),1/D3.scaled(A.lo))
    zcenter=-center*inv
    dr=D3.ceil(D3.scaled(gplus.abshi())/D3.scaled(A.abslo())*S)
    dev=dr;zz=zcenter
    for _ in range(n3):
        dev=D3.upper_product(2*zz.abshi(),dev)+D3.upper_product(dev,dev)
        zz=zz.square()+c
    check(D3.scaled(zz.abshi()+dev)<radii[2],'whole radial gate containment')
    check(zcenter.abshi()<x[n3].abslo(),'radial gate real connector')
    ratio=D3.scaled(gplus.lo)/D3.scaled(inner.hi)
    v=(ratio-1)/(ratio+1)
    check(v>0,'positive logarithm argument')
    log_lower=2*sum(v**(2*j+1)/Q(2*j+1) for j in range(16))
    radial=log_lower/Q(44,7)
    check(radial>Q(1,4),'radial lower width')
    plane_lo,plane_hi=D3.plane_sandwich_upper(y)
    check(plane_hi<Q(31,40),'plane upper width')
    check(radial<plane_lo,'width envelopes inconsistent')
    D3.check_marked_tables()
    return {'gaps':gaps,'normalized_terminal':normalized,'radial_lower':radial,'plane_upper':plane_hi}

def width_inputs(row):
    p,q,r=row['word'];n=p*q*r
    x,_,a=D3.iterate(I(*row['parameter']),6*n)
    y=[I.point(0)]+[-(a[n]*x[j*n]) for j in range(1,7)]
    half=I.point(Q(1,2))
    mid=(y[2]+y[1])*half;rad=(y[1]-y[2])*half
    args=[(mid-y[5])/rad,(mid-y[3])/rad]
    center=(y[2]+y[5])*half;inner=(y[5]-y[2])*half
    gate=-I(*row['alpha'])-center
    v=Q(gate.lo-inner.hi,gate.lo+inner.hi)
    return args,v


def sqrt_witness(t):
    check(t>=0,'negative sqrt witness')
    scale=10**12
    k=isqrt((t.numerator*scale*scale)//t.denominator)
    return Q(k,scale),Q(k+1,scale)


def make_agm_witness(t):
    alo=ahi=Q(1);blo=bhi=t;steps=[]
    for _ in range(10):
        low=sqrt_witness(alo*blo)[0]
        high=sqrt_witness(ahi*bhi)[1]
        steps.append([rational_pair(low),rational_pair(high)])
        alo,ahi,blo,bhi=(alo+blo)/2,(ahi+bhi)/2,low,high
    return steps


def make_width_witness(row):
    args,v=width_inputs(row)
    angles=[]
    for arg in args:
        lo,hi=D3.acos_bounds(arg)
        lo=Q(D3.floor(lo*10**8),10**8)
        hi=Q(D3.ceil(hi*10**8),10**8)
        angles.append([rational_pair(lo),rational_pair(hi)])
    (al,ah),(bl,bh)=[list(map(parse_ratio,pair)) for pair in angles]
    kl=(bl-ah)/(bl+ah);kh=(bh-al)/(bh+al)
    sl=sqrt_witness(1-kh*kh)[0]
    sh=sqrt_witness(1-kl*kl)[1]
    return {'log_v':rational_pair(Q(D3.floor(v*10**6),10**6)),
        'angles':angles,'complement':[rational_pair(sl),rational_pair(sh)],
        'agm':{name:make_agm_witness(t) for name,t in
            (('klo',kl),('khi',kh),('slo',sl),('shi',sh))}}


def check_agm_witness(t,steps):
    check(0<t<=1 and len(steps)==10,'invalid AGM input/length')
    alo=ahi=Q(1);blo=bhi=t
    for pair in steps:
        low,high=map(parse_ratio,pair)
        check(0<low<=high and low*low<=alo*blo and ahi*bhi<=high*high,
              'invalid AGM square-root bounds')
        alo,ahi,blo,bhi=(alo+blo)/2,(ahi+bhi)/2,low,high
    check(0<blo<=ahi,'AGM final order')
    return blo,ahi


def check_width_witness(row):
    args,v=width_inputs(row);w=row['width']
    v0=parse_ratio(w['log_v'])
    check(0<v0<=v<1,'logarithm witness outside gate')
    lower=2*sum(v0**(2*j+1)/Q(2*j+1) for j in range(16))/Q(44,7)
    check(lower>Q(1,4),'coarse logarithm lower fails')
    angles=[list(map(parse_ratio,pair)) for pair in w['angles']]
    check(len(angles)==2,'acos pair count')
    for arg,(lo,hi) in zip(args,angles):
        check(0<lo<hi<2,'acos bracket order')
        check(D3.cos_bounds(lo)[0]>D3.scaled(arg.hi) and
              D3.cos_bounds(hi)[1]<D3.scaled(arg.lo),'acos Taylor witness')
    (al,ah),(bl,bh)=angles
    check(ah<bl,'angle separation')
    kl=(bl-ah)/(bl+ah);kh=(bh-al)/(bh+al)
    check(0<kl<kh<1,'elliptic ratios')
    sl,sh=map(parse_ratio,w['complement'])
    check(0<sl<=sh and sl*sl<=1-kh*kh and 1-kl*kl<=sh*sh,'complement sqrt')
    agm={name:check_agm_witness(t,w['agm'][name]) for name,t in
        (('klo',kl),('khi',kh),('slo',sl),('shi',sh))}
    plane_lo=agm['klo'][0]/agm['shi'][1]
    plane_hi=agm['khi'][1]/agm['slo'][0]
    check(lower<plane_lo and plane_hi<Q(31,40),'coarse plane envelope')
    return lower,plane_hi


def verify_data(data,verbose=False):
    check(data['scale_bits']==512,'wrong dyadic scale')
    expected=list(itertools.product((3,4,5),repeat=3))
    check([tuple(row['word']) for row in data['rows']]==expected,
          'incomplete or duplicated grid')
    charts=[I(*row['parameter']) for row in data['rows']]
    check(all(a.hi<b.lo or b.hi<a.lo for i,a in enumerate(charts) for b in charts[i+1:]),
          'parameter charts not pairwise disjoint')
    for row in data['rows']:
        verify_row(row)
        check_width_witness(row)
        if verbose: print('PASS',*row['word'],'root/kneading/disks/nesting/cuts/gate/envelopes',flush=True)


def main():
    path=HERE/'data.json'
    if '--generate' in sys.argv:
        search=json.loads((HERE/'numerical_seeds.json').read_text())
        output={'scale_bits':512,'rows':[]}
        for key in sorted(search):
            row,res=make_row(search[key]);output['rows'].append(row)
            print(key,'R3',parse_ratio(row['radii'][2]),
                'lower',float(res['radial_lower']),'upper',float(res['plane_upper']),flush=True)
        path.write_text(json.dumps(output,indent=2)+'\n')
    else:
        data=json.loads(path.read_text())
        verify_data(data,verbose=True)
        print('PASS: complete 27-word finite arithmetic grid; no analytic identification claimed.')

if __name__=='__main__':main()
