"""Rigorous complex disks with exact integer outward rounding (not GMP floats)."""
import argparse,json
from fractions import Fraction
from math import isqrt
from pathlib import Path
import mpmath as m
BITS=320; S=1<<BITS

def ceildiv(a,b): return -(-a//b)
def upnorm(x,y):
    n=x*x+y*y;t=isqrt(n);return t+(t*t!=n)
def seed(s):
    x,y=(Fraction(v)*S for v in s);return Ball(x.numerator//x.denominator,y.numerator//y.denominator)
class Ball:
    def __init__(self,x=0,y=0,r=0): self.x,self.y,self.r=x,y,r
    def __add__(a,b):
        if isinstance(b,int): b=Ball(b*S)
        return Ball(a.x+b.x,a.y+b.y,a.r+b.r)
    __radd__=__add__
    def __neg__(a): return Ball(-a.x,-a.y,a.r)
    def __sub__(a,b): return a+-b
    def __rsub__(a,b): return -a+b
    def __mul__(a,b):
        if isinstance(b,int): return Ball(a.x*b,a.y*b,a.r*abs(b))
        x=(a.x*b.x-a.y*b.y)//S;y=(a.x*b.y+a.y*b.x)//S
        r=ceildiv(upnorm(a.x,a.y)*b.r+upnorm(b.x,b.y)*a.r+a.r*b.r,S)+2
        return Ball(x,y,r)
    __rmul__=__mul__
    def __pow__(a,n):
        b=Ball(S)
        for _ in range(n): b=b*a
        return b
    def upper(a): return upnorm(a.x,a.y)+a.r
    def lower(a): return max(0,isqrt(a.x*a.x+a.y*a.y)-a.r)
    def disk(a,r): return Ball(a.x,a.y,r)
    def mid(a): return m.mpc(m.mpf(a.x)/S,m.mpf(a.y)/S)
    def record(a): return [str(a.x),str(a.y),str(a.r)]
    def iv(a):
        v=m.iv.mpf
        return m.iv.mpc(v([a.x-a.r,a.x+a.r])/S,v([a.y-a.r,a.y+a.r])/S)

def jet(c,z,p,second=False):
    w=z;a=Ball(S);b=h=d=Ball();gap=S if p==1 else None
    for j in range(1,p+1):
        if second: h,d=2*(a*a+w*h),2*(a*b+w*d)
        a,b=2*w*a,2*w*b+1;w=w*w+c
        if j<p and p%j==0:
            g=(w-z).lower();gap=g if gap is None else min(gap,g)
    return w,a,b,h,d,gap

def inverse(M):
    m.mp.dps=110
    V=m.matrix([[b.mid() for b in row] for row in M])**-1
    return [[seed([m.nstr(V[i,j].real,105),m.nstr(V[i,j].imag,105)]) for j in range(V.cols)] for i in range(V.rows)]
def contract(Y,g,J,r):
    # infinity norm in a complex polydisk with possibly unequal radii.
    n=len(r);factors=[];ratios=[]
    for i in range(n):
        e=sum((Y[i][k]*g[k] for k in range(n)),Ball()).upper()
        jac=[((1 if i==j else 0)-sum((Y[i][k]*J[k][j] for k in range(n)),Ball())).upper() for j in range(n)]
        t=sum(v*rj for v,rj in zip(jac,r));assert t<S*r[i] and e*S+t<S*r[i], 'contraction failed'
        factors.append(ceildiv(t*10**12,S*r[i]));ratios.append(ceildiv((e*S+t)*10**12,S*r[i]))
    return dict(contraction_upper_1e12=max(factors),selfmap_upper_1e12=max(ratios))

def bound(x):
    # Exact outward-rounded decimal enclosure of an mpmath.iv real interval.
    def frac(t):
        sign,man,exp,_=t;return Fraction((-1 if sign else 1)*man)*Fraction(2)**exp
    a,b=map(frac,x._mpi_);n=10**12
    return [a.numerator*n//a.denominator,ceildiv(b.numerator*n,b.denominator)]
def scaled(a,q):
    m.iv.dps=110
    return bound(q*abs(m.iv.log(a.iv())/(2*m.iv.pi*m.iv.j)))
def center(c,p):
    r=S>>150;C=c.disk(r);f,_,b,_,_,_=jet(c,Ball(),p);_,a,B,_,_,gap=jet(C,Ball(),p)
    cert=contract(inverse([[b]]),[f],[[B]],[r]);assert gap>0
    return C,dict(**cert,parameter=C.record(),period=p,gap_lower_1e12=gap*10**12//S,multiplier=Ball().record())
def root(c,z,p,q):
    r=S>>150;C,Z=c.disk(r),z.disk(r)
    f,a,b,h,d,_=jet(c,z,p,True);_,A,B,H,D,gap=jet(C,Z,p,True)
    v=q*a**(q-1);V=q*A**(q-1)
    J0=[[b,a-1],[v*d,v*h]];J=[[B,A-1],[V*D,V*H]]
    cert=contract(inverse(J0),[f-z,a**q-1],J,[r,r]);assert gap>0
    for k in range(1,q):
        if q%k==0: assert (A**k-1).lower()>0
    m.iv.dps=110; angle=m.iv.arg(A.iv())*q/(2*m.iv.pi)
    assert angle.a>m.iv.mpf('.9') and angle.b<m.iv.mpf('1.1')
    return dict(**cert,parameter=C.record(),point=Z.record(),period=p,gap_lower_1e12=gap*10**12//S,multiplier=A.record(),scaled_norm_1e12=scaled(A,q))
def dividing(C,z,p,q):
    r=S>>110;Z=z.disk(r);f,a,_,_,_,_=jet(C,z,p);_,A,_,_,_,gap=jet(C,Z,p)
    # For the unique certified center c*, use the same contraction uniformly for c in C.
    cert=contract(inverse([[a-1]]),[f-z],[[A-1]],[r]);assert gap>0
    assert A.lower()>0 and A.y-A.r>0 # principal logarithm avoids its cut
    return dict(**cert,point=Z.record(),period=p,gap_lower_1e12=gap*10**12//S,multiplier=A.record(),scaled_norm_1e12=scaled(A,q))

def run(inputs):
    rows=[]
    for x in inputs:
        q,p,P=x['q'],x['p'],x['P'];c=seed(x['center']);r=seed(x['root'])
        C,ce=center(c,P);ro=root(r,seed(x['root_point']),p,q);di=dividing(C,seed(x['center_point']),p,q)
        rows.append(dict(q=q,center=ce,root=ro,dividing_at_center=di));print('certified',q,di['scaled_norm_1e12'],flush=True)
    return dict(bits=BITS,scale='2^320',levels=rows)

def main():
    a=argparse.ArgumentParser();a.add_argument('inputs');a.add_argument('output');v=a.parse_args();x=json.loads(Path(v.inputs).read_text());Path(v.output).write_text(json.dumps(run(x),indent=2,sort_keys=True)+'\n')
if __name__=='__main__': main()
