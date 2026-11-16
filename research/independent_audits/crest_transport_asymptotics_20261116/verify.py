#!/usr/bin/env python3
"""Whole-parent circular-collar four-push optimizer, exact outward arithmetic.

The certified output is CONDITIONAL on physical prime-end/KKL path and conformal
width hypotheses; only finite polynomial, interval, marking and width-ratio
claims are checked here.  No floating-point numbers enter any proof predicate.
"""
from __future__ import annotations
import argparse
import gc
from dataclasses import dataclass
from fractions import Fraction as F
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
PREC=512
S=1<<PREC
Z=None
EXPECTED_BLOCKS=[[18,19,0,1,2],[3,4],[5],[6],[7,8,9],[10],
                 [11,12,13],[14],[15],[16,17]]
# Seeds merely select a *local* root: dyadic endpoint signs and whole-seed
# negative derivative reprove existence and uniqueness.  No seed is an axiom.
SEEDS={
 3:'-1.786510544544324757385260673471213673058457671889172800031923968334629798587697269507048968639156733',
 4:'-1.942554171494761905319728559547351970316877794253756256973061644721007908220533846556129430732097156',
 5:'-1.985528169705348810408255730556821748277263841949252553593917274749073066379677891609603820336856318',
 6:'-1.996382511718412027950049688816515039904858979750298286593034926678792080923860935932139817781617068',
 7:'-1.99909607830917598002359967040562747450315031202203453414490734530886689705706443584075484634242529',
 8:'-1.99977407339705875086923341331568799685514252038080974798691863676382684508119126543885186585434088',
 9:'-1.99994352330879102254975391082738335395352978817090499897525072423167823633706849247069259463644468',
 10:'-1.99998588123682174254843383503975840503292143775299401058889825653946965600383848213765034339890565',
 11:'-1.999996470341035272735632678015004938386461804580811692099169946758788547010051826504894628853093167',
 12:'-1.999999117587637481776828101553703232713431093876163616822020428055010613627327045591565019864984472',
 13:'-1.999999779397082369079696879316810098455511850736656494449253669870699215096781460701',
 14:'-1.999999944849282925470696124741280044711445213829948355375397034210618202325859904025',
 15:'-1.999999986212321597242451384524549984638543131440900114252733790846330656038807191168',
 16:'-1.999999996553080459368407387586897828211256036160400917503794389538446896111170146371',
}
# Published adjacent 2^-256 brackets, crosschecked against unchanged audit.
PRIOR_BRACKETS={
 9:-231577638920564092579136255421939630884836906131569849829313081641534396423027,
 10:-231582543633546533526283756991348241519646229656381644300932701776334013313375,
 11:-231583769768046569854648970766680764658829534892687229250012680253511623627757,
 12:-231584076298261366026035660140568367251093068401698564453360469439884152023717,
}

def must(ok,reason):
 if not ok: raise AssertionError(reason)
def ceildiv(a,b): return -((-a)//b)
def upmul(a,b): return ceildiv(a*b,S)

@dataclass(frozen=True)
class I:
 lo:int
 hi:int
 def __post_init__(self):must(self.lo<=self.hi,'interval inverted')
 @staticmethod
 def point(q):
  q=F(q)*S
  return I(q.numerator//q.denominator,ceildiv(q.numerator,q.denominator))
 @staticmethod
 def hull(lo,hi):
  must(lo<=hi,'rational hull inverted')
  return I(I.point(lo).lo,I.point(hi).hi)
 def __add__(self,b):return I(self.lo+b.lo,self.hi+b.hi)
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,b):return self+-b
 def __mul__(self,b):
  v=(self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi)
  return I(min(v)//S,ceildiv(max(v),S))
 def square(self):
  x=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
  return I(x//S,ceildiv(max(self.lo*self.lo,self.hi*self.hi),S))
 def lt(self,b):return self.hi<b.lo
 def positive(self):return self.lo>0
 def negative(self):return self.hi<0
 def meets(self,b):return self.lo<=b.hi and b.lo<=self.hi
 def lower(self):return F(self.lo,S)
 def upper(self):return F(self.hi,S)
 def mid(self):return F(self.lo+self.hi,2*S)
 def absi(self):return max(-self.lo,self.hi)
 def absl(self):return (self.lo if self.lo>0 else -self.hi if self.hi<0 else 0)

Z=I.point(0);O=I.point(1);T=I.point(2)

def orbit(c,n,der=False):
 xs=[Z];ds=[Z]
 for _ in range(n):
  if der:ds.append(T*xs[-1]*ds[-1]+O)
  xs.append(xs[-1].square()+c)
 return xs,ds

def iterate(z,c,n):
 for _ in range(n):z=z.square()+c
 return z

def parameter(p):
 seed=F(SEEDS[p]);epsilon=F(1,10**72)
 a,b=seed-epsilon,seed+epsilon
 cseed=I.hull(a,b)
 xs,ds=orbit(cseed,6*p,True)
 must((ds[6*p]+ds[3*p]).negative(),f'p={p}: local uniqueness fails')
 def pol(q):
  x,_=orbit(I.point(q),6*p)
  return x[6*p]+x[3*p]
 must(pol(a).positive() and pol(b).negative(),f'p={p}: root sign bracket fails')
 n=seed.numerator*(1<<256)//seed.denominator
 # Prove which adjacent dyadic interval contains the local root.
 for shift in range(-2,3):
  l=F(n+shift,1<<256);h=F(n+shift+1,1<<256)
  if pol(l).positive() and pol(h).negative():
   n+=shift
   break
 else:raise AssertionError(f'p={p}: no adjacent dyadic root bracket')
 must(a<F(n,1<<256) and F(n+1,1<<256)<b,'dyadic bracket escapes seed window')
 if p<=8:
  old=json.loads((ROOT/'research/independent_audits/crest_transport_tip_family_20261116/results.json').read_text())
  earlier=old['results'][p-3]['parameter_bracket_2pow192']
  must(F(earlier[0],1<<192)<F(n,1<<256) and F(n+1,1<<256)<F(earlier[1],1<<192),'old 192-bit root branch drift')
 if p in PRIOR_BRACKETS:
  must(n==PRIOR_BRACKETS[p],'wrong published parameter branch')
  prior=json.loads((ROOT/'research/independent_audits/real_primitive_tip_family_unconditional_20261116/results.json').read_text())
  entry=prior['periods'][p-3]['parameter_bracket']
  must((entry['denominator_power_of_two'],entry['lower_numerator'],entry['upper_numerator'])==(256,n,n+1),'prior 256-bit bracket drift')
 c=I.hull(F(n,1<<256),F(n+1,1<<256))
 x,_=orbit(c,6*p)
 must((x[6*p]+x[3*p]).meets(Z),'critical 3p/6p identity absent')
 must(x[1].negative() and all(x[j].positive() for j in range(2,p)),'wrong outer sign itinerary')
 must(x[3*p].negative() and x[6*p].positive(),'wrong signed 3p/6p return')
 return n,c,x

def alpha(c,p,x):
 # On (x_6p,x_4p), G_p' is negative (positive input, negative
 # first iterate, positive intermediate iterates), so G_p(z)-z has
 # at most one zero. This is independent of bisection signs.
 z=I.hull(x[6*p].lower(),x[4*p].upper())
 must(z.positive(),'alpha interval starts positive')
 for k in range(1,p):
  z=z.square()+c
  must(z.negative() if k==1 else z.positive(),
       f'alpha uniqueness derivative itinerary step {k}')
 a=x[6*p].upper();b=x[4*p].lower()
 def f(t):return iterate(I.point(t),c,p)-I.point(t)
 must(a<b and f(a).positive() and f(b).negative(),'alpha existence signs')
 for _ in range(140):
  m=(a+b)/2;v=f(m)
  must(v.positive() or v.negative(),'alpha midpoint indeterminate')
  if v.positive():a=m
  else:b=m
 return I.hull(a,b)

def source_actions(c,p,x,al):
 target=[x[5*p],x[3*p],x[6*p],al,x[4*p]]
 cuts=[-x[4*p],x[2*p],x[5*p],-al,x[3*p],x[6*p],al,-x[5*p],-x[2*p],x[4*p]]
 must(all(a.lt(b) for a,b in zip(cuts,cuts[1:])),'source cuts not strict')
 must(all(a.lt(b) for a,b in zip(target,target[1:])),'target cuts not strict')
 expected=[target[i] for i in (0,1,2,3,4,4,3,2,1,0)]
 for z,t in zip(cuts,expected):
  must(iterate(z,c,p).meets(t),'source cut is not inverse of named target cut')
 def idx(v,side,marks):
  if v.lt(marks[0]):return 0
  if marks[-1].lt(v):return len(marks)
  for j in range(1,len(marks)):
   if marks[j-1].lt(v) and v.lt(marks[j]):return j if side==1 else 2*len(marks)-j
  raise AssertionError('point touches cut')
 def atom(s,marks,left,right):
  n=len(marks)
  if s==0:a,b,side=left,marks[0],1
  elif s==n:a,b,side=marks[-1],right,1
  else:
   j,side=(s,1) if s<n else (2*n-s,-1)
   a,b=marks[j-1],marks[j]
  must(a.lt(b),'empty source atom')
  return I.point((2*a.mid()+b.mid())/3),side
 cover=[];pull=[];attached=[]
 for s in range(20):
  z,side=atom(s,cuts,-x[p],x[p])
  cover.append(idx(iterate(z,c,p),side if z.upper()<0 else -side,target))
  is_attached=z.lt(x[2*p]);attached.append(s) if is_attached else None
  pull.append(0 if is_attached else idx(z,side,target))
 blocks=[]
 for i in range(10):
  starts=[s for s in range(20) if pull[s]==i and pull[(s-1)%20]!=i]
  must(len(starts)==1,'iota* disconnected block')
  s=starts[0];block=[]
  while pull[s]==i:
   must(len(block)<20,'iota* wraps full circle')
   block.append(s);s=(s+1)%20
  blocks.append(block)
 must(cover==[s%10 for s in range(20)],'G* covering labels')
 must(blocks==EXPECTED_BLOCKS,'iota* immersion blocks')
 must(attached==[0,1,19],'attached side census')
 host={s:i for i,block in enumerate(blocks) for s in block}
 pairs=[((3,1),(19,17)),((6,4),(16,14)),((9,11),),((0,3),(17,0))]
 for stage in pairs:
  for a,b in stage:
   must(host[a]!=host[b],'improper immersion endpoints')
   must(1+min((b-a)%20,(a-b)%20)>2,'KKL source short deletion')
   aa,bb=cover[a],cover[b]
   must(1+min((bb-aa)%10,(aa-bb)%10)>2,'KKL cover short deletion')
 edges=[(x[5*p],x[3*p]),(x[6*p],al),(al,x[4*p])]
 incidence={}
 for s in range(10):
  v,side=atom(s,target,x[2*p],x[p])
  incidence[s]=[j for j,(a,b) in enumerate(edges) if a.lt(v) and v.lt(b)]
 must([s for s in range(10) if incidence[s]]==[1,3,4,6,7,9],'edge incidence')
 must(incidence[1]==incidence[9]==[0],'upper/lower crest must share ONE old edge E0')
 must(atom(1,target,x[2*p],x[p])[1]==1 and atom(9,target,x[2*p],x[p])[1]==-1,'slit sides not opposite')
 return cover,blocks,idx

def rouche(c,p):
 R=F(1,4) if p==3 else F(1,2**p)
 d,A=Z,Z;tail=0
 for k in range(1,p+1):
  tail=upmul(2*d.absi(),tail)+upmul(upmul(A.absi(),I.point(R*R).hi)+tail,upmul(A.absi(),I.point(R*R).hi)+tail)
  A=O if k==1 else T*d*A
  d=d.square()+c
 margin=A.absl()*I.point(R*R).lo//S-d.absi()-tail-I.point(R).hi
 must(margin>I.point(F(1,25)).hi,f'p={p} no Rouché margin >1/25')
 return F(margin,S)

def phase_disjoint(c,p):
 """Pairwise disjoint FULL complex phase disks for the selected U_p."""
 target=F(1,4) if p==3 else F(1,2**p)
 ctr=Z;radius=I.point(target).hi;balls=[]
 for j in range(p):
  for oldc,oldr in balls:
   must(ctr.lo-oldc.hi>radius+oldr or oldc.lo-ctr.hi>radius+oldr,
        f'p={p}: complex phase disks overlap at j={j}')
  balls.append((ctr,radius))
  radius=upmul(2*ctr.absi(),radius)+upmul(radius,radius)
  ctr=ctr.square()+c
 return True

def chebyshev_finite_distortion(c,p,x):
 """Exact finite Taylor control, NOT uniform Chebyshev convergence.

 G_p(z)=x_p + A_p z^2 + E_p(z), |E_p(z)|<=tail on |z|<=5*x_p/4.
 In normalized coordinates H_p(t)=1-kappa_p*t²+e(t), |e|<=tail/x_p.
 """
 d,A=Z,Z;tail=0
 rad=(I.point(F(5,4))*x[p]).upper()
 rad2=I.point(rad*rad).hi
 for k in range(1,p+1):
  inner=upmul(A.absi(),rad2)+tail
  tail=upmul(2*d.absi(),tail)+upmul(inner,inner)
  A=O if k==1 else T*d*A
  d=d.square()+c
 must(d.meets(x[p]),'Taylor centre is not critical return')
 kapa=-A*x[p]
 must(kapa.positive() and kapa.lower()>F(17,10) and kapa.upper()<F(19,10),
      f'p={p}: unexpected normalized quadratic coefficient')
 err=F(tail,x[p].lo)
 # For p>=9, the deterministic holomorphic remainder is already tiny.
 if p>=9:must(err<F(1,10000),'finite normalized Taylor tail too large')
 # Recorded decimal brackets are rational outward enclosures, never floats.
 t=10**8
 lo=(kapa.lo*t)//S;hi=ceildiv(kapa.hi*t,S)
 return lo,hi,ceil_scaled(err,10**12)

def rim(z,y2,c,p):
 # Re(G(z+iY)), Im(G(z+iY))/Y, Y^2=y2.
 b=O;v=z
 for _ in range(p):
  v,b=v.square()-y2*b.square()+c,T*v*b
 return v,b

def arc(d,r,u,c,p):
 return rim(d+r*u,r.square()*(O-u.square()),c,p)

def gate(d,r,c,p):
 lo,hi=F(-1,8),F(1,4)
 must(arc(d,r,I.point(lo),c,p)[0].negative(),'left angular gate sign')
 must(arc(d,r,I.point(hi),c,p)[0].positive(),'right angular gate sign')
 for _ in range(62):
  mid=(lo+hi)/2;v=arc(d,r,I.point(mid),c,p)[0]
  if v.negative():lo=mid
  elif v.positive():hi=mid
  else:break
 return I.hull(lo,hi)

def y_return(d,r,u,c,p):
 re,factor=arc(d,r,u,c,p)
 must(factor.positive(),'imaginary half-plane preservation not enclosed')
 y2=r.square()*(O-u.square())*factor.square()
 must(y2.positive(),'squared imaginary height vanished')
 r2=iterate(c-y2,c,p-1)
 r3=iterate(r2,c,p)
 r4=iterate(r3,c,p)
 return y2,r2,r3,r4

def derivative_disk(c,p,d,maxr):
 """Proves |G'(z)-G'(d)|<=E on full disk |z-d|<=maxr."""
 radius=I.point(maxr.upper()).hi
 v=d;A=O;D=radius;E=0
 for _ in range(p):
  E=upmul(2*v.absi(),E)+upmul(2*D,A.absi()+E)
  D=upmul(2*v.absi(),D)+upmul(D,D)
  A=T*v*A
  v=v.square()+c
 # For u in [-1/8,1/4], sqrt(1-u^2)>=15/16.  This bound
 # implies Re G'(z)>0, dReG/du>0, Im(G'(z)e^iθ)>0.
 must(15*(A.lo-E)>4*E,f'p={p}: no uniform derivative/angle monotonicity')
 return F(A.lo-E,S),F(E,S)

def range_root_and_monotonic(p,c,x,d,parent_lo,parent_hi,rad):
 # Every parent radius has its unique first imaginary-axis crossing.
 for i in range(64):
  l=parent_lo+(parent_hi-parent_lo)*F(i,64)
  h=parent_lo+(parent_hi-parent_lo)*F(i+1,64)
  gate(d,rad(I.hull(l,h)),c,p)
 derivative_disk(c,p,d,rad(I.point(parent_hi)))
 # On the first vertical crossing, Y'(r)=|G'(z)|²/Im(G'(z)e^{iθ})>0.
 # Since f^(p-1)'(c-Y²)<0 and G'(r2)<0, r2 increases and r3 decreases.
 lhs=rad(I.point(parent_lo));rhs=rad(I.point(parent_hi))
 yl,r2l,_,_=y_return(d,lhs,gate(d,lhs,c,p),c,p)
 yh,r2h,_,_=y_return(d,rhs,gate(d,rhs,c,p),c,p)
 must(yl.lt(yh) and r2l.lt(r2h),'imaginary return not increasing at parent ends')
 y2span=I.hull(yl.lower(),yh.upper())
 z=c-y2span
 must(z.negative(),'p-1 orbit input must be negative')
 for j in range(1,p-1):
  z=z.square()+c
  must(z.positive(),f'p={p} derivative sign lost for f^(p-1) at step {j}')
 span=I.hull(r2l.lower(),r2h.upper())
 must(span.positive(),'second return must be positive')
 z=span
 for j in range(1,p):
  z=z.square()+c
  must(z.negative() if j==1 else z.positive(),f'p={p} G derivative sign lost at {j}')
 # On this interval, G maps [-x_p,-x_4p] increasingly to [x_2p,x_5p].
 z=I.hull((-x[p]).lower(),(-x[4*p]).upper())
 must(z.negative(),'terminal negative interval missing')
 for j in range(1,p):
  z=z.square()+c
  must(z.negative() if j==1 else z.positive(),f'p={p} terminal G monotonicity failed')
 return True

def bisect_terminal(p,c,x,d,rad,target,parent_lo,parent_hi):
 def sign(s):
  r=rad(I.point(s));u=gate(d,r,c,p)
  return y_return(d,r,u,c,p)[2] - target
 a,b=parent_lo,parent_hi
 fa,fb=sign(a),sign(b)
 must(fa.positive() and fb.negative(),f'p={p}: terminal boundary not between parent radii')
 for _ in range(55):
  m=(a+b)/2;v=sign(m)
  must(v.positive() or v.negative(),'terminal sign unresolved')
  if v.positive():a=m
  else:b=m
 return a,b

def atan(q,n=42):
 s=sum(((-1)**k*q**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
 term=q**(2*n+1)/F(2*n+1)
 return (s,s+term) if n%2==0 else (s-term,s)

def pi_bounds():
 a,b=atan(F(1,5));v,w=atan(F(1,239))
 lo,hi=4*(4*a-w),4*(4*b-v)
 must(F(333,106)<lo<hi<F(355,113),'Machin interval pi failure')
 return lo,hi

def asin_bounds(q,n=8):
 q=F(q);coef=F(1);value=F(0)
 for k in range(n):
  if k:coef=coef*F((2*k-1)**2,2*k*(2*k+1)) # exact arcsin Maclaurin coefficient ratio
  value+=coef*q**(2*k+1)
 tail=abs(q)**(2*n+1)/(1-q*q)
 return value-tail,value+tail

def log_interval(q,n=23):
 must(q>=1,'log expects >=1')
 if q==1:return F(0),F(0)
 z=(q-1)/(q+1)
 must(z<F(1,2),'log atanh reduction exceeded valid range')
 base=2*sum((z**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
 tail=2*z**(2*n+1)/F(2*n+1)/(1-z*z)
 return base,base+tail

def ceil_scaled(q,t):return ceildiv(q.numerator*t,q.denominator)
def floor_scaled(q,t):return q.numerator*t//q.denominator

def width_bounds(p,c,x,d,rad,aL,aU,bL,bU,parent_lo,parent_hi,bins):
 plo,phi=pi_bounds()
 must(aL<=aU<bL<=bU,'invalid terminal collar bracket')
 total_lo=F(0);total_hi=F(0)
 for j in range(bins):
  a=aU+(bL-aU)*F(j,bins); b=aU+(bL-aU)*F(j+1,bins)
  r=rad(I.hull(a,b));u=gate(d,r,c,p)
  must(u.lower()>=-F(1,8) and u.upper()<=F(1,4),'root outside arcsin regime')
  theta_hi=phi/2-asin_bounds(u.lower())[0]
  theta_lo=plo/2-asin_bounds(u.upper())[1]
  must(theta_lo>0,'nonpositive angle')
  llo,lhi=log_interval(b/a,8)
  total_lo+=llo/theta_hi
  total_hi+=lhi/theta_lo
 # Add slivers to upper bound, including roots of terminal equations.
 taulo=plo/2-asin_bounds(F(1,4))[1]
 must(taulo>0,'global angle bound')
 edge1=log_interval(aU/aL,8)[1]
 edge2=log_interval(bU/bL,8)[1]
 total_hi+=(edge1+edge2)/taulo
 parent_ratio=parent_hi/parent_lo
 denlo,denhi=log_interval(parent_ratio)
 lower=2*plo*total_lo/denhi
 upper=2*phi*total_hi/denlo
 t=100000
 ll=floor_scaled(lower,t);uu=ceil_scaled(upper,t)
 must(0<ll<uu,'invalid two sided ratio bounds')
 return ll,uu

def whole_disk_four(p,c,d,rad,maxs,xp):
 target=F(1,2**p) if p>3 else F(1,4)
 r=rad(I.point(maxs))
 center=d.mid(); radius=r.upper()+d.upper()-center
 must(abs(center)+radius<target,'initial full disk not in U')
 ctr=I.point(center);disc=I.point(radius)
 for k in range(1,4*p+1):
  disc=T*I.point(ctr.absi()/S)*disc+disc.square()
  ctr=ctr.square()+c
  if k%p==0:
   must(F(ctr.absi()+disc.hi,S)<target,f'p={p} full disk exits U after {k//p} pushes')
   if k//p<=3:must((-xp).lt(ctr) and ctr.lt(xp),'disk center loses real central selector')
   if k//p==2:must(ctr.lo>disc.hi,'second support not positive')
   if k//p==3:must(ctr.hi< -disc.hi,'third support not negative')
 return True

def other_gates(p,c,x,alpha,d,rad,a,b,idx):
 cuts=[-x[4*p],x[2*p],x[5*p],-alpha,x[3*p],x[6*p],alpha,
       -x[5*p],-x[2*p],x[4*p]]
 must((-x[4*p]).lt(x[2*p]) and x[5*p].lt(-alpha),'strict source marked gates')
 for j in range(192):
  lo=a+(b-a)*F(j,192);hi=a+(b-a)*F(j+1,192)
  r=rad(I.hull(lo,hi));q=d+r;w=d-r
  must(x[5*p].lt(q) and q.lt(-alpha),'initial q access')
  must((-x[4*p]).lt(w) and w.lt(x[2*p]),'initial w access')
  must((idx(q,1,cuts),idx(w,1,cuts),idx(w,-1,cuts),idx(q,-1,cuts))==(3,1,19,17),'initial source labels')
  for k in range(1,5):
   q=iterate(q,c,p);w=iterate(w,c,p)
   if k==1:
    must(x[6*p].lt(q) and q.lt(alpha) and (-alpha).lt(w) and w.lt(x[3*p]),'first push endpoints')
    must((idx(q,1,cuts),idx(w,1,cuts),idx(w,-1,cuts),idx(q,-1,cuts))==(6,4,16,14),'first pushed source labels')
   if k==2:
    must((-x[2*p]).lt(q) and q.lt(x[4*p]) and (-x[2*p]).lt(w) and w.lt(x[4*p]),'second pushed endpoints')
    must((idx(q,1,cuts),idx(w,1,cuts),idx(w,-1,cuts),idx(q,-1,cuts))==(9,9,11,11),'second pushed source labels')
   if k==3:
    must(x[5*p].lt(q) and q.lt(-alpha),'third selected q-side gate')
    must((idx(q,1,cuts),idx(q,-1,cuts))==(3,17),'third selected q source labels')
    # Do NOT assign the other w endpoint a fixed atom here.
   if k==4:must(x[6*p].lt(q) and q.lt(alpha),'fourth q side gate')
 return True

def run(p,bins=512):
 n,c,x=parameter(p);al=alpha(c,p,x)
 must(all(a.lt(b) for a,b in zip([x[2*p],x[5*p],x[3*p],Z,x[6*p],al,x[4*p],x[p]],
                                  [x[5*p],x[3*p],Z,x[6*p],al,x[4*p],x[p],I.point(F(1,4) if p==3 else F(1,2**p))])),'target real order')
 must((-x[p]).lt(-x[4*p]) and (-x[4*p]).lt(x[2*p]) and x[5*p].lt(-al),'source real order')
 cover,blocks,idx=source_actions(c,p,x,al)
 rouche_margin=rouche(c,p)
 phase_disjoint(c,p)
 kappa_lower,kappa_upper,tail_error=chebyshev_finite_distortion(c,p,x)
 if p==3:
  d=I.point(F(-9,64));lo,hi=F(3,256),F(1,64)
  rad=lambda q:q
 else:
  d=I.point(-F(3,4))*x[p];lo,hi=F(1,16),F(p-1,8*p)
  rad=lambda q:q*x[p]
 range_root_and_monotonic(p,c,x,d,lo,hi,rad)
 # If the lower terminal threshold is already passed at the parent's
 # inner circle, that circle itself is the active (open) endpoint.
 rr=rad(I.point(lo));uu=gate(d,rr,c,p)
 start=y_return(d,rr,uu,c,p)[2]-(-x[4*p])
 if start.negative():aL=aU=lo;lower_active='parent inner radius'
 else:
  must(start.positive(),'lower terminal sign ambiguous at parent')
  aL,aU=bisect_terminal(p,c,x,d,rad,-x[4*p],lo,hi)
  lower_active='terminal -x_4p cut'
 upperL,upperU=bisect_terminal(p,c,x,d,rad,-x[p],lo,hi)
 bL,bU=upperL,upperU
 must(lo<=aL<=aU<bL<=bU<hi,'optimal collar not strictly in chosen parent')
 # Independent strict margins on the WHOLE outer bracket, not merely the
 # inner certified strip. The only endpoint failure is the named S0 cut.
 other_gates(p,c,x,al,d,rad,aL,bU,idx)
 whole_disk_four(p,c,d,rad,bU,x[p])
 ll,uu=width_bounds(p,c,x,d,rad,aL,aU,bL,bU,lo,hi,bins)
 # Independently extend the previous audit's chosen narrow-radius bins
 # for p=9..16 (and cross-check the six original choices) without
 # confusing these smaller witnesses with the circular-family optimum.
 if p==3:fixed_a,fixed_b=F(1,80),F(1,77)
 elif p==4:fixed_a,fixed_b=F(63,1000),F(667,10000)
 elif p==5:fixed_a,fixed_b=F(313,5000),F(663,10000)
 else:fixed_a,fixed_b=F(1,16),F(663,10000)
 must(aU<=fixed_a<fixed_b<=bL,'original fixed bin no longer inside certified full collar')
 fixed_ll,fixed_uu=width_bounds(p,c,x,d,rad,fixed_a,fixed_a,
                                fixed_b,fixed_b,lo,hi,bins)
 if p<=8:
  old=json.loads((ROOT/'research/independent_audits/crest_transport_tip_family_20261116/results.json').read_text())['results'][p-3]
  from_old=lambda label:F(old[label])
  must(F(fixed_ll,100000)<=from_old('certified_ratio_upper') and
       from_old('certified_ratio_lower')<=F(fixed_uu,100000),
       'fixed-bin result disagrees with prior source certificate')
 return {
  'p':p,'parameter_bracket_2pow256':[n,n+1],
  'central_Rouche_margin_gt_1_25':True,
  'complex_primitive_phase_disks_pairwise_disjoint':True,
  'normalized_quadratic_kappa_bracket_1e8':[kappa_lower,kappa_upper],
  'normalized_Taylor_error_upper_1e12_on_abs_t_le_5_4':tail_error,
  'parent':{'center':'-9/64' if p==3 else '-3*x_p/4',
            'radius_variable':'absolute radius' if p==3 else 's=r/x_p',
            'range':[str(lo),str(hi)]},
  'optimal_circular_collar':{'lower_active':lower_active,
             'lower_bracket':[str(aL),str(aU)],'upper_bracket':[str(bL),str(bU)]},
  'ratio_bracket_1e5':[ll,uu],
  'original_fixed_subcollar':{'radius':[str(fixed_a),str(fixed_b)],
    'ratio_bracket_1e5':[fixed_ll,fixed_uu]},
  'width_interpretation':'conditional on physical prime-end/KKL/univalence and exact conformal strip-width hypotheses',
  'two_selected_terminal_crests':['upper: S0,S3 -> I0,I3; closed I1,I2 with E0 upper',
                                  'lower: S17,S0 -> I7,I0; closed I8,I9 with E0 lower'],
 }

def results(bins=512):
 must(bins>=64,'insufficient whole-radius bins')
 rows=[]
 for p in range(3,17):
  rows.append(run(p,bins))
  gc.collect()
 return {'schema':'crest-transport-asymptotics-finite-optimal-circular-v1',
         'meaning':'maximal connected circular subcollar of the specified parent Wave with the selected S0 terminal gate, not the unconstrained KKL-maximal Wave',
         'uniform_p_asymptotics':'numerical conjecture only; physical and quantitative all-p estimates open',
         'arithmetic':'outward fixed grid 2^-512, exact rationals, Machin/asin/atanh with explicit tails',
         'covering_G_star':'S_s -> I_(s mod 10)',
         'immersion_iota_star_blocks':EXPECTED_BLOCKS,
         'results':rows}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--write',action='store_true');ap.add_argument('--bins',type=int,default=512)
 a=ap.parse_args()
 data=json.dumps(results(a.bins),sort_keys=True,indent=2)+'\n'
 path=HERE/'results.json'
 if a.write:path.write_text(data);print('WROTE',path)
 else:must(path.read_text()==data,'locked certificate drift');print('PASS p9-p16 finite optimal circular collars, typed 4-push and rational two-sided bounds')

if __name__=='__main__':main()
