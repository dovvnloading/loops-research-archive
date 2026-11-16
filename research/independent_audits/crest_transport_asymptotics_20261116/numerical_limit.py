#!/usr/bin/env python3
"""NON-CERTIFIED double-precision Q_kappa limit / quadrature exploration.

Nothing here is used by verify.py or as a theorem/CI certificate.
"""
import math

def Q(x,k):return 1-k*x*x

def sextuple(k):
 x=0.;v=[]
 for _ in range(6):x=Q(x,k);v.append(x)
 return v[2]+v[5]

def limit(n=20000):
 lo,hi=1.79,1.791
 assert sextuple(lo)<0 and sextuple(hi)>0
 for _ in range(80):
  m=(lo+hi)/2
  if sextuple(m)<0:lo=m
  else:hi=m
 k=(lo+hi)/2
 y=math.sqrt((math.sqrt(2/k)-1)/k)
 x=-math.sqrt((math.sqrt(1+y*y)+1)/(2*k))
 yy=math.sqrt((math.sqrt(1+y*y)-1)/(2*k))
 s=math.hypot(x+.75,yy)
 def u(r):
  d=-.75;a=2*r*r;b=2*d*r;cc=d*d-r*r-1/k
  return 2*cc/(-b+math.sqrt(b*b-4*a*cc))
 def fun(r):return 1/(r*math.acos(u(r)))
 a=1/16;h=(s-a)/n
 integral=h/3*(fun(a)+fun(s)+4*math.fsum(fun(a+j*h) for j in range(1,n,2)) +
                2*math.fsum(fun(a+j*h) for j in range(2,n,2)))
 return {'kappa':k,'outer_s':s,'A_infty':2*math.pi*integral,'c_infty':2*math.pi*integral/math.log(2)}

if __name__=='__main__':
 for key,val in limit().items():print(key,repr(val))
