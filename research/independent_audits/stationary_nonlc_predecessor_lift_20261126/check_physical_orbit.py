"""Exact finite regression; not a proof of the continuum or Wave statements."""
from itertools import combinations
import json

S = 1 << 256
LO = -607918036626757496169199575185708826140
HI = LO + 1

def const(x):
    return (x*S, x*S)

def add(a,b):
    return (a[0]+b[0], a[1]+b[1])

def mul(a,b):
    p = [x*y for x in a for y in b]
    return min(p)//S, -(-max(p)//S)

def square(a):
    x,y=a
    return (0 if x<=0<=y else min(x*x,y*y)//S, -(-max(x*x,y*y)//S))

def neg(a):
    return -a[1],-a[0]

def orbit(c,n):
    x=[const(0)]; d=[const(0)]
    for _ in range(n):
        d.append(add(mul(mul(const(2),x[-1]),d[-1]),const(1)))
        x.append(add(square(x[-1]),c))
    return x,d

def sign(a):
    return 1 if a[0]>0 else -1 if a[1]<0 else 0

def disjoint(a,b):
    return a[1]<b[0] or b[1]<a[0]

def abs_hi(a):
    return max(abs(a[0]),abs(a[1]))

def abs_lo(a):
    return 0 if a[0]<=0<=a[1] else min(abs(a[0]),abs(a[1]))

def up(a,b):
    return -(-(a*b)//S)

def gap(a,b):
    return max(a[0]-b[1],b[0]-a[1])

def ql_margin(x,p,r,target):
    # Exact upper bounds on |f^j(z)-x_j|, quadratic coefficient and
    # tail, valid uniformly on |z|<=r (dyadic radius).
    dev=[r]; tail=0; coeff=const(0)
    for j in range(p):
        if j==0:
            dev.append(up(r,r)); coeff=const(1)
            continue
        # f^{j+1}-x_{j+1}=2*x_j*(A_j*z^2+E_j)+(f^j-x_j)^2
        tail=up(2*abs_hi(x[j]),tail)+up(dev[-1],dev[-1])
        coeff=mul(mul(const(2),x[j]),coeff)
        dev.append(up(2*abs_hi(x[j]),dev[-1])+up(dev[-1],dev[-1]))
    lower=abs_lo(coeff)*r*r//(S*S)-abs_hi(x[p])-tail-target
    assert lower>0
    assert all(gap(x[i],x[j])>dev[i]+dev[j]
               for i,j in combinations(range(p),2))
    return lower

def main():
    c=(LO<<128,HI<<128)
    x,d=orbit(c,18)
    f=[]
    for endpoint in c:
        y,_=orbit((endpoint,endpoint),18)
        f.append(sign(add(y[18],y[9])))
    assert f[0]*f[1]==-1
    assert sign(add(d[18],d[9])) != 0
    assert all(disjoint(x[i],x[j]) for i,j in combinations(range(19),2))
    m=const(1)
    for i in range(10,19):
        m=mul(m,mul(const(2),x[i]))
    assert m[0]>S or m[1]<-S
    # The physical orbit is periodic from x10, so no orbit point can be
    # any predecessor of a fixed point: its eventual period is exactly 9.
    # Independently certify the real 9-cycle interval endpoints' ordering.
    pairs=[(9,18),(1,10),(11,2),(12,3),(13,4),(5,14),(6,15),(16,7),(8,17)]
    intervals=[]
    for i,j in pairs:
        assert x[i][1]<x[j][0]
        intervals.append((x[i][0],x[j][1]))
    assert all(disjoint(a,b) for a,b in combinations(intervals,2))
    # 0 in phase 0, phase 1 contains the critical value. All other
    # phase intervals avoid the critical point, so f is monotone there.
    assert x[9][1]<0<x[18][0]
    assert all(sign(a)!=0 for a in intervals[1:])
    # At the isolated root x18=-x9, x19=x10 exactly. The endpoint map
    # on each phase follows from the recurrence and the sign of each
    # interval, not from comparing overlapping floating-point boxes.
    def next_index(i):
        return 10 if i==18 else i+1
    for k,(i,j) in enumerate(pairs):
        target=pairs[(k+1)%9]
        if k==0:
            # Both symmetric endpoints map to x10, 0 maps to x1.
            assert target==(1,10) and next_index(i)==next_index(j)==10
        elif sign(intervals[k])<0:
            assert target==(next_index(j),next_index(i))
        else:
            assert target==(next_index(i),next_index(j))
    # A proper degree-two polynomial-like return at the outer scale.
    # Rouché applied to f^3(z)-w for every |w|<=1/4.
    margin=ql_margin(x,3,S//4,S//4)
    assert all(abs_hi(x[i])<S//4 for i in (0,3,6,9,12,15,18))
    # The exact eventual relation x19=x10 ensures these are all
    # successive multiples of three; hence the critical orbit stays in U.
    print(json.dumps({"parameter_bracket_power":128,"signs":f,
        "critical_preperiod":10,"critical_period":9,
        "strictly_repelling_period9":True,"disjoint_real_interval_cycle":9,
        "rouche_period3_margin_lower_millionths":margin*10**6//S,
        "scope":"finite orbit, real intervals and complex disk bounds only"},sort_keys=True))

if __name__=="__main__":
    main()
