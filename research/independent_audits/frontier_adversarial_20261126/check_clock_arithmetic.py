#!/usr/bin/env python3
"""Exact arithmetic premises for the sharp clock theorem, not a geometry proof."""
import json
from fractions import Fraction as F
from math import gcd

Q = 1 << 256
N = -607918036626757496169199575185708826140
DEN = 1 << 128


def iv(x, y=None):
    y = x if y is None else y
    x, y = F(x) * Q, F(y) * Q
    return x.numerator // x.denominator, -((-y.numerator) // y.denominator)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    p = [x*y for x in a for y in b]
    return min(p)//Q, -((-max(p))//Q)


def sq(a):
    lo = 0 if a[0] <= 0 <= a[1] else min(a[0]**2, a[1]**2)
    hi = max(a[0]**2, a[1]**2)
    return lo//Q, -((-hi)//Q)


def lt(a, b):
    return a[1] < b[0]


def require(test, msg):
    if not test:
        raise ArithmeticError(msg)


def orbit(c, n, start=(0, 0)):
    x = [start]
    for _ in range(n):
        x.append(add(sq(x[-1]), c))
    return x


def abs_upper(a):
    return F(max(abs(a[0]), abs(a[1])), Q)


def min_gap(a, b):
    return F(max(a[0]-b[1], b[0]-a[1]), Q)


def main():
    L, R = F(N, DEN), F(N+1, DEN)
    c = iv(L, R)
    x = orbit(c, 18)
    z = iv(0)
    two = iv(2)
    signs = []
    for p in (L, R):
        y = orbit(iv(p), 18)
        v = add(y[9], y[18])
        require(lt(v, z) or lt(z, v), 'endpoint sign')
        signs.append(1 if lt(z, v) else -1)
    d = [z]
    for j in range(18):
        d.append(add(mul(mul(two, x[j]), d[j]), iv(1)))
    dd = add(d[9], d[18])
    require(signs[0] == -signs[1], 'opposite endpoint signs')
    require((signs == [-1, 1] and lt(z, dd)) or
            (signs == [1, -1] and lt(dd, z)), 'strict derivative')
    for j in range(19):
        for i in range(j):
            require(lt(x[i], x[j]) or lt(x[j], x[i]), 'distinct orbit points')
    mult = iv(1)
    for j in range(10, 19):
        mult = mul(mult, mul(two, x[j]))
    require(lt(iv(1), mult) or lt(mult, iv(-1)), 'repelling period-nine orbit')
    # At the unique root, x18=-x9 and x19=x10. The disjoint
    # enclosures prove exact preperiod 10 and period 9.
    require(lt(x[9], z) and lt(z, x[18]), 'terminal symmetric endpoints')
    require(lt(iv(F(-1,32)), x[9]) and lt(x[18], iv(F(1,32))), 'terminal radius')

    # Independent f^3 expansion/Rouche test on the circle |z|=1/4.
    # G(z)=x3+4cx2 z^2+(4c^2+2x2)z^4+4cz^6+z^8.
    r = F(1,4)
    require(lt(c,z) and lt(z,x[2]), 'signs of first phases')
    cmax, cmin = abs_upper(c), F(-c[1], Q)
    x2min, x2max = F(x[2][0],Q), F(x[2][1],Q)
    leading = 4*cmin*x2min*r**2
    error = (4*cmax*cmax+2*x2max)*r**4+4*cmax*r**6+r**8
    margin = leading-error-abs_upper(x[3])-r
    require(margin > 0, 'Rouche margin for all target values')
    radii = [r,r*r,2*cmax*r*r+r**4]
    require(cmin > radii[1] and x2min > radii[2], 'no extra critical points')
    require(abs_upper(x[3]) < r, 'critical value in target disk')
    gaps = [min_gap(x[i],x[j])-radii[i]-radii[j]
            for i in range(3) for j in range(i)]
    require(min(gaps) > 0, 'three phase disk separation')

    # Invariant interval [x6,x3]: endpoints map to x9,x6; 0 maps to x3.
    # On the source disk the two intermediate factors have signs -, +
    # on the real line, so G is increasing to 0 and decreasing thereafter.
    require(lt(iv(-r),x[6]) and lt(x[3],iv(r)), 'interval in source disk')
    require(lt(x[6],x[9]) and lt(x[9],z) and lt(z,x[3]), 'interval extrema')

    # Exact dividing fixed-point isolator for G and the covering f^6(I)⊃I.
    alo, ahi = F(3,32), F(1,10)
    require(lt(iv(alo),orbit(c,3,iv(alo))[-1]), 'G(a_lo)>a_lo')
    require(lt(orbit(c,3,iv(ahi))[-1],iv(ahi)), 'G(a_hi)<a_hi')
    deriv = iv(1)
    for y in orbit(c,2,iv(alo,ahi)):
        deriv = mul(deriv,mul(two,y))
    require(lt(deriv,iv(-1)), 'unique fixed point on isolator')
    require(lt(x[6],iv(-ahi)) and lt(iv(ahi),x[3]), 'I inside invariant interval')
    # G^2(a)=a and G^2(0)=x6<-a; IVT gives [-a,a] subset G^2(I).

    # Actual period-nine real saturated component: check endpoints/phase signs.
    pairs = [(9,18),(1,10),(11,2),(12,3),(13,4),(5,14),(6,15),(16,7),(8,17)]
    phase = []
    for j,(l,h) in enumerate(pairs):
        require(lt(x[l],x[h]), 'ordered phase endpoints')
        phase.append((x[l][0],x[h][1]))
        if j:
            require(lt(x[h],iv(-ahi)) or lt(iv(ahi),x[l]), 'nonzero phase avoids I')
            require(set((l+1,h+1)) == set(pairs[(j+1)%9]), 'endpoint map')
    for i in range(9):
        for j in range(i):
            require(lt(phase[i],phase[j]) or lt(phase[j],phase[i]), 'phase intervals disjoint')
    require(all(lt(c,x[j]) for j in range(2,19)), 'other orbit values above c')
    # Phase 0 is symmetric and maps onto [c,x10]; all other phases
    # avoid 0 and their target intervals lie strictly above c.

    # Deterministic residue regression, distinct from the all-m proof.
    checked=0
    for m in range(1,513):
        seen={0}; stack=[0]
        while stack:
            a=stack.pop()
            for step in (6,9):
                b=(a+step)%m
                if b not in seen:
                    seen.add(b); stack.append(b)
        d=gcd(m,3)
        require(seen == set(range(0,m,d)), 'generated critical residues')
        require(len(seen)==m//d, 'critical count')
        checked+=1
    # Print strict rational lower floors, not floating point assertions.
    floor9=lambda v: (v.numerator*10**9)//v.denominator
    print(json.dumps({'status':'EXACT_ARITHMETIC_ONLY',
        'precision_bits':256,'root_signs':signs,'critical_preperiod':10,
        'critical_period':9,'rouche_margin_floor_times_1e9':floor9(margin),
        'phase_gap_floor_times_1e9':floor9(min(gaps)),
        'fixed_point_bracket':['3/32','1/10'],
        'residue_cases':checked,'forced_degrees':{str(m):2**(m//gcd(m,3)) for m in (1,2,3,6,9,12,18,27)},
        'scope':'arithmetic premises; written analytic and continuum arguments are separate'},sort_keys=True,indent=2))


if __name__ == '__main__':
    main()
