#!/usr/bin/env python3
"""Exact rational regressions for the scalar frontier audit, not a proof checker.

No polynomial orbit computation, external input, floating point or dependency.
The analytic theorems and native hypotheses are in the accompanying note.
"""
from fractions import Fraction as F
from itertools import product


def inv(z):
    x, y = z
    n = x*x + y*y
    assert n > 0
    return x/n, -y/n


def norm2(z):
    return z[0]**2 + z[1]**2


def solve(m, rhs):
    n = len(rhs)
    a = [list(row) + [v] for row, v in zip(m, rhs)]
    for j in range(n):
        k = next(k for k in range(j, n) if a[k][j])
        a[j], a[k] = a[k], a[j]
        pivot = a[j][j]
        a[j] = [v/pivot for v in a[j]]
        for k in range(n):
            if k != j:
                c = a[k][j]
                a[k] = [v-c*w for v,w in zip(a[k], a[j])]
    result = [row[-1] for row in a]
    assert all(sum(c*v for c,v in zip(row,result)) == b
               for row,b in zip(m,rhs))
    return result


def spike(q, d, b, targets, e):
    A = F(q*q, 2)
    rhs = [A*x+b for x in targets]
    assert all(rhs)
    ys = [x-e*(1 if t>0 else -1) for x,t in zip(targets,rhs)]
    eta = e*e
    m = [[e*(x-y)/(eta*eta+(x-y)**2) for y in ys] for x in targets]
    weights = solve(m,rhs)
    assert all(v>0 for v in weights)

    def H(X):
        x,y = X
        terms = [inv((x+eta,y-z)) for z in ys]
        return (d+A*x+sum(e*w*t[0] for w,t in zip(weights,terms)),
                b+A*y+sum(e*w*t[1] for w,t in zip(weights,terms)))

    for x in targets:
        h = H((F(0),x))
        assert h[1] == 0 and d < h[0] < d*F(101,100)
        u = inv(h)
        assert F(100,101)/d < u[0] < 1/d and u[1] == 0
    for X in [(F(1), F(0)), (F(1,2), F(3)), (F(3), F(-5))]:
        h = H(X)
        ref = (d+A*X[0],b+A*X[1])
        assert h[0] > d+A*X[0]
        u, u0 = inv(h), inv(ref)
        assert norm2((u[0]-u0[0],u[1]-u0[1])) < F(1,10**8)
        # Combined disk criterion, R_eff=1/(2(d+A Re X)).
        r = 1/(2*(d+A*X[0]))
        assert norm2((u[0]-r,u[1])) < r*r
    # The residual at X=infinity is exactly d+i*b for all epsilon.
    # Hence these two Taylor coefficients of u at lambda=1 are fixed.
    aa = 1/(2*A)
    beta_re, beta_im = (A-d)/(4*A*A), -b/(4*A*A)
    assert aa == F(1,q*q)
    assert (A-q**4*beta_re,-q**4*beta_im) == (d,b)
    # q*((q+1)/2-I) from the actual residue algebra in the note.
    I = (F(1,2)+q**3*beta_re,q**3*beta_im)
    assert (q*(F(q+1,2)-I[0]),-q*I[1]) == (d,b)
    return len(targets)


def lens_checks():
    # Rational unit-circle pairs give exact sqrt(1-h^2).
    count = 0
    for h,s in [(F(3,5),F(4,5)),(F(5,13),F(12,13)),
                (F(7,25),F(24,25)),(F(8,17),F(15,17))]:
        assert h*h+s*s == 1
        for delta,x,y in product([F(1,3),F(1),F(3)],
                                  [F(1,10),F(1),F(4),F(17)],
                                  [F(-5),F(-1),F(0),F(1),F(5)]):
            d = h/delta
            L = delta/s
            v2 = x*x+y*y
            u2 = v2/((1+d*x)**2+(d*y)**2)
            assert (u2 >= delta*delta) == ((1-h*h)*v2-2*d*delta*delta*x-delta*delta >= 0)
            assert (u2 >= delta*delta) == (v2/L**2-1 >= 2*x*h/(L*s))
            count += 1
    return count


def continuation_checks():
    count = 0
    for s,D2 in product([F(1,1000),F(1,10),F(1,2),F(1)],
                        [F(1,100),F(1,2),F(1),F(4)]):
        T = ((s/2)**2+(1-s/2)*D2)/(s-s*s/4)
        assert T <= s/3+4*D2/(3*s)
        for q in (3,9,81):
            a = F(1,q*q)
            assert 6*a*T <= 2*a*s+8*a*D2/s
            count += 1
    return count


def main():
    targets = list(map(F, [-5,-1,1,3,11]))
    count = 0
    for q,b in product((3,9,81), (F(0),F(7,3))):
        count += spike(q,F(5,2),b,targets,F(1,10**8))
    print(f'{count} simultaneous spike targets; {lens_checks()} lens equivalences; '
          f'{continuation_checks()} continuation inequalities; exact rational checks passed')


if __name__ == '__main__':
    main()
