"""Exact arithmetic regression for RANK_ONE.md and SPECTRAL.md.

The all-period source's analytic estimates (14), (16), (17) are inputs;
this checker does not reprove them or the analytic response identities.
"""
from fractions import Fraction as F


def square(a, b):
    return (F(0) if a <= 0 <= b else min(a*a, b*b), max(a*a, b*b))


def orbit_enclosures():
    q = F(1, 4**13)
    E = [F(0)]
    for _ in range(6):
        E.append(4*E[-1] + 88*q)
    assert E[6] + E[3] == 121968*q
    left, right = F(-1795, 1000), F(-1785, 1000)
    N = 1000
    bounds = [(F(100), F(-100)) for _ in range(6)]
    for i in range(N):
        a, b = left+(right-left)*i/N, left+(right-left)*(i+1)/N
        l = h = F(0)
        for j in range(1, 7):
            l, h = square(l, h)
            l, h = l+a, h+b
            old_l, old_h = bounds[j-1]
            bounds[j-1] = min(old_l, l-E[j]), max(old_h, h+E[j])
    advertised = [(-1796,-1784), (1400,1428), (170,250),
                  (-1754,-1736), (1220,1290), (-306,-122)]
    for (lo, hi), (a,b) in zip(bounds, advertised):
        assert F(a,1000) < lo <= hi < F(b,1000)
    # K0 = [-w3,w3], K1 = [-w4,-w1], K2 = [-w2,-w5].
    # w6 = -w3 at the root, from the source (not interval arithmetic).
    ell = F(1,40)
    assert 2*F(170,1000) > ell
    assert F(1784-1754,1000) > ell
    assert F(1400-1290,1000) > ell
    assert F(1220-250,1000) > ell
    assert F(1736-250,1000) > ell
    assert F(1800-1796,1000) > 0
    print('1000 interval cells: uniform six-orbit enclosures, lengths and gaps passed')


def fourier_and_schur():
    count = 0
    for den in range(2, 19):
        for num in range(1,den):
            t = F(num,den)
            for n in range(1,13):
                cn = (1+t**(2*n))/(1-t**(2*n))
                c1 = (1+t*t)/(1-t*t)
                assert 1 < cn <= c1 and c1-1 == 2*t*t/(1-t*t)
                count += 1
    print(f'{count} rational Fourier-factor cases passed')
    count = 0
    for beta in (F(1,100), F(1,3), F(1), F(9), F(100)):
        for k in (F(1,100), F(1,2), F(1), F(3), F(20)):
            for x in range(-2,3):
                for m in range(-2,3):
                    s = (beta*m+k*x)/(beta+k)
                    c = beta*k/(beta+k)
                    assert beta*(s-m)**2 + k*(x-s)**2 == c*(x-m)**2
                    for d in (F(-3,7), F(0), F(4,5)):
                        assert beta*(s+d-m)**2 + k*(x-s-d)**2 == c*(x-m)**2 + (beta+k)*d*d
                    count += 1
    print(f'{count} rational scalar Schur-complement cases passed')


if __name__ == '__main__':
    orbit_enclosures()
    fourier_and_schur()
