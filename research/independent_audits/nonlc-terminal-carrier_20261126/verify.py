"""Exact arithmetic regression at the archive's actual 3/9 Misiurewicz tip.
Not a machine proof of the continuum/lamination theorem in NOTE.md.
"""
from fractions import Fraction as Q
from math import isqrt

S = 1 << 256
K = -607918036626757496169199575185708826140


def ceil_div(a, b):
    return -((-a) // b)


class I:
    def __init__(self, lo, hi=None):
        lo, hi = Q(lo), Q(lo if hi is None else hi)
        assert lo <= hi
        self.a = (lo.numerator * S) // lo.denominator
        self.b = ceil_div(hi.numerator * S, hi.denominator)

    @classmethod
    def raw(cls, a, b):
        obj = cls.__new__(cls)
        assert a <= b
        obj.a, obj.b = a, b
        return obj

    def __add__(self, other):
        return I.raw(self.a + other.a, self.b + other.b)

    def __neg__(self):
        return I.raw(-self.b, -self.a)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        v = [x * y for x in (self.a, self.b) for y in (other.a, other.b)]
        return I.raw(min(v) // S, ceil_div(max(v), S))

    def sqrt(self):
        assert self.a >= 0
        return I.raw(isqrt(self.a * S), isqrt(self.b * S) + 1)

    def absmax(self):
        return Q(max(abs(self.a), abs(self.b)), S)

    def absmin(self):
        return Q(0 if self.a <= 0 <= self.b else min(abs(self.a), abs(self.b)), S)

    def strictly_below(self, other):
        return self.b < other.a


def orbit(c, n):
    x, d = [I(0)], [I(0)]
    for _ in range(n):
        d.append(I(2) * x[-1] * d[-1] + I(1))
        x.append(x[-1] * x[-1] + c)
    return x, d


def main():
    lo, hi = Q(K, 1 << 128), Q(K + 1, 1 << 128)
    for endpoint, positive in [(lo, True), (hi, False)]:
        x, _ = orbit(I(endpoint), 18)
        g = x[18] + x[9]
        assert (g.a > 0 if positive else g.b < 0)
    c = I(lo, hi)
    x, d = orbit(c, 18)
    dg = d[18] + d[9]
    assert I(-71).strictly_below(dg) and dg.strictly_below(I(-70))
    for j in range(19):
        for k in range(j):
            assert x[j].strictly_below(x[k]) or x[k].strictly_below(x[j])
    m = I(1)
    for j in range(10, 19):
        m = m * I(2) * x[j]
    assert I(3).strictly_below(m) and m.strictly_below(I(4))

    # Fixed points and actual positive preimages of the dividing fixed point.
    delta = (I(1) - I(4) * c).sqrt()
    alpha = (I(1) - delta) * I(Q(1, 2))
    beta = (I(1) + delta) * I(Q(1, 2))
    a1 = -alpha
    a2 = (a1 - c).sqrt()
    assert alpha.strictly_below(I(0)) and I(0).strictly_below(a1)
    assert a1.strictly_below(a2) and a2.strictly_below(beta)
    assert I(1).strictly_below(I(2) * a1)

    # Enclose actual f^j(D(0,1/4)) by disks via the direct recurrence.
    # |f(z)-f(w)| <= 2|w|r+r^2 for |z-w|<=r.
    radii = [Q(1, 4)]
    for j in range(2):
        rr = 2 * x[j].absmax() * radii[-1] + radii[-1] ** 2
        radii.append(Q(ceil_div(rr.numerator * S, rr.denominator), S))
    bands = [I.raw(xj.a - int(r*S), xj.b + int(r*S)) for xj, r in zip(x, radii)]
    assert bands[1].strictly_below(alpha)
    for j in (0, 2):
        assert alpha.strictly_below(bands[j])
        assert bands[j].strictly_below(a2)
    for band in bands:
        assert band.strictly_below(beta)
    # The full complex disks, not just their real traces, are disjoint.
    for j in range(3):
        for k in range(j):
            assert bands[j].strictly_below(bands[k]) or bands[k].strictly_below(bands[j])
    # Negative control: the weaker first positive preimage is inside a
    # range below the second phase centre, not beyond the entire cycle.
    assert a1.strictly_below(x[2])
    print('PASS: exact root, preperiod/period, multiplier, fixed and preimage ordering, phase disk bounds')
    print('LIMIT: no computation of non-LC fibers, prime-end markings, or Wave geometry')


if __name__ == '__main__':
    main()
