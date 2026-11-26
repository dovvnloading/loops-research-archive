#!/usr/bin/env python3
"""Exact rational regression for midpoint trace reduction; not a proof of realization."""
from fractions import Fraction as F
from itertools import product
import json


def main():
    modes = 0
    for rho in (F(1, 2), F(1, 3), F(1, 10), F(3, 5), F(1, 1024)):
        bound = ((1 + rho) / (1 - rho)) ** 2
        one = 1 + 2 * rho / (1 + rho * rho)
        for n in range(1, 13):
            t = rho ** n
            c = (1 + t*t) / (1 - t*t)
            s = 2*t / (1 - t*t)
            h = (1+t) / (1-t)
            assert h == c+s and c*c-s*s == 1
            assert h/(c-s) == h*h <= bound
            assert h/c == 1 + 2*t/(1+t*t) <= one
            assert n*s <= 2*rho/(1-rho*rho)
            for a, b in product(range(-3, 4), repeat=2):
                full = n*(c*(a*a+b*b)-2*s*a*b)
                cut = n*h*(a*a+b*b)
                assert cut-full == n*s*(a+b)**2
                assert 0 <= full <= cut <= bound*full
                if b == 0:
                    assert cut <= one*full
                if n == 1 and a == b:
                    assert cut == bound*full
                if a == -b:
                    assert cut == full
                modes += 1
    # Popoviciu variance bound used after Parseval; finite vectors are diagnostics.
    variance_tests = 0
    for values in product(range(5), repeat=4):
        mean = F(sum(values), len(values))
        var = sum((v-mean)**2 for v in values)/len(values)
        assert 4*var <= (max(values)-min(values))**2
        variance_tests += 1
    # Scalar elimination: exact response for an inner one-electrode conductance.
    series_tests = 0
    for a,g,x,y in product((F(1,3),F(2),F(7)), (F(1,5),F(3),F(11)), range(-2,3), range(-2,3)):
        m = (a*y+g*x)/(a+g)
        assert a*(m-y)**2+g*(m-x)**2 == a*g/(a+g)*(x-y)**2
        series_tests += 1
    # Existing physical bounds 3/20 < R/2^p < 17/100; uniform error at p>=13.
    physical_tests = 0
    for p in range(13, 101):
        radius_lower = F(3,20)*2**p
        rho_upper = 2/radius_lower
        assert rho_upper < F(1,2)
        assert 2*rho_upper/(1+rho_upper*rho_upper) < F(1,2**(p-5))
        # Ellipse parameter s=20R+1 encloses disk R for segment half-length 1/10.
        radius = radius_lower
        s = 20*radius+1
        assert F(1,20)*(s-1/s) > radius
        physical_tests += 1
    print(json.dumps({"status":"PASS", "mode_tests":modes, "variance_tests":variance_tests,
                      "series_tests":series_tests,"physical_tests":physical_tests,
                      "scope":"exact arithmetic diagnostics, not formal proof or MLC"},indent=2))


if __name__ == '__main__':
    main()
