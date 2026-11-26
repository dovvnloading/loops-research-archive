"""Exact arithmetic for the real q=2, n=1 decoration counterexample.

This checks orbit isolations and angle tables, not the analytic puzzle theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt
import json

S = 1 << 256
K = -607918036626757496169199575185708826140
D = 1 << 128


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def enc(x):
    x = F(x) * S
    return x.numerator // x.denominator, -((-x.numerator) // x.denominator)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[1], -a[0]


def mul(a, b):
    p = [x * y for x in a for y in b]
    return min(p) // S, -((-max(p)) // S)


def sq(a):
    lo = 0 if a[0] <= 0 <= a[1] else min(x*x for x in a)
    hi = max(x*x for x in a)
    return lo // S, -((-hi) // S)


def sqrt(a):
    check(a[0] >= 0, 'negative radicand')
    return isqrt(a[0] * S), isqrt(a[1] * S) + 1


def inside(a, lo, hi):
    return F(a[0], S) > lo and F(a[1], S) < hi


def orbit(c):
    x, dx = enc(0), enc(0)
    xs = [x]
    ds = [dx]
    for _ in range(18):
        dx = add(mul(mul(enc(2), x), dx), enc(1))
        x = add(sq(x), c)
        xs.append(x)
        ds.append(dx)
    return xs, ds


c = (enc(F(K, D))[0], enc(F(K+1, D))[1])
left, _ = orbit(enc(F(K, D)))
right, _ = orbit(enc(F(K+1, D)))
xs, ds = orbit(c)
signs = [add(left[18], left[9]), add(right[18], right[9])]
check(signs[0][0] > 0 > signs[1][1] or signs[1][0] > 0 > signs[0][1], 'root bracket')
deriv = add(ds[18], ds[9])
check(deriv[0] > 0 or deriv[1] < 0, 'simple unique root')
for i in range(19):
    for j in range(i):
        check(xs[i][0] > xs[j][1] or xs[j][0] > xs[i][1], 'distinct orbit')
mult = enc(1)
for x in xs[10:19]:
    mult = mul(mult, mul(enc(2), x))
check(inside(mult, 3, 4), 'repelling period-nine cycle')
check(inside(c, -2, F(-3,4)), 'real parameter range')
s = sqrt(add(enc(1), mul(enc(-4), c)))
alpha = mul(enc(F(1,2)), add(enc(1), neg(s)))
beta = mul(enc(F(1,2)), add(enc(1), s))
check(inside(neg(alpha), F(7,8), 1), 'alpha prime')
check(xs[2][0] > S and xs[2][1] < beta[0], 'first escape')
# Preimage -t has f^2(-t)=alpha_prime and f^3(-t)=alpha.
u = neg(sqrt(add(neg(alpha), neg(c))))
# The negative intermediate preimage of alpha_prime is u; t^2=u-c.
t = sqrt(add(u, neg(c)))
check(inside(t, F(5,16), F(7,16)), 'inner vertices')

P = ((F(1,6), F(1,3)), (F(2,3), F(5,6)))
Q = {'L': ((F(7,24), F(1,3)), (F(2,3), F(17,24))),
     'R': ((F(1,6), F(5,24)), (F(19,24), F(5,6)))}
# Each entry is (target sector, integer lift offset) indexed by source sector.
lifts = {'L': ((0, 1), (1, 2)), 'R': ((1, 0), (0, 3))}
for a in Q:
    for i, ((lo, hi), (j, k)) in enumerate(zip(Q[a], lifts[a])):
        check((4*lo-k, 4*hi-k) == P[j], 'exact sector lift')
        check(P[i][0] <= lo < hi <= P[i][1], 'parent sector')


def upper(w):
    a, b = F(0), F(1)
    for ch in reversed(w):
        if ch == 'L':
            a, b = (a+3)/4, (b+3)/4
        else:
            a, b = (1-b)/4, (1-a)/4
    return (a+1)/6, (b+1)/6


count = 0
for m in range(11):
    last = []
    for word in product('LR', repeat=m):
        lo, hi = upper(word)
        lower = (1-hi, 1-lo)
        check(P[0][0] <= lo < hi <= P[0][1], 'upper containment')
        check(P[1][0] <= lower[0] < lower[1] <= P[1][1], 'lower containment')
        check(hi-lo == F(1,6*4**m), 'width scaling')
        if m:
            p, q = upper(word[:-1])
            check(p <= lo < hi <= q, 'nesting')
        for interval in [(lo,hi), lower]:
            a,b = (4**m*e for e in interval)
            k = a.numerator // a.denominator
            check((a-k,b-k) in P, 'iterated sector bijection')
        last.append((lo,hi))
        count += 1
    last.sort()
    check(all(a[1] < b[0] for a,b in zip(last,last[1:])), 'disjoint words')
    check(upper('L'*m) == (F(1,3)-F(1,6*4**m), F(1,3)), 'constant left address')
print(json.dumps({'parameter_bracket': [f'{K}/{D}', f'{K+1}/{D}'],
                  'root_unique': True, 'period': 9, 'preperiod': 10,
                  'q': 2, 'n': 1, 'words_checked': count,
                  'max_depth': 10, 'constant_left_angles': ['1/3','2/3'],
                  'scope': 'exact orbit and angular arithmetic only'}, sort_keys=True))
