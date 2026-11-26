from fractions import Fraction as F
from itertools import product
from math import prod
import json


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    corners = [x*y for x in a for y in b]
    return min(corners), max(corners)


def sq(a):
    lo, hi = a
    return (F(0) if lo <= 0 <= hi else min(lo*lo, hi*hi), max(lo*lo, hi*hi))


def orbit(c):
    x = [(F(0), F(0))]
    d = [(F(0), F(0))]
    for _ in range(6):
        d.append(add(mul((F(2), F(2)), mul(x[-1], d[-1])), (F(1), F(1))))
        x.append(add(sq(x[-1]), c))
    return x, d


def inside(a, lo, hi):
    assert lo < a[0] <= a[1] < hi, (a, lo, hi)


def main():
    c = F(-179033, 100000), F(-179032, 100000)
    x, d = orbit(c)
    for t, sign in zip(c, (-1, 1)):
        y, _ = orbit((t, t))
        assert sign * (y[3][0] + y[6][0]) > 0
    derivative = add(d[3], d[6])
    inside(derivative, F(11), F(13))
    boxes = [(F(-18,10), F(-179,100)), (F(14,10), F(15,10)),
             (F(1,5), F(1,4)), (F(-177,100), F(-17,10)),
             (F(6,5), F(13,10)), (F(-1,4), F(-1,5))]
    for a, (lo, hi) in zip(x[1:], boxes):
        inside(a, lo, hi)
    z1 = add((F(0), F(1,16)), c)
    z2 = add(sq(z1), c)
    assert z1[1] < -1 and z2[0] > 1
    assert 8 * F(1,5) * F(17,10) * F(6,5) > 1
    # Finite shadow of the proved address equality and degree law, not a geometry test.
    rows = []
    degrees = (2, 1, 1)
    for m in range(1, 9):
        N = 2*m
        words = list(product((0, 1), repeat=m))
        for j in range(N+1):
            k, s = divmod(j, 2)
            keys = [w[k:] if s == 0 else w[k+1:] for w in words]
            assert len(set(keys)) == 2**(m-k-s)
        for j in range(4):
            split = max(0, j-N)
            forward = prod(degrees[:split])
            projection = prod(degrees[split:j])
            assert forward*projection == prod(degrees[:j])
            if m >= 2 and j > 0:
                assert forward == 1 and projection == 2
            if m == 2:
                rows.append([j, forward, projection, 2**(m-j//2-j%2)])
    print(json.dumps({"parameter_bracket": [str(t) for t in c],
                      "endpoint_signs": [-1, 1], "derivative_bounds": [11, 13],
                      "orbit_boxes": [[str(lo), str(hi)] for lo, hi in boxes],
                      "f2_on_real_quarter_interval_gt": 1,
                      "depth_two_rows_j_forward_projection_component_count": rows,
                      "status": "exact finite arithmetic; analytic proof in NOTE.md"}, indent=2))


if __name__ == '__main__':
    main()
