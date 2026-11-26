#!/usr/bin/env python3
"""Exact outward-dyadic arithmetic for the physical 3/9 tip in NOTE.md.

No external dependencies. Does not check source puzzle geometry, topology,
prime-end realization, or native Wave completeness. Fails closed on any
unresolved interval comparison. Python 3.12 in CI.
"""
import json
from fractions import Fraction

Q = 1 << 256
N = -607918036626757496169199575185708826140
DEN = 1 << 128


def iv(lo, hi=None):
    hi = lo if hi is None else hi
    lo, hi = Fraction(lo) * Q, Fraction(hi) * Q
    return lo.numerator // lo.denominator, -((-hi.numerator) // hi.denominator)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    p = [x * y for x in a for y in b]
    return min(p) // Q, -((-max(p)) // Q)


def sq(a):
    lo = 0 if a[0] <= 0 <= a[1] else min(a[0] ** 2, a[1] ** 2)
    hi = max(a[0] ** 2, a[1] ** 2)
    return lo // Q, -((-hi) // Q)


def lt(a, b):
    return a[1] < b[0]


def require(cond, label):
    if not cond:
        raise ArithmeticError(label)


def orbit(c, n, start=(0, 0)):
    x = [start]
    for _ in range(n):
        x.append(add(sq(x[-1]), c))
    return x


def param_derivative(c, n):
    x = orbit(c, n)
    d = [iv(0)]
    for k in range(n):
        d.append(add(mul(mul(iv(2), x[k]), d[k]), iv(1)))
    return x, d


def main():
    left, right = Fraction(N, DEN), Fraction(N + 1, DEN)
    c = iv(left, right)
    xl, xr = orbit(iv(left), 18), orbit(iv(right), 18)
    fl, fr = add(xl[18], xl[9]), add(xr[18], xr[9])
    x, d = param_derivative(c, 18)
    df = add(d[18], d[9])
    require((lt(fl, iv(0)) and lt(iv(0), fr) and lt(iv(0), df)) or
            (lt(fr, iv(0)) and lt(iv(0), fl) and lt(df, iv(0))),
            "strict root signs and derivative")
    for i in range(19):
        for j in range(i):
            require(lt(x[i], x[j]) or lt(x[j], x[i]), f"distinct x{i}, x{j}")
    mult = iv(1)
    for j in range(10, 19):
        mult = mul(mult, mul(iv(2), x[j]))
    require(lt(iv(1), mult) or lt(mult, iv(-1)), "repelling 9-cycle")
    # P18+P9=0 implies x18=-x9 and x19=x10 exactly, hence period nine
    # (pairwise disjoint enclosures prove preperiod 10 and exact period 9).
    b_lo, b_hi = Fraction(3, 32), Fraction(1, 10)
    g_lo = orbit(c, 3, iv(b_lo))[-1]
    g_hi = orbit(c, 3, iv(b_hi))[-1]
    require(lt(iv(b_lo), g_lo) and lt(g_hi, iv(b_hi)), "positive dividing fixed point bracket")
    y = orbit(c, 2, iv(b_lo, b_hi))
    deriv = iv(1)
    for z in y:
        deriv = mul(deriv, mul(iv(2), z))
    require(lt(deriv, iv(-1)), "strictly decreasing repelling G on a bracket")
    require(lt(x[6], iv(-b_hi)) and lt(iv(b_hi), x[3]), "I3 contains I")
    require(lt(iv(Fraction(-1, 32)), x[9]) and lt(x[9], iv(0)), "K9 left endpoint")
    require(lt(iv(0), x[18]) and lt(x[18], iv(Fraction(1, 32))), "K9 right endpoint")
    # Every physical postcritical value except x9 and x18 misses I=[-a,a].
    hits = []
    for j in range(1, 19):
        if lt(iv(-b_lo), x[j]) and lt(x[j], iv(b_lo)):
            hits.append(j)
        else:
            require(lt(x[j], iv(-b_hi)) or lt(iv(b_hi), x[j]), f"ambiguous root hit x{j}")
    require(hits == [9, 18], "exact root shadow set")
    phase_pairs = [(9, 18), (1, 10), (11, 2), (12, 3), (13, 4),
                   (5, 14), (6, 15), (16, 7), (8, 17)]
    for j, (l, r) in enumerate(phase_pairs):
        require(lt(x[l], x[r]), f"ordered phase {j}")
        if j:
            require(lt(x[r], iv(-b_hi)) or lt(iv(b_hi), x[l]),
                    f"entire nonzero phase {j} misses I")
    # The z^2 coefficient of the physical f^9 at 0 is strictly positive.
    coeff = iv(1)
    for j in range(1, 9):
        coeff = mul(coeff, mul(iv(2), x[j]))
    require(lt(iv(0), coeff), "local four-arm critical pullback")
    # Exact recurrence derived in NOTE: a unique critical component is on
    # the central ancestry every ninth step; all other components split.
    census = {0: 1}
    counts = []
    for depth in range(1, 55):
        if depth % 9:
            census = {m: 2 * k for m, k in census.items()}
        else:
            m = depth // 9 - 1
            require(census.get(m, 0) >= 1, "central component exists")
            census = {j: 2 * k for j, k in census.items()}
            census[m] -= 2
            census[m + 1] = 1
            census = {j: k for j, k in census.items() if k}
        require(sum((1 << m) * k for m, k in census.items()) == 1 << depth,
                "total polynomial degree")
        require(sum(census.values()) == (1 << depth) - sum(1 << (depth - j) for j in range(9, depth + 1, 9)),
                "component count")
        if depth == 12:
            require(census == {0: 4080, 1: 8}, "depth-12 physical census")
        if depth % 6 == 0:
            M = depth // 9
            require(set(census) == set(range(M + 1)), "all critical counts available")
            counts.append({"depth": depth, "components_by_critical_count": census.copy(),
                           "selected_fan_degree": (1 << (M + 1)) - 1,
                           "selected_intrinsic_access_lifts": 6 * ((1 << (M + 1)) - 1)})
    result = {"status": "EXACT_ARITHMETIC_CHECKED_PARTIAL_NOT_NATIVE_VSC5",
              "precision_bits": 256, "parameter_bracket_numerator": [N, N + 1],
              "parameter_bracket_denominator_power": 128,
              "exact_critical_preperiod": 10, "exact_critical_period": 9,
              "root_postcritical_hit_indices": hits, "intrinsic_root_accesses": 6,
              "sampled_depth_censuses": counts,
              "scope": "arithmetic only; source geometry and written proof are separate"}
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
