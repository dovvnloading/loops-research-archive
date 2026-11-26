"""Exact arithmetic inputs for NOTE.md §§6 and 8; not an analytic proof."""
from fractions import Fraction as Q
import json


def require(condition, message):
    if not condition:
        raise AssertionError(message)


# Integer polynomial arithmetic in Z[c]/(c^3 + 2c^2 + 2c + 2).
def reduce_poly(poly):
    coeff = list(poly) + [0] * max(0, 3 - len(poly))
    for k in range(len(coeff) - 1, 2, -1):
        lead = coeff[k]
        for j in (1, 2, 3):
            coeff[k - j] -= 2 * lead
        coeff[k] = 0
    return tuple(coeff[:3])


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def mul(a, b):
    product = [0] * 5
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            product[i + j] += x * y
    return reduce_poly(product)


def p(x):
    return x**3 + 2*x**2 + 2*x + 2


def satellite():
    lo, hi = Q(-31, 20), Q(-77, 50)
    require(p(lo) < 0 < p(hi), "root signs")
    require(hi < -1, "negative root branch")
    # x^2+x decreases on [lo, hi].
    al, ah = hi**2 + hi, lo**2 + lo
    require(Q(1, 2) < al < ah < Q(9, 10), "interval/repelling bounds")
    require(lo < hi < -ah < 0 < al, "distinct ordered orbit labels")
    c = (0, 1, 0)
    a = add(mul(c, c), c)
    f = lambda z: add(mul(z, z), c)
    require(f((0, 0, 0)) == c, "f(0)")
    require(f(c) == a, "f(c)")
    require(f(a) == f(neg(a)) == neg(a), "fixed -a")
    require(mul(a, a) == add(neg(a), neg(c)), "a^2=-a-c")
    require(mul(c, c) == add(a, neg(c)), "c^2=a-c")
    # The positive-real-part sqrt of w-c has real part >=
    # sqrt(Re(w-c)); for |w|<=1 the lower bound exceeds 7/10.
    re_lower = -hi - 1
    require(re_lower > Q(7, 10)**2, "negative branch real part")
    radial_bound = (1 + Q(9, 10)) / (-hi + Q(7, 10))
    r = Q(7, 8)
    require(radial_bound == Q(95, 112) < r < 1, "cyclic collar margin")
    require(ah**2 < r, "central H0 contained in A0")
    require(-hi > 1 and hi**2 > r, "obstacle exclusion")
    return {
        "parameter_bracket": [str(lo), str(hi)],
        "endpoint_sign_values": [str(p(lo)), str(p(hi))],
        "a_bounds": [str(al), str(ah)],
        "mod_p_orbit_identities": "verified",
        "repelling_multiplier_lower": str(2*al),
        "negative_branch_radial_bound": str(radial_bound),
        "strict_margin": str(r-radial_bound),
        "degree_word": [2, 1],
        "critical_value_retained": True,
    }


def chebyshev():
    R, r0, r1 = Q(3, 2), Q(7, 5), Q(49, 25)
    require(r0 < R and r0**2 == r1, "quadratic compact collar")
    require(2 - R > 0, "right half-plane sqrt")
    estimate = (R + 2) / 2
    require(estimate < r1, "univalent collar")
    # f(-2)=2, outside the closed target D(0,R).
    require(2 > R, "critical value strictly omitted")
    # The test point -sqrt(2) in A1 satisfies w+2>0.
    require(2**2 > 2, "positive square-root branch anchor")
    return {
        "target_radii": [str(R), str(r1)],
        "source_radius_0": str(r0),
        "univalent_radial_bound": str(estimate),
        "strict_margin": str(r1-estimate),
        "critical_value_image_outside_target_margin": str(2-R),
        "degree_word": [2, 1],
        "selected_base_change_degrees": [1, 1],
        "critical_value_retained": False,
    }


if __name__ == "__main__":
    print(json.dumps({
        "status": "exact arithmetic checks; analytic deductions in NOTE.md",
        "satellite": satellite(),
        "chebyshev": chebyshev(),
    }, indent=2, sort_keys=True))
