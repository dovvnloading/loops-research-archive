#!/usr/bin/env python3
"""Exact dyadic certificate of two nested REAL restrictive intervals.

For f_c(x)=x*x+c, certify a unique c* in a 2^-128 dyadic bracket
with f_c*^27(0)=0, exact critical period 27, and two nested, phase-
disjoint restrictive real intervals of return times 3 and 9.

Every inequality uses signed INTEGER interval arithmetic with outward
rounding at 2^-224; it is independent of numerical diagonalization,
floating point, mpmath, scipy or a nonlinear root solver. The short
analytic justification of interval invariance is in the companion note.

Does not prove complex polynomial-like renormalization, source puzzle
markings, an MLC parameter class, or K(f)=J(f).
"""
from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, localcontext

C_BITS = 128
C_K = -607890580437450502081459824019535455703
PREC = 224
UNIT = 1 << PREC


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError("invalid bounds")

    def __add__(self, b: "Interval") -> "Interval":
        return Interval(self.lo + b.lo, self.hi + b.hi)

    def __mul__(self, b: "Interval") -> "Interval":
        products = (self.lo*b.lo, self.lo*b.hi,
                    self.hi*b.lo, self.hi*b.hi)
        return Interval(min(products)//UNIT,
                        -(-max(products)//UNIT))

    def square(self) -> "Interval":
        a, b = self.lo*self.lo, self.hi*self.hi
        low = 0 if self.lo <= 0 <= self.hi else min(a, b)
        return Interval(low//UNIT, -(-max(a, b)//UNIT))

    def times(self, k: int) -> "Interval":
        assert k >= 0
        return Interval(k*self.lo, k*self.hi)

    def positive(self) -> bool:
        return self.lo > 0

    def negative(self) -> bool:
        return self.hi < 0

    def excludes_zero(self) -> bool:
        return self.positive() or self.negative()

    def below(self, b: "Interval") -> bool:
        return self.hi < b.lo

    def strictly_inside(self, b: "Interval") -> bool:
        return b.lo < self.lo and self.hi < b.hi

    def display(self, digits: int = 19) -> tuple[str, str]:
        """Display only: rounded decimals, not the certified endpoints."""
        with localcontext() as ctx:
            ctx.prec = digits+12
            return (f"{Decimal(self.lo)/Decimal(UNIT):.{digits}f}",
                    f"{Decimal(self.hi)/Decimal(UNIT):.{digits}f}")


ZERO = Interval(0, 0)
ONE = Interval(UNIT, UNIT)


def parameter(k: int) -> Interval:
    # Each 2^-128 dyadic parameter is represented EXACTLY at 2^-224.
    return Interval(k << (PREC-C_BITS), k << (PREC-C_BITS))


def iterate(initial: Interval, c: Interval, horizon: int) -> list[Interval]:
    out = [initial]
    for _ in range(horizon):
        out.append(out[-1].square()+c)
    return out


def orbit_and_derivative(c: Interval, horizon: int) -> tuple[list[Interval], list[Interval]]:
    x, d = [ZERO], [ZERO]
    for _ in range(horizon):
        # d_{j+1}=2*x_j*d_j+1; valid enclosure for every c in interval.
        d.append(x[-1]*d[-1].times(2)+ONE)
        x.append(x[-1].square()+c)
    return x, d


def disjoint(intervals: list[Interval]) -> bool:
    return all(a.below(b) or b.below(a)
               for i, a in enumerate(intervals)
               for b in intervals[i+1:])


def strictly_between(v: Interval, a: Interval, b: Interval) -> bool:
    return a.below(v) and v.below(b)


def check() -> None:
    low, high = parameter(C_K), parameter(C_K+1)
    # Exact outward-rounded signs for the two dyadic P_27 endpoints.
    assert iterate(ZERO, low, 27)[27].positive()
    assert iterate(ZERO, high, 27)[27].negative()
    C = Interval(low.lo, high.hi)
    X, D = orbit_and_derivative(C, 27)
    assert D[27].negative(), "P_27 must be strictly decreasing throughout"
    assert X[27].lo < 0 < X[27].hi
    # IVT and the derivative bound imply a UNIQUE c* in this bracket
    # with f^27(0)=0. Since 27=3^3 and P_1,P_3,P_9 are nonzero,
    # its exact critical period is 27.
    assert X[1].negative() and X[3].positive() and X[9].negative()

    # Actual endpoint values at c*: I3=[x6,x3], I9=[x9,x18].
    # X[k] enclose x_k(c*) for each k.
    assert X[6].negative() and X[18].positive()
    assert strictly_between(X[9], X[6], X[3])
    I3 = Interval(X[6].lo, X[3].hi)
    I9 = Interval(X[9].lo, X[18].hi)
    assert I9.strictly_inside(I3)

    certificates = {}
    for period, I in ((3, I3), (9, I9)):
        Y = iterate(I, C, period)
        assert disjoint(Y[:period]), ("phase collision", period)
        assert all(Y[j].excludes_zero() for j in range(1, period))
        # (f^p)'(x) = 2^p * x * product_{j=1}^{p-1} f^j(x).
        # All intermediate images omit 0, so f^p has one critical
        # point, at x=0, with sign determined by negative phases.
        negatives = sum(Y[j].negative() for j in range(1, period))
        assert all(Y[j].positive() or Y[j].negative()
                   for j in range(1, period))
        assert negatives % 2 == (1 if period == 3 else 0)
        certificates[period] = (I, Y, negatives)

    # Invariant period-3 interval:
    # f^3(0)=x3 (maximum), f^3(x3)=x6 (minimum),
    # f^3(x6)=x9 (strictly inside [x6,x3]).
    assert strictly_between(X[9], X[6], X[3])
    # Invariant period-9 interval:
    # f^9(0)=x9 (minimum), f^9(x9)=x18 (maximum),
    # f^9(x18)=x27=0 (inside [x9,x18]).
    assert X[9].negative() and X[18].positive()

    # For the return g=f^3, intermediate g(I9),g^2(I9) stay in
    # I3: their extrema arise at 0 and at x9,x18. The orbit
    # identities give f^j(x9)=x_(9+j), f^j(x18)=x_(18+j).
    # At j=3,6 the images of these points fit in I3; j=3 and
    # j=6 have no extra critical points as stages j'=1..j-1
    # of I9 exclude zero.
    for j in (3, 6):
        for k in (j, 9+j, 18+j):
            assert k == 6 or X[6].below(X[k]), ("lower", j, k)
            assert k == 3 or X[k].below(X[3]), ("upper", j, k)

    print("PASS: exact dyadic two-scale real restrictive-interval certificate")
    print(f"  parameter bracket = [{C_K}/2^{C_BITS}, {C_K+1}/2^{C_BITS}]")
    print("  sign(P27(lower))=+, sign(P27(upper))=-; P27'(c)<0 throughout")
    print("  exact critical period = 27; P1,P3,P9 never vanish in bracket")
    for period, (I, Y, neg) in certificates.items():
        print(f"  I{period} display endpoints (rounded) = {I.display()}")
        print(f"  f^0...f^{period-1}(I{period}) pairwise disjoint; negative stages={neg}")
        print(f"  verified return: f^{period}(I{period})=I{period} (see endpoint proof)")
        if period == 9:
            print("  I9 is strictly inside I3; f^3(I9) and f^6(I9) lie in I3")
    print("LIMIT: real restrictive intervals; complex puzzle and MLC gates remain open")


if __name__ == "__main__":
    check()
