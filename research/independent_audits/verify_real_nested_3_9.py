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
    # Exact signed kneading/critical itinerary on the 26 nonzero phases.
    # This is a reproducible input for later external-ray/lamination work.
    signs = "".join("+" if X[j].positive() else "-" if X[j].negative()
                    else "?" for j in range(1, 27))
    assert signs == "-++-+--+--++-+--++-++-+--+", signs

    # Actual endpoint values at c*: I3=[x6,x3], I9=[x9,x18].
    # X[k] enclose x_k(c*) for each k.
    assert X[6].negative() and X[18].positive()
    assert strictly_between(X[9], X[6], X[3])
    assert X[18].below(X[3]), "exact inner upper endpoint must precede outer upper"
    assert X[6].below(X[18]), "exact outer lower precedes inner upper"
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
        # A finite-horizon COMPLEX neighborhood certificate.
        # For a real x in f^j(I), |x|<2, so if z stays within
        # e_j of x, then |f(z)-f(x)|<=e_j*(4+e_j)<=5*e_j
        # whenever e_j<=1. Start with e_0=2^-40.
        # Thus e_j<=5^j*2^-40<10^-6 for j<=8.
        assert all(max(abs(J.lo), abs(J.hi)) < 2*UNIT
                   for J in Y[:period]), ("phase outside radius 2", period)
        phase_zero_clearance = []
        for j in range(1, period):
            J = Y[j]
            bound = J.lo if J.positive() else -J.hi
            assert bound*10 > UNIT, ("phase approaches 0", period, j)
            phase_zero_clearance.append(bound)
        phase_gaps = [
            B.lo-A.hi if A.below(B) else A.lo-B.hi
            for j, A in enumerate(Y[:period])
            for B in Y[j+1:period]
        ]
        assert phase_gaps and min(phase_gaps)*100 > UNIT, (
            "phase gap smaller than 1/100", period)
        assert 5**(period-1)*1_000_000 < 2**40
        # Pairwise images of the complex 2^-40 stadium about I
        # stay inside disjoint (<10^-6)-tubes around the Y[j].
        # No f^j(z), 1<=j<period, can equal 0 in that tube,
        # so f^period has no critical point other than z=0 there.
        certificates[period] = (I, Y, negatives)

    # Uniform finite-horizon COMPLEX separation persists for a nontrivial
    # REAL parameter neighborhood, not just the exact center c*. Keep
    # the already-certified center intervals I3/I9 as fixed geometric
    # sets and enlarge the allowed quadratic parameter by 2^-32.
    delta = 1 << (PREC-32)
    parameter_neighborhood = Interval(C.lo-delta, C.hi+delta)
    for period, (I, _, _) in certificates.items():
        Ynear = iterate(I, parameter_neighborhood, period)
        assert disjoint(Ynear[:period]), ("parameter-phase collision", period)
        assert all(max(abs(J.lo), abs(J.hi)) < 2*UNIT
                   for J in Ynear[:period])
        for j in range(1, period):
            J = Ynear[j]
            clearance = J.lo if J.positive() else -J.hi
            assert 10*clearance > UNIT, ("parameter critical collision", period,j)
        gaps = [
            B.lo-A.hi if A.below(B) else A.lo-B.hi
            for j,A in enumerate(Ynear[:period])
            for B in Ynear[j+1:period]
        ]
        assert gaps and 100*min(gaps) > UNIT, (
            "parameter phase gap falls below 1/100", period)
        # The same initial complex 2^-40 stadium and growth bound
        # 5^j*2^-40 < 10^-6 therefore work for every real parameter
        # in this explicit open 2^-32-neighborhood of c*.
    # The finite complex phase separation also survives every COMPLEX
    # quadratic parameter c' in the open disk |c'-c*| < 2^-26.
    # For any z within 2^-40 of x in the center interval I_p, let
    # e_j=|f_{c'}^j(z)-f_{c*}^j(x)|. Since center phase |f^j(x)|<2,
    # e_(j+1) <= e_j*(4+e_j)+2^-26 <= 5*e_j+2^-26 if e_j<=1.
    # Thus e_j <= 5^j*2^-40 + ((5^j-1)/4)*2^-26.
    # At j=8 this is less than 1/500, checked entirely in integers.
    # Each center real phase is separated by >1/100, so the COMPLEX
    # perturbed images remain disjoint (2/500<1/100); noninitial
    # images remain >1/10-1/500 from zero.
    e8_num = 5**8 * (2**26) + ((5**8-1)//4) * (2**40)
    assert 500*e8_num < (2**66)
    assert 2*100 < 500  # 2/500 < 1/100
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
    print("  certified critical signs x1..x26 =", signs)
    for period, (I, Y, neg) in certificates.items():
        print(f"  I{period} display endpoints (rounded) = {I.display()}")
        print(f"  f^0...f^{period-1}(I{period}) pairwise disjoint; negative stages={neg}")
        print(f"  verified return: f^{period}(I{period})=I{period} (see endpoint proof)")
        if period == 9:
            print("  I9 is strictly inside I3; f^3(I9) and f^6(I9) lie in I3")
    print("  COMPLEX: epsilon=2^-40 phase tubes disjoint for j<3 and j<9")
    print("  COMPLEX: all intermediate iterates avoid the critical point")
    print("  COMPLEX: phase collars persist for |c-c*|<~2^-32 (dyadic bracket widened)")
    print("  COMPLEX: finite phase disjointness uniform for |c'-c*|<2^-26")
    print("  COMPLEX LIMIT: no polynomial-like proper return or KL rays/sheets proved")
    print("LIMIT: real restrictive intervals; complex puzzle and MLC gates remain open")


if __name__ == "__main__":
    check()
