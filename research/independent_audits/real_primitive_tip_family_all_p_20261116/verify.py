#!/usr/bin/env python3
"""Read-only exact arithmetic checks for the large-p real tip lemma.

The universal quantifier is proved in NOTE.md by recurrences and monotonicity;
this script checks all fixed rational boundary inequalities at p0=13,
model-transversality and strict cut separation, plus an independent p=13 root.
No floating point or third-party dependency is used.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q

P0 = 13
q = Q(1, 4**P0)
t0, t1 = Q(-1795, 1000), Q(-1785, 1000)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


@dataclass(frozen=True)
class Iv:
    lo: Q
    hi: Q

    def __post_init__(self) -> None:
        require(self.lo <= self.hi, 'reversed interval')

    @classmethod
    def point(cls, x: Q | int) -> 'Iv':
        return cls(Q(x), Q(x))

    def __add__(self, other: 'Iv') -> 'Iv':
        return Iv(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> 'Iv':
        return Iv(-self.hi, -self.lo)

    def __sub__(self, other: 'Iv') -> 'Iv':
        return self + -other

    def __mul__(self, other: 'Iv') -> 'Iv':
        vals = (self.lo*other.lo, self.lo*other.hi,
                self.hi*other.lo, self.hi*other.hi)
        return Iv(min(vals), max(vals))

    def square(self) -> 'Iv':
        return Iv(Q(0) if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2),
                  max(self.lo**2, self.hi**2))

    def wider(self, radius: Q) -> 'Iv':
        return Iv(self.lo-radius, self.hi+radius)


def model(lo: Q, hi: Q) -> tuple[list[Iv], list[Iv]]:
    t = Iv(lo, hi)
    u, v = [Iv.point(0)], [Iv.point(0)]
    for _ in range(6):
        v.append(Iv.point(1) + Iv.point(2)*u[-1]*v[-1])
        u.append(u[-1].square() + t)
    return u, v


def atan_interval_remainder(x: Q, n: int = 10) -> Iv:
    # Alternating series: even number of terms underestimates, odd overestimates.
    require(n % 2 == 0 and 0 < x < 1, 'atan preconditions')
    s = sum(((-1)**k)*x**(2*k+1)/Q(2*k+1) for k in range(n))
    return Iv(s, s + x**(2*n+1)/Q(2*n+1))


def verify_universal_constants() -> dict[str, str]:
    a = atan_interval_remainder(Q(1, 5))
    b = atan_interval_remainder(Q(1, 239))
    pi = Iv.point(16)*a - Iv.point(4)*b  # Machin's formula
    require(Q(157, 50) < pi.lo and pi.hi < Q(22, 7), 'Archimedes bounds')
    require(Q(314159, 100000) < pi.lo and pi.hi < Q(314160, 100000), 'pi enclosure')

    eps = 16*q
    require(eps < Q(1, 4_000_000), 'epsilon upper bound')
    require(P0*eps < Q(1, 300_000), 'p*epsilon decays from p=13')
    require(P0*P0*eps < Q(1, 20_000), 'p^2*epsilon decays from p=13')
    require(Q(38, 25)**2 < Q(7, 3) and Q(8, 3) < Q(41, 25)**2,
            'initial angle bounds')
    require((Q(41, 25)-Q(157, 100)) <= Q(7, 100), 'sin lower bound: right side')
    require(Q(11, 7)-Q(38, 25) < Q(7, 100), 'sin lower bound: left side')
    require(1-Q(7, 100)**2/2 > Q(99, 100), 'sin on [1.52,1.64]')
    require(2-Q(41, 50)**2-eps/2 > Q(13, 10), 'positive intermediate orbit')
    require(Q(41, 50)**2 < Q(7, 10), 'logistic orbit upper bound')

    # Exact endpoints of epsilon-interval cross the x_p=0 target.
    require(Q(7, 3) < Q(77, 50)**2 and Q(81, 50)**2 < Q(8, 3),
            'endpoint phase separation')
    left_angle = Q(3, 100)
    right_angle = Q(81, 50)-Q(11, 7)
    left_sin_lower = left_angle-left_angle**3/6
    right_sin_lower = right_angle-right_angle**3/6
    require(2*left_sin_lower-3*P0*eps > Q(1, 20), 'positive center bracket')
    require(2*right_sin_lower-3*P0*eps > Q(1, 20), 'negative center bracket')

    # A_p q bounds: product cosine comparison and doubling identity.
    b_lower = (4-2*eps)/16 * (Q(99, 100)/Q(41, 25)) * (1-P0*eps)
    b_upper = Q(1, 4)*Q(25, 38)*(1+3*eps)*(1+3*P0**2*eps)
    require(b_lower > Q(3, 20), 'coefficient B lower bound')
    require(b_upper < Q(17, 100), 'coefficient B upper bound')

    require(Q(3, 400)-Q(14, 48)*q > Q(7, 1000), 't parameter transversality')
    require(Q(200_000, 7)*q*q < 30_000*q*q, 'error parameter derivative')
    require(256*q < 1, 'Taylor disk normalized size')
    require((Q(4, 128)+(Q(1, 4)+Q(1, 512))**2) < Q(16, 128),
            'Taylor remainder induction')
    require((Q(2, 3*128)+Q(4, 128)
             +2*(Q(1, 4)+Q(1, 512))*(Q(1, 48)+Q(1, 512))) < Q(64, 128),
            'parameter derivative remainder induction')
    margin = Q(3, 20)-12*q-Q(1, 128)-Q(1, 2**P0)
    require(margin > Q(1, 25), 'uniform Rouché margin')
    return {'pi_lower': str(pi.lo), 'pi_upper': str(pi.hi),
            'B_lower': str(b_lower), 'B_upper': str(b_upper),
            'Rouche_margin_lower_at_13': str(margin),
            'epsilon_leading_term': '(3*pi^2/2)*4^(-p)',
            'epsilon_error': '500*p*16^(-p)'}


def verify_model_and_cut_order() -> dict[str, str]:
    u, du = model(t0, t1)
    require(all(-Q(9, 5) < z.lo and z.hi < Q(9, 5) for z in u),
            'quadratic model escapes [-1.8,1.8]')
    require(all(-25 < z.lo and z.hi < 25 for z in du[:6]),
            'quadratic model derivative >25')
    require((du[6]+du[3]).lo > 2, 'quadratic model P1 transversality')
    lo, _ = model(t0, t0)
    hi, _ = model(t1, t1)
    require((lo[6]+lo[3]).hi < -Q(1, 20), 'left endpoint P1 sign')
    require((hi[6]+hi[3]).lo > Q(1, 20), 'right endpoint P1 sign')

    E, D = [Q(0)], [Q(0)]
    for _ in range(6):
        D.append(4*D[-1]+25*(2*E[-1]+171*q)+30_000*q*q)
        E.append(4*E[-1]+88*q)
    require(E[6]+E[3] < Q(1, 500), 'sign perturbation too large')
    require(D[6]+D[3] < Q(1, 5), 'derivative perturbation too large')
    require(E[6] < Q(1, 10), 'chart orbit left 1.9 disk')

    # At the real tip: v6=-v3, w_alpha in (-1,-4/5).
    # Multiplication by A<0 reverses the strict source order.
    w = {j: u[j].wider(E[j]) for j in (1, 2, 3, 4, 5)}
    alpha = Iv(-Q(1), -Q(4, 5))
    reversed_cuts = [-w[1], -w[4], w[2], w[5], -alpha,
                     w[3], -w[3], alpha, -w[5], -w[2], w[4], w[1]]
    for i in range(len(reversed_cuts)-1):
        require(reversed_cuts[i].lo > reversed_cuts[i+1].hi,
                f'non-strict source cut gap index {i}')
    require(t0+2 > 88*q and t1+Q(36, 25) < -88*q,
            'fixed point signs at -1 and -4/5')
    return {'P1_derivative_lower': str((du[6]+du[3]).lo),
            'model_sign_left': str((lo[6]+lo[3]).hi),
            'model_sign_right': str((hi[6]+hi[3]).lo),
            'model_error_E6': str(E[6]), 'model_derivative_error_D6': str(D[6]),
            'strict_source_cut_count': str(len(reversed_cuts))}


def verify_whole_kneading_window() -> dict[str, str]:
    """Rule out every other root in -2 <= t < 0 with prescribed signs.

    The broad orbit comparison uses |model orbit|<=2 from its invariant real
    interval, |perturbed orbit|<2.1 and a 4.2 Lipschitz envelope.  The root
    near -1.75488 is the period-three *center* and is excluded by x_3p<0.
    """
    wide = [Q(0)]
    for _ in range(6):
        wide.append(Q(21, 5)*wide[-1]+88*q)
    require(wide[6]+wide[3] < Q(1, 400), 'whole-window model sign uncertainty')
    require(wide[6] < Q(1, 10), 'whole-window orbit leaves 2.1 chart')

    excluded = [
        ('-2', '-1.989'), ('-1.988', '-1.982'),
        ('-1.980', '-1.894'), ('-1.892', '-1.795'),
        ('-1.785', '-1.756'), ('-1.753', '-0.01'),
    ]
    for left, right in excluded:
        a, b = Q(left), Q(right)
        # Every subinterval uses exact rational interval polynomial evaluation.
        for i in range(1000):
            lo = a+(b-a)*i/1000
            hi = a+(b-a)*(i+1)/1000
            u, _ = model(lo, hi)
            value = u[6]+u[3]
            require(value.lo > Q(1, 400) or value.hi < -Q(1, 400),
                    f'whole-window unexcluded model root {left},{right}, cell {i}')

    # Non-target Q-polynomial zeros have the wrong G-return signs.
    bad_windows = [
        ('-1.989', '-1.988', 4, '+'),
        ('-1.982', '-1.980', 5, '-'),
        ('-1.894', '-1.892', 5, '-'),
    ]
    for left, right, k, sign in bad_windows:
        u, _ = model(Q(left), Q(right))
        v = u[k].wider(wide[k])
        require(v.lo > 0 if sign == '+' else v.hi < 0,
                f'non-target root has allowed sign {left},{right}')

    # In the center window, P=H^3(v)+v = v*(2+int_0^1 (H^3)'(sv)ds),
    # where H is h_t and v=H^3(0).  The factor is strictly positive.
    u, _ = model(Q('-1.756'), Q('-1.753'))
    center_v = u[3].wider(wide[3])
    require(-Q(1, 40) < center_v.lo and center_v.hi < Q(1, 40),
            'period-three center chart')
    require((Q(1, 20)+256*q)*(Q(18, 5)+256*q)*(3+256*q) < 1,
            'center factor may vanish')

    # In the final t<0 window, h_t(t)=t(1+t)+e_t(t)<0, whereas
    # x_2p<0 needs h_t^2(0)>0 (because A_p<0).  e(0)=O(t^4) by Schwarz.
    require(88*q*Q(5, 12)**4*Q(1, 100)**3 < Q(1, 100),
            'Schwarz-order-four exclusion near t=0')
    return {'broad_interval': '[-2,0)',
            'rational_nonroot_segments': str(len(excluded)),
            'wrong_kneading_windows': str(len(bad_windows)),
            'remaining_extra_root': 'G^3(0)=0 (excluded by strict sign)'}


# Independent endpoint signs for a p=13 adjacent 2^-256 bracket, with outward
# grid rounding. This is a regression, not the source of the all-p induction.
S = 1 << 512
N13 = -231584152930559666515303967650834348256481862329075540046349754537259200892081


@dataclass(frozen=True)
class Grid:
    lo: int
    hi: int

    @staticmethod
    def exact(x: Q | int) -> 'Grid':
        z = Q(x)*S
        return Grid(z.numerator//z.denominator, -((-z.numerator)//z.denominator))

    def __add__(self, b: 'Grid') -> 'Grid':
        return Grid(self.lo+b.lo, self.hi+b.hi)

    def __neg__(self) -> 'Grid':
        return Grid(-self.hi, -self.lo)

    def __mul__(self, b: 'Grid') -> 'Grid':
        v = (self.lo*b.lo, self.lo*b.hi, self.hi*b.lo, self.hi*b.hi)
        return Grid(min(v)//S, -((-max(v))//S))

    def square(self) -> 'Grid':
        z = 0 if self.lo <= 0 <= self.hi else min(self.lo*self.lo, self.hi*self.hi)
        return Grid(z//S, -((-max(self.lo*self.lo, self.hi*self.hi))//S))


def P13_on(c: Grid) -> tuple[Grid, Grid, Grid]:
    x, d = Grid.exact(0), Grid.exact(0)
    x3 = dx3 = None
    for j in range(1, 79):
        d = Grid.exact(2)*x*d+Grid.exact(1)
        x = x.square()+c
        if j == 39:
            x3, dx3 = x, d
    assert x3 is not None and dx3 is not None
    return x+x3, d+dx3, x3


def P13_at(n: int) -> tuple[Grid, Grid, Grid]:
    return P13_on(Grid.exact(Q(n, 2**256)))


def verify_period13_bracket() -> dict[str, str]:
    left, dl, xl = P13_at(N13)
    right, dr, xr = P13_at(N13+1)
    hull = Grid(N13 << 256, (N13+1) << 256)
    contains, derivative, x3 = P13_on(hull)
    require(left.lo > 0 and right.hi < 0, 'p13 adjacent bracket P signs')
    require(dl.hi < 0 and dr.hi < 0, 'p13 endpoint derivative signs')
    require(xl.hi < 0 and xr.hi < 0, 'p13 required negative x3p')
    require(contains.lo < 0 < contains.hi, 'p13 hull does not contain zero')
    require(derivative.hi < 0, 'p13 full-hull derivative sign')
    require(x3.hi < 0, 'p13 full-hull negative x3p')
    return {'parameter_lower_numerator': str(N13),
            'parameter_upper_numerator': str(N13+1),
            'denominator_power_of_two': '256'}


def main() -> None:
    import json
    print(json.dumps({'universal': verify_universal_constants(),
                      'quadratic_model': verify_model_and_cut_order(),
                      'whole_window': verify_whole_kneading_window(),
                      'p13': verify_period13_bracket()}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
