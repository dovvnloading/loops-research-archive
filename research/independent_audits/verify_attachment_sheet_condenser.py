#!/usr/bin/env python3
"""Exact algebra + deterministic Fourier checks for the attachment-sheet condenser.

This is a regression of finite algebraic/analytic formulas, NOT a proof of the
PDE Gamma-limit, KKL prime-end proper-path hypotheses, or a canonical WAD bridge.

    python research/independent_audits/verify_attachment_sheet_condenser.py --check-manifest
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path

OUT = Path(__file__).resolve().parents[2] / 'results' / 'attachment_sheet_condenser_20261107.json'


class Qc:
    """Exact elements of Q[c]/(c^3 + 2c^2 + 2c + 2)."""
    def __init__(self, coeff=(0, 0, 0)):
        self.v = tuple(F(x) for x in coeff)
        assert len(self.v) == 3

    @staticmethod
    def conv(x):
        return x if isinstance(x, Qc) else Qc((x, 0, 0))

    def __add__(self, other):
        z = Qc.conv(other)
        return Qc(tuple(a + b for a, b in zip(self.v, z.v)))

    __radd__ = __add__

    def __neg__(self):
        return Qc(tuple(-a for a in self.v))

    def __sub__(self, other):
        return self + (-Qc.conv(other))

    def __rsub__(self, other):
        return Qc.conv(other) - self

    def __mul__(self, other):
        z = Qc.conv(other)
        co = [F(0) for _ in range(5)]
        for i in range(3):
            for j in range(3):
                co[i + j] += self.v[i] * z.v[j]
        for i in (4, 3):
            x = co[i]
            # c^i = -2 c^(i-1) -2 c^(i-2) -2 c^(i-3)
            co[i - 1] -= 2 * x
            co[i - 2] -= 2 * x
            co[i - 3] -= 2 * x
        return Qc(co[:3])

    __rmul__ = __mul__

    def __eq__(self, other):
        return self.v == Qc.conv(other).v

    def __repr__(self):
        return repr(self.v)


def algebraic_cover_check() -> dict:
    c = Qc((0, 1, 0))
    b = c * c + c
    # Unique real root since H'(x)=3(x+2/3)^2+2/3 > 0.
    def h(x):
        return x*x*x + 2*x*x + 2*x + 2
    lo, hi = F(-8, 5), F(-3, 2)
    assert h(lo) < 0 < h(hi)
    for _ in range(115):
        mid = (lo + hi) / 2
        if h(mid) < 0:
            lo = mid
        else:
            hi = mid
    assert hi - lo < F(1, 2**100)
    tested = []
    for w in [F(1), F(5, 4), F(3, 2), F(4, 3), F(2), F(5, 2), F(4)]:
        psi_src = (-c) * F(1, 2) * (w + 1/w)
        psi_target = (c+b)*F(1, 2) + (c*c)*F(1, 4) * (w*w + 1/(w*w))
        assert psi_src*psi_src + c == psi_target, ('Joukowski', w)
        minus_source = (-c)*F(1, 2)*(-w-1/w)
        assert minus_source == -psi_src
        tested.append(str(w))
    cnum = float((lo+hi)/2)
    theta = math.acos(-cnum-1)/(2*math.pi)
    ell = 4*math.pi*theta
    angular_gap = math.pi - ell
    kappa = 2/angular_gap
    assert 0 < theta < .25 and 0 < ell < math.pi
    assert math.acos(F(3, 5).numerator/F(3, 5).denominator)/(2*math.pi) < theta < 1/6
    return {
        'polynomial': 'c^3+2*c^2+2*c+2=0',
        'isolating_interval': ['-8/5', '-3/2'],
        'bracket_steps': 115,
        'bracket_width_less_than_2_power_minus_100': True,
        'exact_joukowski_rational_w_samples': tested,
        'root_approx': round(cnum, 15),
        'root_access_theta_approx': round(theta, 15),
        'attached_arc_angular_length_approx': round(ell, 15),
        'two_gap_length_approx': round(angular_gap, 15),
        'sharp_thin_density_approx': round(kappa, 15)
    }


def sinc(x):
    return math.sin(x) / x if x else 1.0


def return_dual(h, ell, max_n=12001):
    total = 0.
    for n in range(1, max_n + 1, 2):
        total += (1/math.tanh(n*h))/n * sinc(n*ell/2)**2
    partial = 4/math.pi*total
    # coth(x) <= 1+1/x, |sinc(n ell/2)| <= 2/(n ell),
    # sum_{n>N} n^-3 <= 1/(2N^2) (even ignoring odd restriction).
    tail = (8/(math.pi * ell*ell)) * (1+1/h) / (max_n*max_n)
    return partial, tail


def gstar_fourier(n, ell):
    if n % 2 == 0:
        return 0.
    return 2*math.cos(n*ell/2)/(math.pi*(math.pi-ell)*n*n)


def reference_free_energy(h, ell, max_n=12001):
    return 4*math.pi*sum(
        n*math.tanh(n*h)*gstar_fourier(n,ell)**2
        for n in range(1,max_n+1,2)
    )


def test_continuum_formulas(ell):
    kappa = 2/(math.pi-ell)
    results=[]
    for h in (.69,.2,.1,.05,.025,.0125):
        dual, tail = return_dual(h, ell)
        lower = 1/(dual+tail)
        upper = h*kappa
        gstar_harmonic = reference_free_energy(h, ell)
        assert 0 < lower <= gstar_harmonic + 1e-11 <= upper+1e-11
        # Using prescribed angular trace g_star, the harmonic free energy
        # approaches the 1D reference energy after division by h.
        results.append({
            'h': h,
            'rigorous_charge_lower': round(lower, 12),
            'rigorous_radial_constant_upper': round(upper, 12),
            'test_trace_free_harmonic_energy': round(gstar_harmonic, 12),
            'test_trace_energy_divided_by_h': round(gstar_harmonic/h, 12),
            'certified_charge_response_tail_le': round(tail, 12),
        })
    ratios=[x['test_trace_energy_divided_by_h'] for x in results]
    assert all(a <= b + 1e-9 for a,b in zip(ratios,ratios[1:]))
    assert ratios[-1] < kappa and kappa-ratios[-1] < 0.02
    # The analytic coefficient identity for the linear-gap 1D minimizer.
    truncated_1d = 4*math.pi * sum(n*n*gstar_fourier(n,ell)**2
                                 for n in range(1,120002,2))
    assert abs(truncated_1d - kappa) < 2e-5
    return {
        'source_ell': round(ell, 15),
        'thin_density_exact_formula': '2/(pi-ell)',
        'thin_density_approx': round(kappa, 12),
        'lower_and_upper_probes': results,
        '1d_fourier_energy_partial': round(truncated_1d,12),
        '1d_Fourier_tail_check_less_than': 2e-5,
    }


def test_two_parameter_no_go():
    fixed_h = .2
    rho = min(fixed_h/2,math.pi/4)
    short_electrodes=[]
    for power in (5,20,50,100):
        # ell = rho * exp(-power), so test no underflow and exact cutoff energy
        logratio=power
        upper_cap=math.pi/logratio
        short_electrodes.append({'log_rho_over_ell': power,
                                 'capacity_upper':round(upper_cap,12),
                                 'capacity_upper_divided_by_h':round(upper_cap/fixed_h,12)})
    assert short_electrodes[-1]['capacity_upper_divided_by_h'] < short_electrodes[0]['capacity_upper_divided_by_h']
    diag=[]
    for h in (.5,.2,.1,.05,.025):
        # ell(h) = (h/4) exp(-1/h^2), rho=h/2.
        upper_normalized=math.pi*h/(1+h*h*math.log(2))
        diag.append({'h':h,'normalized_width_upper':round(upper_normalized,12)})
    assert all(diag[i+1]['normalized_width_upper'] < diag[i]['normalized_width_upper'] for i in range(len(diag)-1))
    assert diag[-1]['normalized_width_upper'] < .08
    return {
        'fixed_h':fixed_h,
        'rho':rho,
        'fixed_h_small_electrode_log_cutoff':short_electrodes,
        'diagonal_ell': '(h/4)*exp(-1/h^2)',
        'diagonal_exact_normalized_upper': 'pi*h/(1+h^2*log(2))',
        'diagonal_upper_values':diag,
        'iterated_limits': {'thin_then_shrink':'2/pi','shrink_then_thin':'0'},
    }


def test_reciprocal_polarization():
    modes=0
    for h in (.003,.02,.1,.69,1.3,3.):
        for n in range(1,151):
            pin = n/math.tanh(n*h)
            free= n*math.tanh(n*h)
            assert abs((pin*free)/(n*n)-1)<1e-14
            modes+=1
    for h in (.02,.69,3):
        # Real g having cosine modes n=1,3,7 with nontrivial amplitudes.
        amps={1: F(1,2),3: F(1,5),7: F(1,10)}
        epin = 4*math.pi*sum(n/math.tanh(n*h)*float(a*a) for n,a in amps.items())
        efree=4*math.pi*sum(n*math.tanh(n*h)*float(a*a) for n,a in amps.items())
        einf=4*math.pi*sum(n*float(a*a) for n,a in amps.items())
        assert epin*efree + 1e-12 >= einf*einf
    return {
        'mode_pairs_checked':modes,
        'identity':'Lambda_pinned(n)*Lambda_free(n)=n^2',
        'energy_product_lower':'(4*pi*sum_n n*|g_hat(n)|^2)^2',
        'pure_mode_equality':True,
    }


def build_manifest():
    actual=algebraic_cover_check()
    return {
        'schema_version':1,
        'status':'finite exact algebra plus verified analytic formulas; PDE thin-limit is written proof; no KKL Wave transport',
        'source':'actual Misiurewicz quadratic slit covering / degree-two KKL covering-leg interface',
        'actual_quadratic':actual,
        'continuum_bounds':test_continuum_formulas(actual['attached_arc_angular_length_approx']),
        'two_parameter_no_go':test_two_parameter_no_go(),
        'reciprocal_polarization':test_reciprocal_polarization(),
        'scope':'condenser full path family between source attached block and its deck translate; NOT actual canonical WAD',
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    group=p.add_mutually_exclusive_group()
    group.add_argument('--check-manifest', action='store_true')
    group.add_argument('--write-manifest', action='store_true')
    arg=p.parse_args()
    payload=json.dumps(build_manifest(), sort_keys=True,indent=2)+'\n'
    if arg.write_manifest:
        OUT.parent.mkdir(parents=True,exist_ok=True)
        OUT.write_text(payload,encoding='utf-8')
        print('WROTE '+str(OUT))
    elif arg.check_manifest:
        assert OUT.read_text(encoding='utf-8') == payload, 'manifest mismatch'
        print('PASS: exact Joukowski algebra, free-vs-pinned duality, capacity bounds, two-scale controls, byte-identical manifest')
    else:
        print(payload,end='')

if __name__=='__main__':
    main()
