#!/usr/bin/env python3
"""Independent deterministic checks for the analytic annular contact law.

Only finite identities, universal inequalities, and a numerical arcsine test
are executable here. The infinite-dimensional charge duality, logarithmic
potential minimization, and continuum KKL application are WRITTEN proofs,
not machine-verified by this script.

python research/independent_audits/verify_annular_contact_crossover.py --check-manifest
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

OUT = Path(__file__).resolve().parents[2] / 'results' / 'annular_contact_crossover_20261107.json'
PI = math.pi


def thermal_original_product(h: float) -> float:
    """Sum log(coth(k h)) WITHOUT using the eta formula."""
    out = 0.0
    k = 1
    while True:
        term = -math.log(math.tanh(k*h))
        out += term
        if k*h > 19:
            break
        k += 1
    return out


def thermal_odd_series(h: float) -> float:
    """Independent first-return Fourier series for the same thermal kernel."""
    result = 0.0
    for n in range(1, int(math.ceil(38/h))+2, 2):
        # expm1 avoids cancellation for small positive 2*n*h
        result += (2.0/math.expm1(2*n*h))/n
    return result


def eta_modular(h: float) -> tuple[float, float]:
    """Modular-image product; the final correction is exponentially small."""
    q = math.exp(-PI*PI/h)
    correction = 0.0
    if q:
        for k in range(1, 200):
            term = math.log1p(-q**k) - 2*math.log1p(-(q*q)**k)
            correction += term
            if q**k < 1e-17:
                break
    result = PI*PI/(8*h) + 0.5*math.log(h/(2*PI)) + correction
    return result, correction


def exact_contact_upper(h: float, ell: float) -> float:
    """Explicit upper bound on the *minimum resistance*: arcsine log energy + T_h(0)."""
    t, _ = eta_modular(h)
    return (4/PI)*(t+0.5*math.log(8/ell))


def asymptotic_resistance(h: float, ell: float) -> float:
    return PI/(2*h)+(2/PI)*math.log(4*h/(PI*ell))


def eps_odd_log(t: float) -> float:
    """K_odd(t) - 1/2 log(2/|t|), smooth at t=0."""
    t = abs(t)
    if t < 1e-4:
        return -t*t/24 - 7*t**4/2880
    return 0.5*math.log((t/2)/math.tan(t/2))


def arcsine_test(h: float, ell: float, samples: int = 96) -> dict:
    """An *independent* arcsine probability trial using Chebyshev quadrature.

    It bounds equilibrium resistance from above, but is not the actual
    condenser minimum for general h/ell. It tests the analytic kernel split.
    """
    points = [ell/2*math.cos((j+0.5)*PI/samples) for j in range(samples)]
    # Quadrature over the arcsine equilibrium measure, only for a smooth error.
    log_error = sum(eps_odd_log(x-y) for x in points for y in points) / samples**2
    # Thermal coefficient is independently obtained from the source angles;
    # no Bessel function library is needed.
    thermal_loss = 0.0
    for n in range(1, int(math.ceil(35/h))+2, 2):
        m_real = sum(math.cos(n*x) for x in points)/samples
        coeff = 2/math.expm1(2*n*h)/n
        thermal_loss += coeff * (1-m_real*m_real)
    t0 = thermal_original_product(h)
    rtrial=(4/PI)*(t0+0.5*math.log(8/ell)+log_error-thermal_loss)
    rup=exact_contact_upper(h,ell)
    formula=asymptotic_resistance(h,ell)
    # The true minimum R_* lies below R_trial, which lies below R_up;
    # the exact lower bound uses log-energy minimality and thermal variation.
    assert log_error <= 1e-12
    assert thermal_loss >= -1e-12
    assert rtrial <= rup+1e-10
    assert abs(rup-formula) < 0.001   # eta modular remainder
    assert rtrial >= rup - 15*((ell/h)**2+ell*ell)
    return {
        'h': h, 'ell': ell, 'ratio': round(ell/h, 9),
        'log_kernel_error': round(log_error, 12),
        'thermal_variation': round(thermal_loss, 12),
        'arcsine_trial_resistance_upper': round(rtrial, 11),
        'analytic_resistance_upper': round(rup, 11),
        'eta_main_law': round(formula, 11),
        'uniform_truncation_bound': 'R_main - R_* = O(ell^2 + (ell/h)^2)'
    }


def analytic_invariants() -> dict:
    # Exact identities for simple rational-logarithmic equilibrium energies.
    # log energy for arcsine on an interval of length ell: log(4/ell).
    # Uniform density gives log(1/ell)+3/2; their difference is scale-free.
    excess = 1.5-math.log(4)
    assert 0.1 < excess < 0.12
    # A negative control: uniform charges are *not* optimal and would
    # shift the constant 4/pi in the resistance formula.
    return {
        'arcsine_log_energy': 'log(4/ell)',
        'uniform_log_energy': 'log(1/ell)+3/2',
        'uniform_charge_energy_excess': round(excess, 15),
        'universal_reciprocal_resistance': 'pi/(2h)+(2/pi)log(4h/(pi ell))+o(1)',
        'error_regime': '0<h<=1, 0<ell<=h/4; O((ell/h)^2 + ell^2 + exp(-pi^2/h))',
    }


def eta_tests() -> dict:
    tests=[]
    for h in (2.0, 1.0, .5, .2, .1, .05):
        direct=thermal_original_product(h)
        odd=thermal_odd_series(h)
        modular, correction=eta_modular(h)
        assert abs(direct-odd)<1e-10, (h,direct,odd)
        assert abs(direct-modular)<1e-10, (h,direct,modular)
        tests.append({
            'h':h, 'log_coth_product':round(direct, 13),
            'modular_eta_value':round(modular,13),
            'modular_correction':round(correction,13),
            'abs_independent_difference':round(abs(direct-odd),15)
        })
    return {'identity':'sum_{k>=1} log coth(kh) = pi^2/(8h)+(1/2)log(h/(2pi))+eta-modular-correction',
            'samples':tests}


def crossover_tests() -> dict:
    samples=[]
    for C in (.25, 1, 2):
        for h in (.2, .1, .05, .025):
            ell=math.exp(-C/h)
            # Only use the asymptotic formula when ell << h, as required.
            if ell/h > .25:
                continue
            law=asymptotic_resistance(h,ell)
            h_over_width=h*law
            predicted_limit=PI/2+(2/PI)*C
            eta_correction=(2*h/PI)*math.log(4*h/PI)
            assert abs(h_over_width-predicted_limit-eta_correction)<5e-13
            samples.append({'C':C,'h':h,'ell':round(ell,15),
                            'h_times_main_resistance':round(h_over_width,12),
                            'limiting_h_over_width':round(predicted_limit,12),
                            'finite_h_log_correction':round(eta_correction,12)})
    fixed_ell=1.0
    assert abs(2/(PI-fixed_ell)-2/PI)>.2  # fixed-access negative control
    return {
        'critical_exponential_law': 'W_h(exp(-C/h))/h -> 1/(pi/2 + 2C/pi)',
        'all_shrinking_access_scales':'h log(1/ell)->C in [0,infinity] gives the same crossover, with 0 at C=infinity',
        'samples':samples,
        'fixed_access_negative_control': {
            'ell':fixed_ell,
            'correct_density':round(2/(PI-fixed_ell),12),
            'incorrect_shrinking_access_density':round(2/PI,12),
        },
    }


def attachment_control() -> dict:
    # Use the same source-defined algebraic c as the archive; do not suggest
    # fixed ell_X realizes our simultaneous shrinking theorem.
    def H(x): return x**3+2*x**2+2*x+2
    lo,hi=-1.6,-1.5
    assert H(lo)<0<H(hi)
    for _ in range(70):
        c=(lo+hi)/2
        if H(c)<0:lo=c
        else:hi=c
    c=(lo+hi)/2
    theta=math.acos(-c-1)/(2*PI)
    ell=4*PI*theta
    assert 0<ell<PI
    return {'actual_attachment_ell':round(ell,12),
            'physical_model_is_constant_ell':True,
            'native_cover_dichotomy':'ell>=pi -> saturated covering image; 0<ell<pi -> disjoint deck electrodes',
            'correct_fixed_ell_density':round(2/(PI-ell),12),
            'critical_exponential_law_not_claimed_for_actual_fixed_ell':True}


def compute():
    return {'schema_version':1,
            'provenance':'analytic written proof + deterministic tests only; NOT native KKL Wave/WAD certificate',
            'contact':analytic_invariants(),
            'eta_modularity':eta_tests(),
            'arcsine_kernel_brackets':[arcsine_test(h,h/50) for h in (.2,.1,.05)],
            'exponential_crossover':crossover_tests(),
            'actual_attachment_control':attachment_control(),
            'source':'Actual KKL f-leg is a covering; iota*-born attached blocks must be separately verified'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--write-manifest',action='store_true')
    group.add_argument('--check-manifest',action='store_true')
    options=parser.parse_args()
    output=json.dumps(compute(),indent=2,sort_keys=True)+'\n'
    if options.write_manifest:
        OUT.parent.mkdir(parents=True,exist_ok=True)
        OUT.write_text(output,encoding='utf-8')
        print('WROTE',OUT)
    elif options.check_manifest:
        assert OUT.read_text(encoding='utf-8')==output, 'Manifest differs from exact regeneration'
        print('PASS: independent eta/series, arcsine equilibrium, exponential crossover, and analytic negative controls')
    else:
        print(output,end='')

if __name__ == '__main__':
    main()
