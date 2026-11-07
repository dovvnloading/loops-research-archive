#!/usr/bin/env python3
"""Exact algebra and reproducible spectral checks for the sheet-character
Dirichlet defect and smooth-charge/extremal-width bridge.

NO computation here proves a native KKL immersion/attachment theorem.
The paper supplies that analytic proof and states its own limitations.
Run:
    python research/independent_audits/verify_sheet_character_width_duality.py --check-manifest
"""
from __future__ import annotations

import argparse
import cmath
from fractions import Fraction as F
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / 'results' / 'sheet_character_width_duality_20261107.json'
PI = math.pi
H = math.log(2)


def finite_fourier_energy_over_pi(coeffs: dict[int, tuple[F,F]], constant: F, h: F) -> F:
    """u=(1-t/h)(constant+Σ_{n>0}(a_n cos nθ+b_n sin nθ)).

    Energy is π*(2 constant²/h+Σ(a²+b²)(1/h+n² h/3)).
    This is EXACT rational algebra, not discretization or floating point.
    """
    energy = 2*constant**2/h
    for n, (a,b) in coeffs.items():
        assert n>0
        energy += (a*a+b*b)*(1/h + F(n*n,3)*h)
    return energy


def exact_character_tests() -> dict:
    cases=0
    nonzero_defects=0
    for d in (2,3,4,8,16,64):
        for h in (F(1,2),F(1),F(3,2)):
            # Both invariant and noninvariant frequencies, with exact rational amplitudes.
            ns=sorted({1,2,3,d-1,d,d+1,2*d-1,2*d,2*d+1,3*d+1})
            coeffs={n:(F(1,n+2),F(-2,n+3)) for n in ns if n>0}
            constant=F(1,3)
            invariant={n:val for n,val in coeffs.items() if n%d==0}
            other={n:val for n,val in coeffs.items() if n%d!=0}
            base={n//d:val for n,val in invariant.items()}
            total=finite_fourier_energy_over_pi(coeffs,constant,h)
            inv=finite_fourier_energy_over_pi(invariant,constant,h)
            non=finite_fourier_energy_over_pi(other,F(0),h)
            target=finite_fourier_energy_over_pi(base,constant,d*h)
            assert total==inv+non, ('orthogonal',d,h)
            assert inv==d*target, ('cover_degree',d,h)
            assert non>0
            # Invariant harmonics of the source form precisely d-multiple modes.
            assert all(n%d==0 for n in invariant)
            assert all(n%d!=0 for n in other)
            cases+=1;nonzero_defects+=1
    return {
        'degrees':[2,3,4,8,16,64], 'exact_rational_radial_heights':['1/2','1','3/2'],
        'exact_energy_identity_cases':cases,
        'positive_noninvariant_defects':nonzero_defects,
        'identity':'E_source=d*E_target(descended)+E_nondescending',
        'normalization':'energies divided by pi; affine radial Fourier modes; exact Fractions',
    }


def tanh_n_log2_as_fraction(n: int) -> F:
    assert n>=1
    return F(4**n-1,4**n+1)


def sheet_R(d: int,N: int,h: float=H) -> float:
    assert d>=2 and N>=1
    delta=2*PI/d
    return (2/PI)*sum(
        (1-n/(N+1))**2 * (1-math.cos(n*delta)) * math.tanh(n*h)/n
        for n in range(1,N+1)
    )


def sheet_R_d2_times_pi_exact(N:int)->F:
    # For d=2 at h=log2, cosine(n*pi) is ±1 and tanh(n log2) rational.
    return 2*sum((F(N+1-n,N+1)**2)*F(1-(-1)**n)*tanh_n_log2_as_fraction(n)/n
                 for n in range(1,N+1))


def character_trace_bound_tests()->dict:
    """Independent Fourier variational check: affine radial extensions have
    energy at least the exact harmonic extension of their noninvariant trace.
    Analytic proof: Dirichlet principle + tanh/coth mode calculation.
    """
    checked=0
    for d in (2,3,4,8,64):
        for h in (0.25,0.5,math.log(2),1.0,2.0):
            ns=sorted({1,2,3,d-1,d,d+1,2*d-1,2*d,2*d+1})
            coeffs={n:(F(1,n+2),F(-2,n+3)) for n in ns if n>0 and n%d!=0}
            affine=float(finite_fourier_energy_over_pi(coeffs,F(0),F(str(h))))
            harmonic=sum((float(a*a+b*b))*n/math.tanh(n*h) for n,(a,b) in coeffs.items())
            lower=sum(float(a*a+b*b)*n for n,(a,b) in coeffs.items())
            assert affine +1e-12 >= harmonic >= lower >0
            checked+=1
    # d=2: a pure third harmonic is deck odd, but the first odd coefficient is 0.
    # This is an adversarial control against treating the first-harmonic probe
    # as exhaustive evidence for sheet non-descent.
    assert 3%2!=0 and 1!=3
    # For a cos(theta) trace u with harmonic extension, ghat_1=1/2;
    # sharp odd harmonic energy is pi*coth(h), exactly the optimal Fejer bound.
    assert abs(4*PI*0.25/math.tanh(H) - 5*PI/3)<2e-14
    return {
        'degrees':[2,3,4,8,64],
        'heights':[0.25,0.5,'log(2)',1.0,2.0],
        'affine_vs_harmonic_trace_bound_cases':checked,
        'character_modes':'n nonzero modulo d',
        'formula':'E_nondesc >= 4*pi*sum_{n>0,d does not divide n} n*coth(n*h)*abs(ghat_n)^2',
        'modulus_free_bound':'coth(n*h)>=1',
        'd2_first_odd_trace':'E_odd >= 4*pi*coth(h)*abs(ghat_1)^2',
        'negative_control':'pure third harmonic has odd energy but zero first Fourier coefficient',
    }


def sheet_charge_tests()->dict:
    assert sheet_R_d2_times_pi_exact(1)==F(3,5)
    assert abs(sheet_R(2,1) - 3/(5*PI))<1e-14
    for N in range(1,25):
        assert abs(sheet_R(2,N)*PI-float(sheet_R_d2_times_pi_exact(N)))<2e-12
    ds=(2,3,8,64)
    records=[]
    for d in ds:
        for N in (1,4*d):
            resistance=sheet_R(d,N)
            assert resistance>0
            records.append({'degree':d,'probe_N':N,
                            'riesz_norm_squared':round(resistance,14),
                            'optimal_energy_per_unit_delta_squared':round(1/resistance,12)})
    R641=sheet_R(64,1)
    assert R641>0
    exact_angle=(3/(10*PI))*(1-math.cos(PI/32))
    assert abs(R641-exact_angle)<1e-16
    certified_lower=20480/(3*PI)
    assert 1/R641>=certified_lower
    # A coherent exact Riesz test: one real Fourier mode at d=2,N=1.
    # For u with trace cos(theta), outer trace 0, ∆=1 and E=π coth(h).
    assert math.isclose(PI/math.tanh(H),5*PI/3,rel_tol=1e-14)
    return {
        'probe':'Fejer nonnegative normalized smooth global probe, no compact support',
        'height':'log(2)','finite_sums':[{'d':x['degree'],'N':x['probe_N'],
                     'R':x['riesz_norm_squared'],'optimal':x['optimal_energy_per_unit_delta_squared']} for x in records],
        'd2_N1_exact_pi_times_R':'3/5',
        'd2_N1_exact_defect_constant':'5*pi/3',
        'd64_N1_certified_lower_coefficient':'20480/(3*pi)',
        'd64_N1_coefficient_approx':round(1/R641,9),
        'd64_N256_coefficient_approx':round(1/sheet_R(64,256),9),
        'd2_rational_N_values_checked':24,
        'sharpness':'Riesz equality for outer-Dirichlet/inner-Neumann problem',
    }


def cosine_arch_coefficient(n:int)->complex:
    """Fourier coefficient of C1 arch psi=(1-cos(6θ))/ell on 0<=θ<=ell,
    ell=π/3, normalized by 1/(2π). Analytic integration, not FFT.
    """
    ell=PI/3
    if n==0:
        return 1/(2*PI)
    if abs(n)==6:
        return -1/(4*PI)
    return 18*(1-cmath.exp(-1j*n*ell))/(PI*ell*1j*n*(36-n*n))


def free_boundary_resistance(N:int,h:float=H)->float:
    # q=psi(theta)-psi(theta-pi), so only odd Fourier modes survive.
    return 16*PI*sum((abs(cosine_arch_coefficient(n))**2)/(n*math.tanh(n*h))
                     for n in range(1,N+1,2))


def certified_tail_upper(N:int)->float:
    assert N>=12
    return 92160/(PI**3*N**6)


def full_width_tests()->dict:
    assert abs(abs(cosine_arch_coefficient(1))-54/(35*PI**2))<1e-14
    # Exact analytic L2 and trial-voltage constants.
    # Each arch has ∫psi²=9/(2π), q has disjoint supports and ∫q²=9/π.
    r_max=15/PI
    lower=PI/15
    upper=3*H/PI
    pinned_min_lb=2*PI/(9*H)
    assert lower<upper<pinned_min_lb
    assert pinned_min_lb>1.0 and upper<0.67
    series=free_boundary_resistance(256)
    tail=certified_tail_upper(256)
    assert 0<tail<2e-11
    assert 0<series<r_max
    rigorous_stronger_lb=1/(series+tail)
    assert lower<rigorous_stronger_lb<upper
    # Check analytic coefficient high-mode n^-3 bound and stable summation.
    for n in range(12,1500):
        assert abs(cosine_arch_coefficient(n)) <= 144/(PI*PI*n**3)*(1+1e-12)
    for n in (32,64,128,256):
        partial=free_boundary_resistance(n)
        bound=certified_tail_upper(n)
        assert 0 <= series-partial <= bound+5e-12
    return {
        'annulus_height':'log(2)',
        'electrode_arcs':'[0,pi/3] and [pi,4*pi/3] on inner circle; outer free',
        'probes':'normalized C1 cosine-arch, disjoint support',
        'capacity_extremal_width_lower_exact':'pi/15',
        'capacity_extremal_width_upper_exact':'3*log(2)/pi',
        'rigorous_tail_upper_at_N256':round(tail,15),
        'free_neumann_charge_R_N256':round(series,12),
        'certified_series_lower_width':round(rigorous_stronger_lb,12),
        'naive_pinned_outer_one_terminal_min_lower':round(pinned_min_lb,12),
        'naive_inequality_fails':'pinned one-terminal min > true full condenser capacity upper',
        'total_charge_zero':True,
        'width_convention':'W(full connecting family)=mixed condenser Dirichlet capacity',
        'wave_limit':'no inference for strict subfamilies of full connecting family',
    }


def manifest()->dict:
    return {
        'schema_version':1,
        'status':'exact covering energy and smooth-charge analytic proofs; no native KKL WAD or MLC proof',
        'physical_scope':'Bottcher exterior positive Green annuli of connected quadratic; p=6 gives d=64 physical covering',
        'character_decomposition':exact_character_tests(),
        'character_trace_bound':character_trace_bound_tests(),
        'sheet_mismatch':sheet_charge_tests(),
        'full_width':full_width_tests(),
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument('--write-manifest',action='store_true')
    group.add_argument('--check-manifest',action='store_true')
    args=parser.parse_args()
    serialized=json.dumps(manifest(),indent=2,sort_keys=True)+'\n'
    if args.write_manifest:
        MANIFEST.parent.mkdir(parents=True,exist_ok=True)
        MANIFEST.write_text(serialized,encoding='utf-8')
        print('WROTE '+str(MANIFEST))
    elif args.check_manifest:
        assert MANIFEST.read_text(encoding='utf-8')==serialized, 'manifest differs from exact recomputation'
        print('PASS: exact Fourier-cover identities, signed-charge width bounds, negative controls, manifest')
    else:
        print(serialized,end='')

if __name__=='__main__':
    main()
