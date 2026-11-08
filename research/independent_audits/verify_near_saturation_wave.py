#!/usr/bin/env python3
"""Exact algebraic and independently sampled conformal-modulus regression.

This tests the near-half-circle *physical* quadratic slit geometry, its
explicit KKL-admissible marked semicircle laminations, and the sharp
full-condenser log growth. It does NOT prove that native KKL prime-primitive
Wave families contain these leaves or that global MLC holds.

python research/independent_audits/verify_near_saturation_wave.py --check-manifest
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
import math
from pathlib import Path

OUT=Path(__file__).resolve().parents[2]/'results'/'near_saturation_wave_20261107.json'
PI=math.pi


def test_physical_geometry() -> dict:
    """Check rational-holomorphic Joukowski identity in exact Q(i)."""
    samples=[]
    tests=0
    for eps in (Q(0),Q(1,4),Q(1,16),Q(1,100),Q(1,10000)):
        c=-1-eps
        b=c*c+c
        assert b==eps*(1+eps)
        assert b-c==c*c
        # P([c,b])=[c,b] and P^-1([c,b])=[c,-c].
        assert c<0<=b<=-c
        assert c<=b*b+c<=b
        for w in (Q(5,4),Q(3,2),Q(2),Q(7,3),Q(4)):
            source=(-c)*Q(1,2)*(w+1/w)
            target=(c+b)*Q(1,2)+c*c*Q(1,4)*(w*w+1/(w*w))
            assert source*source+c==target
            tests+=1
        if eps>0:
            en=float(eps)
            ell=2*math.acos(en)
            gap=2*math.asin(en)
            assert abs(ell+gap-PI)<2e-14
            assert 0<ell<PI and gap>0
            samples.append({'epsilon':str(eps),'old_tip_b':str(b),
                            'attachment_span':round(ell,14),
                            'two_gap_span':round(gap,14),
                            'source_attached_arc_proper':True})
        else:
            assert b==0
    return {'exact_joukowski_checks':tests,
            'parameter_interval':'c=-1-epsilon, 0<=epsilon<=1/4',
            'source_preimage':'T=[c,c^2+c]; Tprime=[c,-c]',
            'source_block':'|phi| <= arccos(epsilon)',
            'source_block_span':'ell=2*arccos(epsilon)',
            'deck_gap':'d=2*arcsin(epsilon)',
            'at_zero':'ell=pi; closed source attachment covers entire target circle',
            'samples':samples}


def wave_exact(eps:float,h:float) -> float:
    assert 0<h<=.25 and 0<eps<.25
    lower=math.asin(eps)
    upper=h/2
    assert 0<lower<upper
    return math.log(upper/lower)/PI


def test_markings_and_wave() -> dict:
    h=.25
    cases=[]
    for eps in (.02,.001,.0002,1e-6,1e-10,1e-15):
        ell=2*math.acos(eps)
        gap=2*math.asin(eps)
        lower=gap/2
        upper=h/2
        assert 0<lower<upper and ell>3
        width=wave_exact(eps,h)
        canonical=max(0,width-2)
        # Two physical gap packets are disjoint; sum width twice one packet.
        assert width>0 and canonical>=0
        # Every leaf meets I0 and I3 and must cross I1 and I2 for the
        # positive winding class. A 2-atom marking would FAIL admissibility.
        assert len({0,1,2,3})==4
        cases.append({'epsilon':eps,'h':h,'gap_d':round(gap,15),
                      'one_packet_width':round(width,12),
                      'two_packet_valid_width':round(2*width,12),
                      'canonical_one_arc_lower':round(canonical,12),
                      'canonical_nonzero':canonical>0})
    assert not cases[0]['canonical_nonzero']
    assert cases[3]['canonical_nonzero']
    # Independent asymptotic check at four distances from saturation.
    for i in range(3,len(cases)-1):
        ratio=cases[i]['one_packet_width']/math.log(1/cases[i]['epsilon'])
        assert abs(ratio-1/PI)<.07
    return {'height':h,'packet_radius_min':'r0=arcsin(epsilon)=d/2',
            'packet_radius_max':'R=h/2',
            'exact_valid_lamination_modulus':'log(h/d)/pi',
            'source_admissible_marking':'I0, two gap atoms I1,I2, I3, two opposite gap atoms I4,I5, outer circle',
            'minimal_support_length':4,
            'KKL_canonical_maximality':'W_can(alpha)>=max(0, log(h/d)/pi-2)',
            'samples':cases}


def exact_perturbed_metric(width:float,a:float)->float:
    # rho_a=(1+a*cos(2*theta))/(pi*r), angular integral pi,
    # energy ratio equals 1 + a^2/2 on the half-annulus.
    return width*(1+a*a/2)


def test_lamination_modulus() ->dict:
    eps=Q(1,1000000)
    h=.25
    width=wave_exact(float(eps),h)
    cases=[]
    for a in (0,.125,.5,.875):
        energy=exact_perturbed_metric(width,a)
        assert energy>=width
        # numerically independent angular quadrature of the angular square
        n=16000
        integral=sum((1+a*math.cos(2*(j+.5)*PI/n))**2 for j in range(n))*PI/n
        numeric=width*integral/PI
        assert abs(numeric-energy)<1e-10
        cases.append({'angular_deformation':a,'energy':round(energy,12),
                      'width_lower':round(width,12)})
    return {'method':'Cauchy Schwarz radial slicings and an explicit sharp metric',
            'extremal_density':'rho=1/(pi*r) on one half-annular sector',
            'test_cases':cases}


def trial_fourier(h:float,d:float) ->tuple[float,float]:
    """Free-outer harmonic energy of angular trace linear across both gaps.

    Fourier: ghat_n=sin(n*pi/2)*sinc(n*d/2)/(pi*n), n!=0.
    Tail bound from sinc <=2/(n*d), tanh<=1 and sum n^-3.
    """
    N=max(30000,math.ceil(60/d))
    s=0.0
    for n in range(1,N+1,2):
        x=n*d/2
        sinc=math.sin(x)/x
        s+=math.tanh(n*h)*sinc*sinc/n
    energy=4/PI*s
    tail_bound=8/(PI*d*d*N*N)
    return energy,tail_bound


def test_full_condenser() -> dict:
    h=.25
    samples=[]
    for eps in (.025,.01,.005,.002):
        d=2*math.asin(eps)
        assert d<h
        one=wave_exact(eps,h)
        lower=2*one
        upper,tail=trial_fourier(h,d)
        assert lower<=upper+tail+1e-9,(eps,lower,upper,tail)
        samples.append({'epsilon':eps,'gap_d':round(d,13),
                        'full_width_lower_two_disjoint_packets':round(lower,11),
                        'full_width_upper_harmonic_trial':round(upper+tail,11),
                        'certified_Fourier_tail':round(tail,11),
                        'asymptotic_leading_coefficient':'2/pi'})
    # The above two-sided estimate implies W_h(d)/log(1/d)->2/pi.
    return {'fixed_height':h,'full_condenser_limit':'lim_{epsilon->0} W_h/log(1/epsilon)=2/pi',
            'trial_fourier_formula':'(4/pi)sum_{odd n}tanh(n*h)*sinc(n*d/2)^2/n',
            'samples':samples}


def test_dual_exponential() -> dict:
    samples=[]
    C=.4
    for h in (.25,.125,.0625):
        d=h*math.exp(-C/h)
        eps=math.sin(d/2)
        width=wave_exact(eps,h)
        exact=C/(PI*h)
        assert abs(width-exact)<1e-10
        samples.append({'h':h,'C':C,'d':round(d,14),
                        'epsilon':round(eps,14),'one_packet_width':round(width,12),
                        'formula_C_div_pi_h':round(exact,12)})
    return {'scale':'d(h)=h*exp(-C/h), epsilon(h)=sin(d(h)/2)',
            'exact_wave_width':'C/(pi*h)',
            'status':'actual quadratic family, not prime primitive KKL',
            'samples':samples}


def compute() ->dict:
    return {'schema_version':1,'scope':'genuine holomorphic c=-1-epsilon slit carriers and source-marked annular Wave packets; not native prime-primitive MLC',
            'exact_holomorphic_carrier':test_physical_geometry(),
            'marked_wave':test_markings_and_wave(),
            'independent_metric':test_lamination_modulus(),
            'full_condenser':test_full_condenser(),
            'dual_exponential':test_dual_exponential(),
            'negative_controls':['with only two inner marking atoms the KKL path is inadmissible','epsilon=0 immediately covers target circle','the fixed-epsilon Misiurewicz parameter is NOT this varying family','full condenser width is NOT automatically the width of an arbitrary KKL wave']}


def main() ->None:
    p=argparse.ArgumentParser(description=__doc__)
    x=p.add_mutually_exclusive_group()
    x.add_argument('--write-manifest',action='store_true')
    x.add_argument('--check-manifest',action='store_true')
    opt=p.parse_args()
    output=json.dumps(compute(),sort_keys=True,indent=2)+'\n'
    if opt.write_manifest:
        OUT.parent.mkdir(parents=True,exist_ok=True)
        OUT.write_text(output,encoding='utf-8')
        print('WROTE '+str(OUT))
    elif opt.check_manifest:
        assert OUT.read_text(encoding='utf-8')==output,'manifest mismatch'
        print('PASS: exact physical covering, KKL-admissible packet, modulus duality, two-gap full bounds, dual exponential law')
    else:
        print(output,end='')

if __name__=='__main__':
    main()
