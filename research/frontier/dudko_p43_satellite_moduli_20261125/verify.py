"""Exact rational enclosures of BLOT's upper envelope, never actual moduli."""
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path

N = 80
D = 10**40
DELTA = Q(1, 2)


def atan_bounds(z):
    a = sum(((-1)**j * z**(2*j+1) / (2*j+1) for j in range(N)), Q(0))
    b = a + (-1)**N * z**(2*N+1) / (2*N+1)
    return min(a, b), max(a, b)


def log_unit_bounds(y):
    assert 1 <= y <= 2
    t = (y-1)/(y+1)
    a = 2*sum((t**(2*j+1)/(2*j+1) for j in range(N)), Q(0))
    return a, a + 2*t**(2*N+1)/((2*N+1)*(1-t*t))


def log_bounds(x):
    assert isinstance(x, int) and x >= 2
    e = x.bit_length()-1
    a,b = log_unit_bounds(Q(2))
    c,d = log_unit_bounds(Q(x, 2**e))
    return e*a+c, e*b+d


def pi_bounds():
    a,b = atan_bounds(Q(1,5))
    c,d = atan_bounds(Q(1,239))
    return 16*a-4*d,16*b-4*c


def envelope(s):
    assert s >= 2
    a,b = pi_bounds()
    c,d = log_bounds(4*(s+1))
    assert 0 < c <= d
    return 2*a/d,2*b/c


def outward(a,b):
    lo = a*D
    hi = b*D
    l = lo.numerator//lo.denominator
    u = -(-hi.numerator//hi.denominator)
    assert Q(l,D) <= a <= b <= Q(u,D) and u-l <= 2
    def fmt(n):
        return f'{n//D}.{n%D:040d}'
    return fmt(l),fmt(u),Q(u,D)


def fib(n):
    a,b=0,1
    for _ in range(n):
        a,b=b,a+b
    return a


def run():
    import math
    rows=[]
    base=list(range(2,33))+[64,128]
    chains={'linear':lambda k:(1,k),'exponential':lambda k:(1,2**k),
            'constant':lambda k:(1,2),'golden':lambda k:(fib(k),fib(k+1))}
    decisions={}
    for name, rotation in chains.items():
        indices=base+([256,1024,1048576] if name=='linear' else [])
        hits=[]
        previous=None
        for k in indices:
            p,s=rotation(k)
            assert 0<p<s and math.gcd(p,s)==1
            a,b=envelope(s)
            lo,hi,u=outward(a,b)
            if previous is not None:
                assert (a,b)==previous if name=='constant' else b<previous[0]
            previous=(a,b)
            reject=u<DELTA
            if reject: hits.append(k)
            rows.append({'chain':name,'k':k,'rotation':f'{p}/{s}',
                         'relative_period':str(s),'B_lo':lo,'B_hi':hi,
                         'm_lower_non_strict':'0','m_upper_strict':hi,
                         'reject_threshold':reject})
        decisions[name]={'decision':'reject' if hits else 'inconclusive',
                         'first_sampled_rejection':hits[0] if hits else None}
        expected={'linear':1048576,'exponential':32,'golden':32}
        if name in expected:
            assert expected[name] in hits
        else:
            assert not hits
    assert len(rows)==135
    # Independent coarse bounds to catch normalization and rounding mistakes.
    a,b=pi_bounds(); assert Q(314,100)<a<b<Q(315,100)
    a,b=log_bounds(2); assert Q(69,100)<a<b<Q(70,100)
    a,b=envelope(2); assert 2<a<b<3
    return {'schema':1,'status':'imported obstruction; finite certificate; pseudo-Siegel open',
            'observable':'upper envelope B(s), NOT actual annulus modulus',
            'threshold':'1/2','precision_decimal_places':40,'terms':N,
            'decisions':decisions,'rows':rows,
            'actual_moduli_measured':0,'pseudo_siegel_test':'not identified'}


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path('results.json'))
    args=parser.parse_args()
    data=run()
    summary_path=Path(__file__).with_name('results_summary.json')
    if summary_path.exists():
        summary=json.loads(summary_path.read_text())
        assert data['decisions']==summary['decisions']
        assert data['actual_moduli_measured']==summary['actual_moduli_measured']
        for expected in summary['rows']:
            row=next(x for x in data['rows'] if x['chain']==expected['chain'] and x['k']==expected['k'])
            assert all(row[key]==value for key,value in expected.items())
    args.output.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps(data['decisions'],sort_keys=True))
