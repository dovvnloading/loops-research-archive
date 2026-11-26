"""Exact rational regressions, not verification of the analytic proof."""
from fractions import Fraction as Q
import json
from pathlib import Path


def abs2(x, y):
    return x*x+y*y


def kernel(x, y):
    return (1-abs2(x, y))/abs2(1-x, y)


def verify(data):
    disk_checks = threshold_checks = witnesses = numerical_checks = 0
    for q in (3, 4, 9, 50, 100):
        n = q**3
        a = Q(q,n)
        for m in (7,13):
            for i in range(-m,m+1):
                for j in range(-m,m+1):
                    x, y = Q(i,m), Q(j,m)
                    if abs2(x,y) >= 1:
                        continue
                    re = a + Q(q*q,2)*kernel(x,y)
                    im = q*q*y/abs2(1-x,y)+Q(7,3)
                    s = abs2(re,im)
                    hx, hy = re/s, -im/s
                    h2 = abs2(hx,hy)
                    assert re*h2 == hx
                    assert h2/hx == 1/re <= Q(n,q)
                    d = 1/(6*q*kernel(x,y))  # pi>3
                    if d <= Q(19,180):
                        assert Q(9,10)**2+Q(9,5)*d <= 1
                        assert 1 <= Q(6,5)**2-Q(12,5)*d
                        assert 2*d*d <= (1-d)**2 and d < 1
                        threshold_checks += 1
                    for T in (Q(1,10),Q(1,100),Q(1,1000)):
                        if h2 >= T*T:
                            u = (T*hx+h2)/abs2(T+hx,hy)
                            assert u >= Q(1,2)
                    disk_checks += 1
        for x,y in ((Q(0),Q(1)),(Q(3,5),Q(4,5)),(Q(99,101),Q(20,101))):
            assert abs2(x,y) == 1
            b = -q*q*y/abs2(1-x,y)
            re = a + Q(q*q,2)*kernel(x,y)
            im = q*q*y/abs2(1-x,y)+b
            assert im == 0 and 1/re == Q(n,q)
            witnesses += 1
    chart = (('root',None),('center',(Q(0),Q(0))),('minus',(Q(-95,100),Q(0))),
             ('plusI',(Q(0),Q(95,100))),('minusI',(Q(0),Q(-95,100))),('plus',(Q(99,100),Q(0))))
    assert data['own_primary_order'] == [name for name,_ in chart]
    rows = []
    for row in data['levels']:
        q = row[data['columns'].index('q')]
        vals = row[data['columns'].index('own_primary')]
        for i,(_,w) in enumerate(chart[1:],1):
            d = 1/(6*q*kernel(*w))
            v = Q(vals[i]); tol = Q(1,10**12)
            # Printed sample interval intersects enlarged theoretical annular bound.
            assert 1+d*d <= (v+tol+d)**2
            u = v-tol-d
            assert u <= 0 or u*u <= 1+d*d
            numerical_checks += 1
        rows.append({'q':q,'guaranteed_centered_chart_radius':str(Q(19*q-30,19*q+30)),
                     'center_scaled_norm':vals[1]})
    return dict(diskChecks=disk_checks,thresholdChecks=threshold_checks,witnesses=witnesses,
                numericalChecks=numerical_checks,rows=rows)


if __name__ == '__main__':
    data = json.loads((Path(__file__).resolve().parent.parent/'cs_multiplier_locus_extended_20261126'/'results.json').read_text())
    print(json.dumps(verify(data),indent=2))
