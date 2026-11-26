#!/usr/bin/env python3
"""Exact arithmetic regressions for the satellite-component Julia bound.

No dynamical computation or source theorem verification is performed here.
"""
from fractions import Fraction as F
import json


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def neg(a):
    return (-a[0], -a[1])


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0])


def norm2(a):
    return a[0]**2 + a[1]**2


def div(a, b):
    n = norm2(b)
    v = mul(a, (b[0], -b[1]))
    return (v[0]/n, v[1]/n)


ONE = (F(1), F(0))
SAMPLES = {
    'center': (F(0), F(0)), 'plus': (F(99, 100), F(0)),
    'minus': (F(-19, 20), F(0)), 'plusI': (F(0), F(19, 20)),
    'minusI': (F(0), F(-19, 20)),
}


def T(lam):
    return norm2(sub(ONE, lam))/(1-norm2(lam))


def principal_sufficient(q, t):
    # pi > 3: T/q^2 < pi*(1-2/q) for theta=2*pi/q.
    return t < 3*q*(q-2)


def prediction_sufficient(q, t):
    # b=T/(2*pi*q) < T/(6*q); 19/180 ensures [0.9,1.2].
    return t/(6*q) <= F(19, 180)


def model(q, R, t, lam):
    # lambda_*=(1+i*t)/(1-i*t), H(lambda_*)=i/t.
    C = (1/(2*R), -F(q*q, 2)/t)
    numerator = sub(ONE, lam)
    denominator = add(mul((F(q*q, 2), F(0)), add(ONE, lam)),
                      mul(C, numerator))
    return div(numerator, denominator)


def main():
    expected = [F(1), F(1, 199), F(39), F(761, 39), F(761, 39)]
    require([T(l) for l in SAMPLES.values()] == expected, 'sample factors')
    table = []
    for q in range(3, 10):
        for label, lam in SAMPLES.items():
            t = T(lam)
            table.append({'q': q, 'label': label, 'T': str(t),
                          'log_disk_radius': str(t/q**2),
                          'principal_sufficient_pi_gt_3': principal_sufficient(q, t),
                          'prediction_sufficient_pi_gt_3': prediction_sufficient(q, t)})
    require(all(r['principal_sufficient_pi_gt_3'] for r in table if r['q'] == 9),
            'q=9 principal lift bound')
    require(all(r['prediction_sufficient_pi_gt_3'] for r in table
                if r['label'] in ('center', 'plus')), 'center/plus prediction')
    require(principal_sufficient(5, F(39)) and principal_sufficient(10, F(199)),
            'compact-disk principal thresholds')
    require(prediction_sufficient(62, F(39)) and not prediction_sufficient(61, F(39)),
            'r=.95 sufficient prediction threshold')
    require(prediction_sufficient(315, F(199)) and not prediction_sufficient(314, F(199)),
            'r=.99 sufficient prediction threshold')
    cases = 0
    for q in (3, 9, 100):
        for R in (F(1, 100), F(1), F(10**6)):
            for t in (F(1, 1000), F(1, 7), F(-1, 3)):
                target = div((F(1), t), (F(1), -t))
                require(norm2(target) == 1 and target != ONE, 'unit target')
                require(model(q, R, t, ONE) == (0, 0), 'root')
                require(model(q, R, t, target) == (2*R, 0), 'boundary saturation')
                for lam in SAMPLES.values():
                    u = model(q, R, t, lam)
                    require(u[0] > 0 and norm2(u) < 2*R*u[0], 'PLY disk')
                    require(norm2(u) <= 2*T(lam)*u[0]/q**2, 'Julia disk')
                    cases += 1
    print(json.dumps({'scope': 'exact rational checks only; not a dynamics certificate',
                      'sample_bounds': table, 'model_interior_checks': cases}, indent=2))


if __name__ == '__main__':
    main()
