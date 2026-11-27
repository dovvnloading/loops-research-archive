#!/usr/bin/env python3
"""Numerical search only. All output must pass the independent rational verifier.

Track the polynomial tip equation through a homotopy from the quadratic
normal form to the actual p-return. Numerical continuation is not evidence.
"""
from __future__ import annotations
import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import mpmath as mp

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod

old = load('depth2_search_source', ROOT / 'research/independent_audits/tip_family_renormalization_depth_20261116/verify.py')

def orbit(c, n):
    x = d = a = da = mp.mpf(0)
    for j in range(n):
        if j == 0:
            an, dan = mp.mpf(1), mp.mpf(0)
        else:
            an, dan = 2*x*a, 2*d*a + 2*x*da
        x, d = x*x+c, 2*x*d+1
        a, da = an, dan
    return x, d, a, da

def chart(c, p):
    x, d, a, da = orbit(c, p)
    return a, da, a*x, da*x+a*d

def residual(c, p, k, s, want_signs=False, want_slope=False):
    a, da, q, dq = chart(c, p)
    v = dv = sv = mp.mpf(0)
    v3 = dv3 = sv3 = None
    signs=[]
    for j in range(6*k):
        z, dz, sz = v/a, dv/a-v*da/(a*a), sv/a
        for _ in range(p):
            z, dz, sz = z*z+c, 2*z*dz+1, 2*z*sz
        v, dv, sv = ((1-s)*(v*v+q)+s*a*z,
                 (1-s)*(2*v*dv+dq)+s*(da*z+a*dz),
                 (1-s)*2*v*sv+s*a*sz+(a*z-v*v-q))
        signs.append(1 if v>0 else -1)
        if j+1 == 3*k:
            v3, dv3, sv3 = v, dv, sv
    if want_slope: return -(sv+sv3)/(dv+dv3)
    return signs if want_signs else (v+v3, dv+dv3)

def newton(fun, c, maxsteps=30, tolerance=None):
    tolerance = tolerance or mp.mpf('1e-120')
    for j in range(maxsteps):
        v, d = fun(c)
        step = v/d
        c -= step
        if abs(step) < tolerance:
            return c
        if not mp.isfinite(c):
            raise ValueError('nonfinite Newton iterate')
    raise ValueError('Newton failed')

def seed(p, q, r, verbose=False):
    target = mp.mpf(old.REFERENCE_TIPS[r])
    c0 = mp.mpf(old.SEEDS[p,q])
    p = p*q
    c = newton(lambda c: (chart(c,p)[2]-target, chart(c,p)[3]), c0)
    if verbose: print('initial',p,q,r,mp.nstr(c,35), flush=True)
    target_signs=residual(c,p,r,mp.mpf(0),True)
    s, ds = mp.mpf(0), mp.mpf('0.002')
    steps=0
    while s < 1:
        slope=residual(c,p,r,s,want_slope=True)
        sn=min(mp.mpf(1),s+ds)
        try:
            cn=newton(lambda c:residual(c,p,r,sn), c+slope*(sn-s))
            # Require a small normalized parameter step. This is only a
            # search guard; final kneading and rational signs are decisive.
            if residual(cn,p,r,sn,True) != target_signs:
                raise ValueError('kneading jump')
            if abs(chart(cn,p)[2]-chart(c,p)[2]) > mp.mpf('0.001'):
                raise ValueError('branch jump')
        except (ValueError, ZeroDivisionError, OverflowError):
            ds/=2
            if ds < mp.mpf('1e-8'): raise
            continue
        c,s=cn,sn
        steps+=1
        if steps%25==0 and verbose: print('homotopy',p,q,r,mp.nstr(s,6),flush=True)
        ds=min(ds*mp.mpf('1.15'),mp.mpf('0.02'))
    return c, steps

def exact_residual(c,n):
    x=d=mp.mpf(0)
    for j in range(6*n):
        x,d=x*x+c,2*x*d+1
        if j+1==3*n: x3,d3=x,d
    return x+x3,d+d3

def alpha(c,n):
    a=orbit(c,n)[2]
    def fn(u):
        z=-u/a;dz=-1/a
        for _ in range(n):z,dz=z*z+c,2*z*dz
        return -a*z-u,-a*dz-1
    return newton(fn,mp.mpf('.94'))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--word',nargs=3,type=int)
    parser.add_argument('--dps',type=int,default=180)
    parser.add_argument('--verbose',action='store_true')
    args=parser.parse_args()
    mp.mp.dps=args.dps
    words=[tuple(args.word)] if args.word else list(itertools.product((3,4,5),repeat=3))
    path=HERE/'numerical_seeds.json'
    rows=json.loads(path.read_text()) if path.exists() else {}
    for p,q,r in words:
        key=f'{p}{q}{r}'
        if key in rows: continue
        c,steps=seed(p,q,r,args.verbose)
        c=newton(lambda c:exact_residual(c,p*q*r),c)
        al=alpha(c,p*q*r)
        rows[key]={'word':[p,q,r], 'seed':mp.nstr(c,args.dps-15),
            'alpha':mp.nstr(al,args.dps-15), 'homotopy_steps':steps}
        path.write_text(json.dumps(rows,indent=2)+'\n')
        print(key, mp.nstr(c,45), 'steps',steps,flush=True)

if __name__=='__main__':main()
