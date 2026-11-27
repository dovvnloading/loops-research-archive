#!/usr/bin/env python3
"""Adversarial controls for plausible but invalid finite certificates.

These target mathematical under-specification: a genuine polynomial root
with the wrong itinerary, the superattracting root of the same equation,
a previously rejected large radius, and unlinked width witnesses.
"""
from __future__ import annotations
from copy import deepcopy
import json
from pathlib import Path
from fractions import Fraction as Q
import verify_grid as V

HERE=Path(__file__).resolve().parent
CENTER='-1.78644006735907867869391347855285941123900799915244109679807489049281684366997363625543521097685575435335499458863335425194592151928555015993277501736469112971222076'
WRONG_ROOT='-1.78644144921332450690457991977933206876932537253693644871709743564556861286455556427888727686247657457514805204601248333155599466203771156317542923370691133095375855'

def root_only(row):
    p,q,r=row['word'];n=p*q*r;c=V.I(*row['parameter'])
    _,d,_=V.D3.iterate(c,6*n)
    deriv=d[3*n]+d[6*n]
    left,_,_=V.D3.iterate(V.I(c.lo,c.lo),6*n)
    right,_,_=V.D3.iterate(V.I(c.hi,c.hi),6*n)
    pl=left[3*n]+left[6*n];pr=right[3*n]+right[6*n]
    return ((pl.hi<0 and pr.lo>0) or (pr.hi<0 and pl.lo>0)) and (deriv.lo>0 or deriv.hi<0)

def set_chart(row,seed):
    b=V.bounds(seed);row['parameter']=[b.lo,b.hi]

def main():
    data=json.loads((HERE/'data.json').read_text());base=data['rows'][0]
    V.verify_row(base);V.check_width_witness(base)
    count=0
    def reject(name,change,expected=None,root_must_pass=False):
        nonlocal count
        row=deepcopy(base);change(row)
        if root_must_pass:
            assert root_only(row), f'{name}: weaker polynomial root test did not pass'
        try:
            V.verify_row(row);V.check_width_witness(row)
        except AssertionError as e:
            if expected is not None:
                assert expected in str(e),(name,str(e),expected)
            print('REJECT',name,':',str(e))
            count+=1
        else:
            raise AssertionError(f'accepted invalid certificate: {name}')

    def shift_root(row):
        lo,hi=row['parameter'];h=hi-lo
        row['parameter']=[lo+4*h,hi+4*h]
    reject('shifted root interval',shift_root,'endpoint root signs')
    reject('superattracting terminal root',lambda row:set_chart(row,CENTER),
           'terminal tip branch',True)
    reject('different genuine collision root',lambda row:set_chart(row,WRONG_ROOT),
           root_must_pass=True)
    reject('archived rejected radius 1/200',lambda row:row['radii'].__setitem__(2,[1,200]))
    reject('zero radius denominator',lambda row:row['radii'].__setitem__(2,[1,0]))
    reject('small alpha interval at zero',lambda row:row.__setitem__('alpha',[-1,1]),
           'fixed-point bracket')
    reject('wrong suffix reference',lambda row:row.__setitem__('reference2',row['reference1']),
           'depth-two reference identity')
    reject('reversed suffix reference',lambda row:row.__setitem__('reference2',row['reference2'][::-1]),
           'depth-two reference identity')
    reject('inflated log witness',lambda row:row['width'].__setitem__('log_v',[99,100]),
           'logarithm witness outside gate')
    def bad_angle(row):
        pair=row['width']['angles'][0]
        row['width']['angles'][0]=[V.rational_pair(V.parse_ratio(t)+Q(1,100)) for t in pair]
    reject('unlinked acos bracket',bad_angle,'acos Taylor witness')
    reject('false complementary square root',
           lambda row:row['width'].__setitem__('complement',[[1,100],[1,100]]),'complement sqrt')
    reject('inflated AGM square-root lower',
           lambda row:row['width']['agm']['klo'][0].__setitem__(0,[1,1]),
           'invalid AGM square-root bounds')
    reject('deflated AGM square-root upper',
           lambda row:row['width']['agm']['khi'][0].__setitem__(1,[1,100]),
           'invalid AGM square-root bounds')
    for name,change,expect in [
        ('missing grid word',lambda d:d['rows'].pop(),'incomplete or duplicated grid'),
        ('duplicated label',lambda d:d['rows'][1].__setitem__('word',[3,3,3]),'incomplete or duplicated grid'),
        ('overlapping root charts',lambda d:d['rows'][1].__setitem__('parameter',d['rows'][0]['parameter']),
         'parameter charts not pairwise disjoint')]:
        corrupted=deepcopy(data);change(corrupted)
        try: V.verify_data(corrupted)
        except AssertionError as e:
            assert expect in str(e),(name,str(e),expect)
            print('REJECT',name,':',str(e));count+=1
        else: raise AssertionError(f'accepted invalid grid: {name}')
    print(f'PASS: {count} adversarial certificate controls; two false candidates pass the isolated-root test.')

if __name__=='__main__':main()
