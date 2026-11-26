"""Generate numerical seeds for interval certification of primary chart samples."""
import argparse,json
from pathlib import Path
import mpmath as m
from extend import load,PRIOR,parse,dump

def generate(s,raw):
    m.mp.dps=80;rows=[]
    for row in raw:
        i,q,p,P=[row[k] for k in ('i','q','p','P')]
        center=parse(row['center']);root=next(t for t in row['samples'] if t['label']==f'root-{i}');own=next(t for t in row['samples'] if t['label']==f'center-{i}')
        def roundpair(v): return [m.nstr(m.mpf(x),55) for x in v]
        v={k:row[k] for k in ('q','p','P')};v.update(root=roundpair(row['root']),center=roundpair(row['center']),root_point=roundpair(root['point']),center_point=roundpair(own['point']),charts=[])
        for label,target in [('plus',['.99','0']),('minus',['-.95','0']),('plusI',['0','.95']),('minusI',['0','-.95'])]:
            t=next(t for t in row['samples'] if t['label']==f'{label}-{i}');c0=parse(t['c']);lam=parse(target)
            try:
                z0,_,_,_=s.fixed(c0,m.mpc(0),P);c,z,_,_=s.chart(c0,z0,P,lam)
                if abs(c-c0)>m.mpf('1e-55'): raise ArithmeticError('chart mismatch')
            except (ArithmeticError,ZeroDivisionError): c,z,_,_,_=s.track(center,m.mpc(0),P,0,lam,16)
            assert abs(c-c0)<m.mpf('1e-55'), (q,label,'parameter mismatch')
            v['charts'].append(dict(label=label,c=roundpair(s.pair(c)),point=roundpair(s.pair(z)),target=target,dividing_point=roundpair(t['point'])))
        rows.append(v);print('chart seeds',q,flush=True)
    return rows

def main():
    a=argparse.ArgumentParser();a.add_argument('raw');a.add_argument('output');a.add_argument('--prior',type=Path,default=PRIOR);a.add_argument('--fast');v=a.parse_args();dump(v.output,generate(load(v.prior,v.fast),json.loads(Path(v.raw).read_text())))
if __name__=='__main__': main()
