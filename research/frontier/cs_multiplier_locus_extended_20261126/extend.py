"""Finite locus test using merged #139 Newton and continuation routines."""
import argparse, ctypes, importlib.util, json
from pathlib import Path
import mpmath as m
HERE=Path(__file__).resolve().parent
PRIOR=HERE.parent/'cs_multiplier_locus_numerics_20261126'/'measure.py'
def load(path,fast):
    spec=importlib.util.spec_from_file_location('cs139',path)
    s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
    if fast:
        fn=ctypes.CDLL(str(Path(fast).resolve())).csjet
        fn.argtypes=[ctypes.c_char_p]*4+[ctypes.c_int]*3;fn.restype=ctypes.c_char_p
        def calc(c,z,p,second):
            v=fn(*(m.nstr(x,m.mp.dps+5).encode() for x in (c.real,c.imag,z.real,z.imag)),p,m.mp.dps,second)
            if v==b'escape': raise ArithmeticError('escaped')
            x=list(map(m.mpf,v.decode().split()));return tuple(m.mpc(x[i],x[i+1]) for i in range(0,10,2))
        s.jet=lambda c,z,p:calc(c,z,p,1)
        s.first=lambda c,z,p:calc(c,z,p,0)[:3]
    s.num=lambda x:m.nstr(x,m.mp.dps-8)
    return s

def parse(v): return m.mpc(*map(m.mpf,v))
def dump(out,data): Path(out).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
def dense(s,src,out,max_q,N,n,min_q=3):
    m.mp.dps=40;rows=[];base=json.loads(Path(src).read_text())
    for row in base:
        q,p,P,i=(row[k] for k in ('q','p','P','i'))
        if q>max_q: break
        if q<min_q: continue
        child,_,_=s.center(parse(row['center']),P);ss=[]
        for a in base[:i]:
            t=next(t for t in a['samples'] if t['label']==f'center-{i}')
            z,rho,e,d=s.fixed(child,parse(t['point']),a['p'])
            angle=m.mpf(t['log_multiplier'][0])*2*m.pi+m.arg(rho/parse(t['rho']))
            ss.append((a['p'],z,rho,angle,e,d))
        result=dict(q=q,P=P,N=N,n=n,samples=[],failures=[])
        for j in sorted(range(N),key=lambda j:(0 if j==0 else -(j&-j),j)):
            for radius in ('.95','.99'):
                try:
                    target=m.mpf(radius)*m.exp(2*m.pi*1j*j/N)
                    edge,ez,ep,ee,ec=s.track(child,m.mpc(0),P,0,target,n)
                    tmp=[dict(q=a['q'],samples=[]) for a in base[:i]]
                    s.observe(tmp,s.follow(child,ep,ss),edge,f'{j}/{N}@{radius}')
                    result['samples'].append(dict(j=j,radius=radius,chart_point=s.pair(ez),chart_residual=s.num(ee),chart_correction=s.num(ec),ancestors=[a['samples'][0] for a in tmp]))
                except (ArithmeticError,ZeroDivisionError) as e: result['failures'].append(dict(j=j,radius=radius,error=str(e)))
        rows.append(result);dump(out,rows);print('dense',q,len(result['samples']),len(result['failures']),flush=True)
def main():
    a=argparse.ArgumentParser();a.add_argument('--prior',type=Path,default=PRIOR);a.add_argument('--fast');a.add_argument('--output',required=True);a.add_argument('--dps',type=int,default=80);a.add_argument('--steps',type=int,default=16);a.add_argument('--max-q',type=int,default=8);a.add_argument('--dense-from');a.add_argument('--grid',type=int,default=16);a.add_argument('--min-q',type=int,default=3);v=a.parse_args();s=load(v.prior,v.fast)
    if v.dense_from: dense(s,v.dense_from,v.output,v.max_q,v.grid,v.steps,v.min_q)
    else: dump(v.output,s.measure(list(range(3,v.max_q+1)),v.dps,v.steps))
if __name__=='__main__': main()
