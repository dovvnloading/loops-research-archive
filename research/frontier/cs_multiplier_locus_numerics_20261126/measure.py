"""Deterministic high-precision finite sample of CS dividing-cycle log multipliers."""
import argparse
import json
from pathlib import Path
import mpmath as m

ADDRESSES = {'linear': [3,4,5,6,7], 'bounded': [3]*5, 'square': [3,9,81]}


def jet(c,z,p):
    a,b,h,d = map(m.mpc,(1,0,0,0))
    for _ in range(p):
        h,d = 2*(a*a+z*h),2*(a*b+z*d)
        a,b = 2*z*a,2*z*b+1
        z = z*z+c
        if abs(z)>4: raise ArithmeticError('orbit escaped')
    return z,a,b,h,d


def first(c,z,p):
    a,b = m.mpc(1),m.mpc(0)
    for _ in range(p):
        a,b = 2*z*a,2*z*b+1
        z = z*z+c
        if abs(z)>4: raise ArithmeticError('orbit escaped')
    return z,a,b


def tol(): return m.mpf(10)**(12-m.mp.dps)


def chart(c,z,p,lam):
    for _ in range(30):
        f,a,b,h,d = jet(c,z,p)
        det=(a-1)*d-b*h
        dc=((a-1)*(a-lam)-h*(f-z))/det
        dz=(d*(f-z)-b*(a-lam))/det
        if max(abs(dc),abs(dz))<tol() and max(abs(f-z),abs(a-lam))<tol():
            return c,z,max(abs(f-z),abs(a-lam)),max(abs(dc),abs(dz))
        c,z=c-dc,z-dz
    raise ArithmeticError('chart Newton')


def track(c,z,p,start,end,n):
    t=m.mpf(0); step=m.mpf(1)/n; path=[]; residual=correction=m.mpf(0)
    while t<1:
        u=min(t+step,m.mpf(1))
        try: c1,z1,e,d=chart(c,z,p,start+(end-start)*u)
        except (ArithmeticError,ZeroDivisionError):
            step/=2
            if step<m.mpf('0.00001'): raise
            continue
        c,z,t=c1,z1,u; path.append(c)
        residual=max(residual,e); correction=max(correction,d)
        step=min(step*m.mpf('1.5'),m.mpf(1)/n)
    return c,z,path,residual,correction


def center(c,p):
    for _ in range(45):
        f,_,b=first(c,m.mpc(0),p); dc=f/b
        if abs(dc)<tol() and abs(f)<tol(): return c,abs(f),abs(dc)
        for j in range(16):
            c1=c-dc/(2**j)
            try: f1,_,_=first(c1,m.mpc(0),p)
            except ArithmeticError: continue
            if abs(f1)<abs(f): break
        else: raise ArithmeticError('center no descent')
        c=c1
    raise ArithmeticError('center Newton')


def gap(c,z,p):
    w=z; g=m.inf
    for j in range(1,p+1):
        w=w*w+c
        if j<p and p%j==0: g=min(g,abs(w-z))
    return g if p>1 else m.mpf(1)


def fixed(c,z,p):
    for _ in range(30):
        f,a,_=first(c,z,p); dz=(f-z)/(a-1)
        if abs(dz)<tol() and abs(f-z)<tol(): return z,a,abs(f-z),abs(dz)
        z-=dz
    raise ArithmeticError('fixed Newton')


def advance(c0,c1,state):
    p,z,a,angle,err,cor=state
    try:
        z1,a1,e,d=fixed(c1,z,p)
        da=m.arg(a1/a)
        if abs(da)>m.mpf('0.2') or abs(m.log(abs(a1/a)))>m.mpf('0.2'):
            raise ArithmeticError('large multiplier step')
        return p,z1,a1,angle+da,max(e,err),max(d,cor)
    except (ArithmeticError,ZeroDivisionError):
        mid=(c0+c1)/2
        if abs(c1-c0)<tol()*100: raise
        return advance(mid,c1,advance(c0,mid,state))


def follow(c0,path,states):
    for c in path:
        states=[advance(c0,c,s) for s in states]; c0=c
    return states


def num(x): return m.nstr(x,26)
def pair(z): return [num(z.real),num(z.imag)]


def observe(rows,states,c,label):
    for row,(p,z,a,angle,e,d) in zip(rows,states):
        q=row['q']; R=m.log(2)/(2*m.pi)*p/q
        w=angle/(2*m.pi)-1j*m.log(abs(a))/(2*m.pi)
        disk=abs(w-(m.mpf(1)/q-1j*R))-R
        g=gap(c,z,p)
        if g<tol()**m.mpf('0.4') or disk>tol()**m.mpf('0.4'):
            raise ArithmeticError('primitive or PLY check')
        if abs(w.real)>m.mpf('0.5'): raise ArithmeticError('nonprincipal lift')
        # Integer shifts of the continuous lift that also pass (32).
        shifts=[j for j in range(-int(m.ceil(R))-2,int(m.ceil(R))+3)
                if abs(w+j-(m.mpf(1)/q-1j*R))<=R+tol()**m.mpf('0.4')]
        row['samples'].append(dict(label=label,c=pair(c),point=pair(z),rho=pair(a),
            log_multiplier=pair(w),abs_z=num(abs(w)),disk_excess=num(disk),
            ply_integer_shifts=shifts,primitive_gap=num(g),residual=num(e),correction=num(d)))


def measure(qs,dps,n):
    m.mp.dps=dps;c=m.mpc(0);p=1;states=[];rows=[]
    for i,q in enumerate(qs,1):
        lam=m.exp(2*m.pi*1j/q)
        r,zr,path,re,rc=track(c,m.mpc(0),p,0,lam,n)
        f,a,b,h,d=jet(r,zr,p); deriv=d+h*b/(1-a)
        old=follow(c,path,states)
        P=p*q
        for fac in ('1','0.5','2','0.25','4','0.125','8','0.0625','16','0.03125'):
            try:
                child,ce,cc=center(r+lam/deriv*m.mpf(fac)/q**2,P)
                cg=gap(child,m.mpc(0),P)
                if cg<tol()**m.mpf('0.4'): raise ArithmeticError('nonprimitive center')
                near,zn,back,ae,ac=track(child,m.mpc(0),P,0,m.mpf('0.99'),n)
                nearer,zz,tail,be,bc=track(near,zn,P,m.mpf('0.99'),m.mpf('0.9999'),n)
                u,v=abs(near-r)/abs(child-r),abs(nearer-r)/abs(child-r)
                if not (v<m.mpf('0.0002') and v/u<m.mpf('0.02')):
                    raise ArithmeticError('wrong attachment')
                break
            except (ArithmeticError,ZeroDivisionError): continue
        else: raise ArithmeticError(f'no linked center at q={q}, P={P}')
        row=dict(i=i,q=q,p=p,P=P,root=pair(r),center=pair(child),seed_factor=fac,
            center_residual=num(ce),center_correction=num(cc),center_gap=num(cg),
            root_residual=num(re),root_correction=num(rc),root_gap=num(gap(r,zr,p)),
            attachment_ratios=[num(u),num(v)],attachment_residual=num(max(ae,be)),
            attachment_correction=num(max(ac,bc)),samples=[])
        rows.append(row)
        roots=old+[(p,zr,a,2*m.pi/q,re,rc)]
        observe(rows,roots,r,f'root-{i}')
        states=follow(r,
                      [nearer]+list(reversed((back+tail)[:-1]))+[child],roots)
        observe(rows,states,child,f'center-{i}')
        # Three other radial directions in the child multiplier disk, at |lambda|=.95.
        for name,target in [('minus',-m.mpf('.95')),('plusI',m.mpf('.95')*1j),('minusI',-m.mpf('.95')*1j)]:
            edge,_,ep,ee,ec=track(child,m.mpc(0),P,0,target,n)
            row.setdefault('edge_chart',[]).append([name,num(ee),num(ec)])
            observe(rows,follow(child,ep,states),edge,f'{name}-{i}')
        observe(rows,follow(child,back,states),near,f'plus-{i}')
        c,p=child,P
        print(f'{dps} dps: q={q}, P={P}',flush=True)
    for row in rows:
        q,p=row['q'],row['p']; S=m.mpf(p)/q; R=m.log(2)/(2*m.pi)*S
        B=m.sqrt(m.mpf(1)/q**2+R**2)+R
        winner=max(row['samples'],key=lambda s:m.mpf(s['abs_z'])); L=m.mpf(winner['abs_z'])
        own=next(s for s in row['samples'] if s['label']==f"center-{row['i']}")
        w=m.mpc(*map(m.mpf,own['log_multiplier']))
        row.update(S=num(S),R=num(R),B=num(B),L=num(L),max_sample=winner['label'],
            qL=num(q*L),L_over_B=num(L/B),center_displacement=num(abs(w-1/m.mpf(q))))
    return rows


def fit(rows,key):
    xs=[m.log(m.mpf(r[key])) for r in rows]; ys=[m.log(m.mpf(r['L'])) for r in rows]
    if len(set(xs))<2: return None
    def ols(x,y):
        a,b=m.fsum(x)/len(x),m.fsum(y)/len(y)
        return m.fsum((u-a)*(v-b) for u,v in zip(x,y))/m.fsum((u-a)**2 for u in x)
    loo=[ols(xs[:j]+xs[j+1:],ys[:j]+ys[j+1:]) for j in range(len(xs))
         if len(set(xs[:j]+xs[j+1:]))>1]
    return dict(ols=num(ols(xs,ys)),endpoint=num((ys[-1]-ys[0])/(xs[-1]-xs[0])),
                leave_one_out=[num(min(loo)),num(max(loo))] if loo else None)


def compare(low,high):
    err=m.mpf(0)
    for a,b in zip(low,high):
        assert (a['q'],a['P'])==(b['q'],b['P'])
        assert len(a['samples'])==len(b['samples'])
        for key in ('root','center'):
            err=max(err,abs(m.mpc(*map(m.mpf,a[key]))-m.mpc(*map(m.mpf,b[key]))))
        for s,t in zip(a['samples'],b['samples']):
            assert s['label']==t['label'] and s['ply_integer_shifts']==t['ply_integer_shifts']
            for key in ('c','rho','log_multiplier'):
                err=max(err,abs(m.mpc(*map(m.mpf,s[key]))-m.mpc(*map(m.mpf,t[key]))))
    assert err<m.mpf('1e-22'), f'precision disagreement {err}'
    return num(err)


def decision(data):
    rows=data['linear']['levels']; L=[m.mpf(r['L']) for r in rows]
    slope=m.mpf(data['linear']['fit_S']['ols'])
    if max(L[-2:])>m.mpf('.5') and L[-3]<L[-2]<L[-1] and slope>=m.mpf('.5'):
        return 'TRUE GEOMETRY DEGENERATES (sampled evidence only)'
    if max(L[-2:])<=m.mpf('.5') and max(m.mpf(r['qL']) for r in rows)<=3 and m.mpf(rows[-1]['L_over_B'])<=m.mpf('.05') and slope<=m.mpf('.25'):
        return 'ESTIMATE IS LOSSY (sampled evidence only)'
    return 'INCONCLUSIVE'


def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--output',type=Path,default=Path(__file__).with_name('results.json'))
    args=parser.parse_args(); data={}
    for name,qs in ADDRESSES.items():
        low=measure(qs,50,8); high=measure(qs,80,16)
        data[name]=dict(levels=high,low_levels=low,precision_agreement=compare(low,high),
                        fit_S=fit(high,'S'),fit_q=fit(high,'q'),low_fit_S=fit(low,'S'),low_fit_q=fit(low,'q'))
    data['verdict']=decision(data)
    args.output.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')


if __name__=='__main__': main()
