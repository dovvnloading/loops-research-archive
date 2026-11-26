"""Validate and summarize raw numerical and rigorous certificate outputs."""
import argparse,json
from pathlib import Path
import mpmath as m

def read(path): return json.loads(Path(path).read_text())
def z(v): return m.mpc(*map(m.mpf,v))
def fmt(x): return f'{float(x):.12f}'
def fracbox(rec):
    s=1<<320;x,y,r=map(int,rec);k=10**12
    return [[(v-r)*k//s,-(-(v+r)*k//s)] for v in (x,y)]
def enc(r):
    return dict(period=r['period'],gap_lower_1e12=r['gap_lower_1e12'],rho_box_1e12=fracbox(r['multiplier']),selfmap_upper_1e12=r['selfmap_upper_1e12'],**({'scaled_norm_1e12':r['scaled_norm_1e12']} if 'scaled_norm_1e12' in r else {}))
def summary(lo,hi,grids,inputs,cert):
    m.mp.dps=100;assert [r['q'] for r in lo]==[r['q'] for r in hi]==[r['q'] for r in inputs]==[r['q'] for r in cert['levels']]
    assert [r['q'] for r in hi] in [list(range(3,9)),list(range(3,10))]
    assert cert['bits']==320
    byq={r['q']:r for r in grids};assert sorted(byq)==list(range(3,9))
    # Check all recorded residuals and corrections at their original stopping thresholds.
    for rows,dps in [(lo,50),(hi,80)]:
        tol=m.mpf(10)**(12-dps)
        for r in rows:
            for k in ('center_residual','center_correction','root_residual','root_correction','attachment_residual','attachment_correction'):
                assert m.mpf(r[k])<tol,(r['q'],dps,k,r[k])
            for _,e,c in r['edge_chart']: assert max(m.mpf(e),m.mpf(c))<tol
            u,v=map(m.mpf,r['attachment_ratios']);assert v<m.mpf('.0002') and v/u<m.mpf('.02')
            assert m.mpf(r['center_gap'])>tol**m.mpf('.4') and m.mpf(r['root_gap'])>tol**m.mpf('.4')
            for t in r['samples']:
                assert max(m.mpf(t['residual']),m.mpf(t['correction']))<tol
                assert m.mpf(t['primitive_gap'])>tol**m.mpf('.4') and m.mpf(t['disk_excess'])<=tol**m.mpf('.4')
    # Compare serialized candidates, continuous logarithms, and discrete diagnostics.
    err=scaled_err=m.mpf(0);levels=[];ambiguous=False;violations=[];edge_labels=['root','center','minus','plusI','minusI','plus']
    for l,h,inp,certrow in zip(lo,hi,inputs,cert['levels']):
        q,i,p,P=(h[k] for k in ('q','i','p','P'));assert p*q==P
        expected=[f'{name}-{j}' for j in range(i,len(hi)+1) for name in edge_labels]
        assert [t['label'] for t in l['samples']]==[t['label'] for t in h['samples']]==expected
        for key in ('root','center'): err=max(err,abs(z(l[key])-z(h[key])))
        for a,b in zip(l['samples'],h['samples']):
            assert a['ply_integer_shifts']==b['ply_integer_shifts'] and 0 in b['ply_integer_shifts']
            for key in ('c','point','rho','log_multiplier'): err=max(err,abs(z(a[key])-z(b[key])))
            scaled_err=max(scaled_err,q*abs(m.mpf(a['abs_z'])-m.mpf(b['abs_z'])))
            assert abs(m.log(z(b['rho']))/(2*m.pi*1j)-z(b['log_multiplier']))<m.mpf('1e-50')
        norm=lambda t:q*m.mpf(t['abs_z'])
        primary=[norm(t) for t in h['samples']];own={t['label'].split('-')[0]:norm(t) for t in h['samples'][:6]}
        assert abs(max(primary)-m.mpf(h['qL']))<m.mpf('1e-65')
        dense=[];density=[];failures=0;dense_amb=0
        for descendant in grids:
            if descendant['q']<q: continue
            assert descendant['N']==(128 if descendant['q']<=7 else 64)
            N=descendant['N'];keys={(t['j'],t['radius']) for t in descendant['samples']};failed={(t['j'],t['radius']) for t in descendant['failures']}
            assert len(keys)==len(descendant['samples']) and len(failed)==len(descendant['failures']) and not (keys&failed)
            assert keys|failed=={(j,r) for j in range(N) for r in ('.95','.99')}
            if descendant['q']==q:
                for n in (4,8,16,32,64,128):
                    if n>N: break
                    vv=[norm(t['ancestors'][i-1]) for t in descendant['samples'] if t['j']%(N//n)==0]
                    density.append([n,len(vv),fmt(max(vv)) if vv else None])
            failures+=len(failed)
            for t in descendant['samples']:
                b=t['ancestors'][i-1];assert 0 in b['ply_integer_shifts'];dense_amb+=len(b['ply_integer_shifts'])>1
                assert max(m.mpf(b['residual']),m.mpf(b['correction']),m.mpf(t['chart_residual']),m.mpf(t['chart_correction']))<m.mpf('1e-28')
                assert m.mpf(b['primitive_gap'])>m.mpf('1e-28')**m.mpf('.4') and m.mpf(b['disk_excess'])<=m.mpf('1e-28')**m.mpf('.4')
                dense.append(norm(b))
        # A conservative guard: nonunique PLY shifts at new levels count as ambiguity,
        # even if the numerical continuation agrees on the principal branch.
        amb=sum(len(t['ply_integer_shifts'])>1 for t in h['samples']);ambiguous|=q>=8 and (amb+dense_amb>0)
        vals=primary+dense
        if q>=8:
            violations.extend([q,fmt(x)] for x in vals if x<m.mpf('.9')-m.mpf('1e-10') or x>m.mpf('1.2')+m.mpf('1e-10'))
            assert all(m.mpf('.9')+m.mpf('1e-10')<x<m.mpf('1.2')-m.mpf('1e-10') for x in vals) or violations
        # Check the certificate input is the same numerical candidate.
        for name in ('root','center'): assert abs(z(inp[name])-z(h[name]))<m.mpf('1e-53')
        for name,label in [('root_point','root'),('center_point','center')]:
            t=next(t for t in h['samples'] if t['label']==f'{label}-{i}');assert abs(z(inp[name])-z(t['point']))<m.mpf('1e-53')
        assert certrow['center']['period']==P and certrow['root']['period']==p and certrow['dividing_at_center']['period']==p
        charts={t['label']:t for t in certrow['charts']};assert sorted(charts)==['minus','minusI','plus','plusI']
        ccert=enc(certrow['center']);rcert=enc(certrow['root']);dcert=enc(certrow['dividing_at_center']);pcert={k:dict(chart=enc(t['chart']),dividing=enc(t['dividing'])) for k,t in charts.items()}
        for label,cc in [('root',rcert),('center',dcert)]+[(k,t['dividing']) for k,t in pcert.items()]:
            a,b=cc['scaled_norm_1e12'];assert m.mpf(a)/10**12<=own[label]<=m.mpf(b)/10**12
        levels.append(dict(q=q,p=p,P=P,root=inp['root'],center=inp['center'],root_point=inp['root_point'],center_dividing_point=inp['center_point'],primary_count=len(primary),primary_max=fmt(max(primary)),primary_min=fmt(min(primary)),own_primary={k:fmt(v) for k,v in own.items()},dense_count=len(dense),dense_failures=failures,dense_own_grids=density,all_max=fmt(max(vals)),all_min=fmt(min(vals)),ply_ambiguous_primary=amb,ply_ambiguous_dense=dense_amb,center_certificate=ccert,root_certificate=rcert,dividing_center_certificate=dcert,chart_certificates=pcert))
    assert err<m.mpf('1e-22') and scaled_err<m.mpf('1e-10')
    verdict='PREDICTION FAILS' if violations else 'INCONCLUSIVE' if ambiguous else 'PREDICTION HOLDS'
    cols=['q','p','P','root','center','root_point','center_dividing_point','primary_count','primary_min','primary_max','own_primary','dense_count','dense_failures','dense_own_grids','all_min','all_max','ply_ambiguous_primary','ply_ambiguous_dense','certificates']
    certcols=['period','gap_lower_1e12','rho_box_1e12','selfmap_upper_1e12','scaled_norm_1e12']
    names=['root','center','minus','plusI','minusI','plus']
    def pack(c): return [c.get(k) for k in certcols]
    packed=[]
    for r in levels:
        r['own_primary']=[r['own_primary'][k] for k in names]
        r['certificates']=[pack(r['center_certificate']),pack(r['root_certificate']),pack(r['dividing_center_certificate'])]+[[pack(r['chart_certificates'][k]['chart']),pack(r['chart_certificates'][k]['dividing'])] for k in ['plus','minus','plusI','minusI']]
        packed.append([r[k] for k in cols])
    return dict(verdict=verdict,conservative_ply_guard=ambiguous,violations=violations,absolute_cross_precision_lt='1e-22',scaled_cross_precision_lt='1e-10',certificate_disk_scale='2^320',parameter_and_root_chart_point_radius='2^-150',dividing_point_radius='2^-110',certificate_units='1e-12',columns=cols,own_primary_order=names,dense_grid_columns=['angles_per_radius','accepted_count','max_scaled_norm'],certificate_columns=certcols,certificate_order=['center','root','dividing_at_center','plus_chart_and_dividing','minus_chart_and_dividing','plusI_chart_and_dividing','minusI_chart_and_dividing'],levels=packed)

def main():
    a=argparse.ArgumentParser();a.add_argument('low');a.add_argument('high');a.add_argument('dense7');a.add_argument('dense8');a.add_argument('inputs');a.add_argument('certs');a.add_argument('output');v=a.parse_args()
    res=summary(read(v.low),read(v.high),read(v.dense7)+read(v.dense8),read(v.inputs),read(v.certs));Path(v.output).write_text(json.dumps(res,indent=2,sort_keys=True)+'\n')
if __name__=='__main__': main()
