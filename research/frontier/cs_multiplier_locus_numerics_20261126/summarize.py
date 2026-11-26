"""Compact deterministic report; raw continuation records are regenerated separately."""
import argparse
import json
from pathlib import Path
import mpmath as m


def compact(raw):
    m.mp.dps=80
    fmt=lambda x: m.nstr(m.mpf(x),12)
    fields=['i','q','p','P','S','R','B','L','qL','L_over_B','center_displacement','center_z','max_z','max_sample','samples','ambiguous','root','center','attachment_ratios','center_gap']
    out={'columns':fields,'addresses':{},'verdict':raw['verdict']}
    for name in ('linear','bounded','square'):
        a=raw[name]; rows=[]
        for r in a['levels']:
            own=next(s for s in r['samples'] if s['label']==f"center-{r['i']}")
            win=next(s for s in r['samples'] if s['label']==r['max_sample'])
            rows.append([r[k] for k in fields[:4]]+[fmt(r[k]) for k in fields[4:11]]+
                [list(map(fmt,own['log_multiplier'])),list(map(fmt,win['log_multiplier'])),r['max_sample'],len(r['samples']),
                sum(len(s['ply_integer_shifts'])>1 for s in r['samples']),list(map(fmt,r['root'])),list(map(fmt,r['center'])),list(map(fmt,r['attachment_ratios'])),fmt(r['center_gap'])])
        checks={}
        for tag,key,dps in [('low','low_levels',50),('high','levels',80)]:
            res=[]; corr=[]
            for r in a[key]:
                for p in ('center','root','attachment'):
                    res.append(m.mpf(r[p+'_residual'])); corr.append(m.mpf(r[p+'_correction']))
                for _,e,c in r['edge_chart']:
                    res.append(m.mpf(e)); corr.append(m.mpf(c))
                for s in r['samples']:
                    res.append(m.mpf(s['residual'])); corr.append(m.mpf(s['correction']))
            limit=m.mpf(10)**(12-dps)
            assert max(res)<limit and max(corr)<limit
            checks[tag]={'max_residual_lt':f'1e{12-dps}','max_correction_lt':f'1e{12-dps}'}
            print(name,tag,'max residual',m.nstr(max(res),5),'max correction',m.nstr(max(corr),5))
        assert m.mpf(a['precision_agreement'])<m.mpf('1e-22')
        print(name,'max crossprecision difference',a['precision_agreement'])
        fits={}
        for k in ('fit_S','fit_q','low_fit_S','low_fit_q'):
            f=a[k]
            fits[k]=None if f is None else {'ols':fmt(f['ols']),'endpoint':fmt(f['endpoint']),'leave_one_out':list(map(fmt,f['leave_one_out'])) if f['leave_one_out'] else None}
        out['addresses'][name]={'rows':rows,'fits':fits,'checks':checks,'crossprecision_abs_diff_lt':'1e-22'}
    return out


def main():
    p=argparse.ArgumentParser(); p.add_argument('raw',type=Path); p.add_argument('output',type=Path)
    a=p.parse_args(); d=compact(json.loads(a.raw.read_text()))
    # Keep each measurement row on one line, preserving the JSON schema.
    lines=['{','  "columns": '+json.dumps(d['columns'])+',','  "addresses": {']
    for j,(name,v) in enumerate(d['addresses'].items()):
        lines+=['    '+json.dumps(name)+': {','      "rows": [']
        lines+=['        '+json.dumps(r)+(',' if i+1<len(v['rows']) else '') for i,r in enumerate(v['rows'])]
        lines+=['      ],','      "fits": '+json.dumps(v['fits'])+',','      "checks": '+json.dumps(v['checks'])+',','      "crossprecision_abs_diff_lt": '+json.dumps(v['crossprecision_abs_diff_lt']),'    }'+(',' if j+1<len(d['addresses']) else '')]
    lines+=['  },','  "verdict": '+json.dumps(d['verdict']),'}']
    a.output.write_text('\n'.join(lines)+'\n')


if __name__=='__main__': main()
