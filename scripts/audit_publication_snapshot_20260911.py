"""Read-only evidence audit; writes a separate snapshot, never promotes old runs."""
from __future__ import annotations
import ast
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
from datetime import datetime, timezone
import numpy as np
from scipy.stats import binom, binomtest

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'research/high_risk_20260910/publication_snapshot_20260911.json'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def median_interval(values, horizon=None):
    x = sorted(values); n = len(x)
    if not n: return None
    eligible = [k for k in range(1, n//2+1) if binom.cdf(k-1,n,.5) <= .025]
    if not eligible: return {'n': n, 'interval': None}
    k=max(eligible); lo,hi=float(x[k-1]),float(x[n-k])
    return {'n':n,'one_based_ranks':[k,n-k+1],'interval':[lo,hi],
            'upper_censored': horizon is not None and hi>horizon}

def corpus():
    rows=[];counts=Counter()
    for src in sorted((ROOT/'work/p13_conjectures').glob('*.lean')):
        log=src.with_suffix('.compile.log'); obj=src.with_suffix('.olean')
        row={'module':src.stem,'source_sha256':sha(src),'olean_exists':obj.exists()}
        if not log.exists():
            row['status']='NO_LOG';counts['NO_LOG']+=1
            counts['NO_LOG_WITH_OLEAN' if obj.exists() else 'NO_LOG_NO_OLEAN']+=1
        else:
            txt=log.read_text(errors='replace')
            audits=[{'name':n,'axioms':[a.strip() for a in ax.split(',') if a.strip()]}
                for n,ax in re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]",txt,re.M)]
            issues=[]
            if re.search(r':\d+:\d+: error(?:\(|:)|^error:',txt,re.M):issues.append('ERROR_IN_LOG')
            if 'sorryAx' in txt:issues.append('SORRY_IN_LOG')
            if any(set(a['axioms'])-ALLOWED for a in audits):issues.append('NONSTANDARD_AUDIT')
            if not obj.exists():issues.append('NO_OLEAN')
            elif obj.stat().st_mtime_ns<src.stat().st_mtime_ns:issues.append('STALE_OLEAN')
            if log.stat().st_mtime_ns<src.stat().st_mtime_ns:issues.append('STALE_LOG')
            if not audits:issues.append('NO_AXIOM_PRINT')
            row.update(status='LOGGED_ISSUES' if issues else 'CLEAN_LOGGED',issues=issues,
                audits=audits,compile_log_sha256=sha(log))
            counts[row['status']]+=1
            if not issues:counts['CLEAN_AUDIT_PRINTS']+=len(audits)
        rows.append(row)
    return {'total_modules':len(rows),'counts':dict(counts),'modules':rows,
        'scope':'Filesystem evidence only, not a clean build. Audit coverage is declaration-specific and transitive; NO_LOG is not proof of compilation. A failed elaboration may print sorryAx without a literal sorry in source.'}

def functional():
    script=ROOT/'scripts/run_functional_variance_stopping_lab_v4.py'
    spec=importlib.util.spec_from_file_location('f4_snapshot',script);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    outputs=[]
    for filename in ['functional_v4_ieee10seed_cellv1.json','functional_v4_shift50_cellv1.json']:
        path=ROOT/'research/confirm_ieee_20260911'/filename; d=json.loads(path.read_text());H=d['max_n']
        manifest=json.loads(Path(str(path)+'.manifest.json').read_text())
        assert sha(path)==manifest['artifact_sha']
        all_rows=d['runs_by_variant']; variants={}
        for v,rr in all_rows.items():
            keys=[(r['seed'],r['instance_id']) for r in rr];assert len(set(keys))==len(keys)
            assert all(r['certificate_emitted']==(r['N_certificate'] is not None) for r in rr)
            values=[H+1 if r['N_certificate'] is None else r['N_certificate'] for r in rr]
            assert values==[r['censored_N_certificate'] for r in rr]
            count=sum(r['certificate_emitted'] for r in rr)
            median=float(np.median(values));assert median==d['by_variant'][v]['median_N_certificate']
            assert count/len(rr)==d['by_variant'][v]['certificate_fraction']
            variants[v]={'runs':len(rr),'certified':count,'median_N':median,
                'median_CI_95':median_interval(values,H),'false_safe':sum(r['false_safe'] is True for r in rr)}
        a={(r['seed'],r['instance_id']):r for r in all_rows['C_anytime']};paired={}
        for v,rr in all_rows.items():
            if v=='C_anytime':continue
            pairs=[(a[(r['seed'],r['instance_id'])],r) for r in rr]
            assert all(x['world_sha256']==y['world_sha256'] for x,y in pairs)
            both=[(x['N_certificate'],y['N_certificate']) for x,y in pairs if x['certificate_emitted'] and y['certificate_emitted']]
            wins=sum(x<y for x,y in both);loss=sum(x>y for x,y in both)
            ratios=[y/x for x,y in both]
            paired[v]={'conditional_both_certified':len(both),'anytime_wins':wins,'anytime_losses':loss,
                'ties':len(both)-wins-loss,'only_anytime':sum(x['certificate_emitted'] and not y['certificate_emitted'] for x,y in pairs),
                'only_comparator':sum(y['certificate_emitted'] and not x['certificate_emitted'] for x,y in pairs),
                'conditional_sign_p':float(binomtest(wins,wins+loss,.5).pvalue) if wins+loss else None,
                'conditional_median_ratio':float(np.median(ratios)) if ratios else None,
                'conditional_ratio_CI_95':median_interval(ratios)}
        regen=0
        for w in d['worlds']:
            rng=np.random.default_rng(np.random.SeedSequence([w['seed'],w['instance_id'],0]))
            truth,sigma,perm,ext=mod._draw_world(rng,d['relations'],d['actions'],
                d['world_audit']['permute_relations'],d['world_audit']['random_extrema'],d['world_audit']['extrema_shift'])
            digest=hashlib.sha256(truth.astype('<f8').tobytes()+sigma.astype('<f8').tobytes()).hexdigest()
            assert digest==w['world_sha256'];regen+=1
        outputs.append({'path':str(path),'artifact_sha256':sha(path),'manifest':manifest,
            'world_audit':d['world_audit'],'regenerated_matching_worlds':regen,
            'rng_protocol':d['rng_protocol'],'max_n':H,'seeds':d['seeds'],
            'variants':variants,'paired_against_anytime':paired,
            'uniform_over_anytime_ratio_of_medians':variants['uniform']['median_N']/variants['C_anytime']['median_N'],
            'literature_baseline_C_lucb_present':'C_lucb' in all_rows,
            'admissibility':'Numeric evidence validated; prospective freeze and source-at-launch not established by seed equality or a post-hoc label correction.'})
    x=mod._instance_data(2026091101,0,5,6,7,'instance_cell_v1',extrema_shift=.5)
    y=mod._instance_data(2026091101,0,5,6,19,'instance_cell_v1',extrema_shift=.5)
    assert x[3]==y[3] and np.array_equal(x[2],y[2][:,:,:7])
    return {'script_sha256_at_audit':sha(script),'runs':outputs,'cross_horizon_prefix_smoke_passed':True,
        'findings':[
            'Both completed panels exclude C_lucb; current script contains it but these runs do not.',
            'extrema_shift is a pre-observation redraw, not a time-varying world or a test of recovery after locking on extrema.',
            'With five relations, round(0.5*5)=2: shift50 redraws two of five relation rows, not exactly half.',
            'Current admissibility_record labels the full seed tuple CONFIRMATORY irrespective of source/protocol freeze, horizon, or legacy RNG; matching seeds is necessary but insufficient.',
            'write_artifact_with_provenance fingerprints the working tree when writing results, not an immutable source snapshot taken at process launch.',
            'Oracle extrema uses extra information. Its realized sample counts need not dominate every deployable policy; it is not a proved computational or sample ceiling.',
            'Conditional paired wins and CI concern jointly certified cases, not unconditional stochastic domination.',
            'Random labels remove a benchmark leak; v3 zero false-safe was not logically guaranteed for noisy policies merely by fixed true labels.'
        ]}

def main():
    report={'created_utc':datetime.now(timezone.utc).isoformat(),'auditor_sha256':sha(Path(__file__)),
        'functional':functional(),'lean':corpus()}
    OUT.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'out':str(OUT),'lean':report['lean']['counts'],
        'functional':[{ 'file':Path(d['path']).name,'medians':{k:v['median_N'] for k,v in d['variants'].items()},
            'ratio':d['uniform_over_anytime_ratio_of_medians'],'paired_uniform':d['paired_against_anytime']['uniform'],
            'worlds_verified':d['regenerated_matching_worlds']} for d in report['functional']['runs']]},indent=2))
if __name__=='__main__':main()
