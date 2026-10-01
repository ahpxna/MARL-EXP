"""Read saved closed-loop rows; no rollout, training, or source mutation."""
import json, hashlib, random, statistics
from collections import defaultdict
from pathlib import Path
ROOT=Path('/Users/phanan/cig-amf-main')
BASE=ROOT/'research/marl_budget'
MAIN=BASE/'cl_baselines_20260927_232931'
FIX=BASE/'cl_w2c_bin_20260927_234219'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def verified(p):
    m=json.loads((p/'manifest.json').read_text())
    assert m['status']=='COMPLETE'
    return {'status':m['status'],'listed_sources_match':{s:sha(ROOT/s)==h for s,h in m.get('source_hashes',{}).items()}}
def quantile(v,p):
    v=sorted(v); x=(len(v)-1)*p; a=int(x); b=min(a+1,len(v)-1)
    return v[a]+(x-a)*(v[b]-v[a])
def ci(v):
    rng=random.Random(917)
    a=[statistics.fmean(rng.choices(v,k=len(v))) for _ in range(10000)]
    return [quantile(a,.025),quantile(a,.975)]
rows=json.loads((MAIN/'rows.json').read_text())
extra=json.loads((FIX/'rows.json').read_text())
anchor={r['episode']:r for r in rows if r['method']=='prefix'}
assert len(anchor)==32
for r in extra:
    if r['method']=='prefix':
        assert all(r[k]==anchor[r['episode']][k] for k in ['queue_sum','finished','bytes'])
rows=[r for r in rows if r['method']!='where2comm_top2']+[r for r in extra if r['method']!='prefix']
groups=defaultdict(lambda:defaultdict(list))
for r in rows:
    groups[r['method'].split('/')[0]][r['episode']].append(r)
    if not r['method'].startswith('oracle'):
        assert not r['summary'].get('oracle_access_used')
eps=sorted(anchor)
means={}
for m,g in groups.items():
    assert sorted(g)==eps
    expected=3 if m in ['ctrl_history','mlp_top2_joint'] else 1
    assert all(len(g[e])==expected for e in eps)
    means[m]={e:{k:statistics.fmean(r[k] for r in g[e]) for k in ['queue_sum','finished','bytes']} for e in eps}
results={}
for m,g in means.items():
    out={'bytes_per_step':statistics.fmean(g[e]['bytes']/26 for e in eps)}
    for ref in ['prefix','ctrl_history']:
        vals=[100*(g[e]['queue_sum']/means[ref][e]['queue_sum']-1) for e in eps]
        clusters=defaultdict(list)
        for e,v in zip(eps,vals): clusters[e.split('_load')[0]].append(v)
        cl=[statistics.fmean(v) for v in clusters.values()]
        out['vs_'+ref]={'waiting_relative_pct':statistics.fmean(vals),'episode_bootstrap_ci95':ci(vals),
                       'traffic_seed_cluster_bootstrap_ci95':ci(cl),
                       'finished_mean_difference':statistics.fmean(g[e]['finished']-means[ref][e]['finished'] for e in eps),
                       'n_episodes':len(eps),'n_traffic_seeds':len(cl)}
    results[m]=out
direct={}
for name in ['direct_indep_ctrl_20260927_233023','direct_indep_t2j_20260927_233023']:
    p=BASE/name
    jj=[]
    for f in sorted(p.glob('job*.json')):
        j=json.loads(f.read_text()); learner=j['learner']
        z=j['results'][learner]['+84']['direct']
        jj.append({'learner':learner,'seed':j['seed'],'best_epoch':j['best_epoch'],
                   'opened_dev_gain':z['summary']['gain'],'tau':z['tau'],'job_sha256':sha(f)})
    direct[name]={'manifest':verified(p),'jobs':jj}
report={'evidence':'Independent reaggregation of saved data; negative waiting change is better. Seed-cluster CI is sensitivity analysis, not a changed preregistered endpoint.',
        'runs':{str(p.relative_to(ROOT)):{'manifest':verified(p),'rows_sha256':sha(p/'rows.json')} for p in [MAIN,FIX]},
        'pairing_anchor_reproduced':True,'dropped':'where2comm_top2: superseded exact-gap leak',
        'statistics':results,'independent_direct_development':direct}
out=ROOT/'research/papers/audits/MARL_PUBLICATION_AUDIT_NUMBERS_20260927.json'
out.write_text(json.dumps(report,indent=2)+'\n')
for m,r in results.items():
    a=r['vs_prefix'];b=r['vs_ctrl_history']
    print(m, 'prefix',round(a['waiting_relative_pct'],3),[round(x,3) for x in a['episode_bootstrap_ci95']],
          'control',round(b['waiting_relative_pct'],3),[round(x,3) for x in b['episode_bootstrap_ci95']],
          'bytes',round(r['bytes_per_step'],2))
for name,r in direct.items():
    print(name,[(j['seed'],j['best_epoch'],round(j['opened_dev_gain'],3)) for j in r['jobs']])
print('Saved',out)
