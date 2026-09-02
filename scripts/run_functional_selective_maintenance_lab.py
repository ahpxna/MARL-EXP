"""Selective certificate maintenance under relation-specific policy drift.

The synthetic panel is intentionally stratified by the *current Top-k boundary
reserve*.  The old version sampled generic Gaussian scores and then shifted all
selected relations by +1, which made most instances trivially safe without any
refresh.  That design could not test the proposed maintenance mechanism.  This
version creates small/moderate/large boundary-gap regimes while preserving a
valid current certificate, then asks for the exact minimum-cost subset of
relations whose drift allowance must be refreshed.
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.novelty_completion import selective_refresh_solution
from research_chains.certificates import topk_indices
from research_chains.provenance import write_artifact_with_provenance
PROTOCOL_VERSION='functional_selective_maintenance_v2'

_GAP_CENTRES={'small':0.16,'moderate':0.34,'large':0.80}


def _panel(rng,relations,topk,regime):
    """Construct a currently certified panel with controlled future reserve."""
    n=int(relations); k=int(topk)
    if not (0 < k < n):
        raise ValueError('topk must be strictly between 0 and relations')
    # Put the k-th / (k+1)-th scores at +/- gap/2, then move other relations
    # farther away from the boundary.  Random permutation prevents fixed IDs
    # from being privileged by the generator.
    gap=float(_GAP_CENTRES[regime]*rng.uniform(.88,1.12))
    selected=np.asarray([gap/2 + .22*i + rng.uniform(.0,.05) for i in range(k)][::-1],float)
    rejected=np.asarray([-gap/2 - .22*i - rng.uniform(.0,.05) for i in range(n-k)],float)
    base=np.concatenate([selected,rejected])
    perm=rng.permutation(n); base=base[perm]
    err=rng.uniform(.01,.035,size=n)
    lower=base-err; upper=base+err
    chosen=set(topk_indices(base,k)); rejected_ids=set(range(n))-chosen
    current_reserve=min(float(lower[j]-upper[l]) for j in chosen for l in rejected_ids)
    # The construction should be currently certified.  Keep an explicit guard
    # rather than silently accepting a broken synthetic instance.
    if current_reserve <= 0:
        raise AssertionError('generator failed to create a currently certified Top-k panel')
    # Boundary-near relations get the largest possible drift; far relations
    # get smaller drift.  Regime scaling creates cases needing 0, 1, or several
    # refreshes while retaining a meaningful easy regime.
    boundary_selected=min(chosen,key=lambda j:base[j])
    boundary_rejected=max(rejected_ids,key=lambda j:base[j])
    scale={'small':1.35,'moderate':1.00,'large':.55}[regime]
    drift=rng.uniform(.02,.16,size=n)*scale
    boundary_mult={
        'small':(.65,1.10),
        'moderate':(.30,.75),
        'large':(.05,.28),
    }[regime]
    drift[boundary_selected]=rng.uniform(*boundary_mult)*current_reserve
    drift[boundary_rejected]=rng.uniform(*boundary_mult)*current_reserve
    # Occasionally make one non-boundary relation consequential too.
    others=[j for j in range(n) if j not in (boundary_selected,boundary_rejected)]
    if others and rng.random()<.35:
        j=int(rng.choice(others)); drift[j]=max(drift[j],rng.uniform(.15,.55)*current_reserve)
    costs=rng.uniform(.5,2.0,size=n)
    return base,lower,upper,drift,costs,current_reserve


def run(instances=1000,seed=0,relations=8,topk=3):
    rng=np.random.default_rng(seed); rows=[]; false_safe=0; solvable=0
    regimes=tuple(_GAP_CENTRES)
    for idx in range(int(instances)):
        regime=regimes[idx%len(regimes)]
        base,lower,upper,drift,costs,current_reserve=_panel(rng,relations,topk,regime)
        # Record whether the certificate would remain safe if nothing were
        # refreshed; this makes the experiment test selective maintenance
        # rather than only reporting a cheap solution on already-safe worlds.
        no_refresh=selective_refresh_solution(lower,upper,drift,np.full(int(relations),1.0),int(topk))
        # The exact solver minimizes declared heterogeneous refresh cost.
        sol=selective_refresh_solution(lower,upper,drift,costs,int(topk))
        if not sol['safe']:
            continue
        solvable+=1; refresh=set(sol['refresh']); future=base.copy()
        # Idealized semantics used by the Lean/experiment proposal: refreshing
        # a relation resets its *future drift allowance*; unrefreshed leaves may
        # move anywhere inside their declared allowance.
        for j in range(int(relations)):
            if j not in refresh:
                future[j]+=rng.uniform(-drift[j],drift[j])
        old=set(topk_indices(base,int(topk))); new=set(topk_indices(future,int(topk)))
        bad=(old!=new); false_safe+=int(bad)
        rows.append({'gap_regime':regime,'current_boundary_reserve':current_reserve,
                     'refresh_fraction':sol['refresh_fraction'],'cost_fraction':sol['cost_fraction'],
                     'refresh_count':len(refresh),'no_refresh_safe':bool(no_refresh['refresh']==[] if no_refresh['safe'] else False),
                     'changed_topk':bad})
    by_regime={}
    for regime in regimes:
        rr=[r for r in rows if r['gap_regime']==regime]
        by_regime[regime]={
            'n':len(rr),
            'no_refresh_safe_fraction':float(np.mean([r['no_refresh_safe'] for r in rr])) if rr else None,
            'mean_refresh_fraction_vs_full':float(np.mean([r['refresh_fraction'] for r in rr])) if rr else None,
            'mean_refresh_cost_fraction_vs_full':float(np.mean([r['cost_fraction'] for r in rr])) if rr else None,
            'median_refresh_count':float(np.median([r['refresh_count'] for r in rr])) if rr else None,
        }
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'solvable_instances':solvable,'seed':int(seed),'relations':int(relations),'topk':int(topk),
            'gap_regimes':dict(_GAP_CENTRES),'false_safe_count':int(false_safe),'false_safe_rate':float(false_safe/max(1,solvable)),
            'no_refresh_safe_fraction':float(np.mean([r['no_refresh_safe'] for r in rows])) if rows else None,
            'mean_refresh_fraction_vs_full':float(np.mean([r['refresh_fraction'] for r in rows])) if rows else None,
            'mean_refresh_cost_fraction_vs_full':float(np.mean([r['cost_fraction'] for r in rows])) if rows else None,
            'median_refresh_count':float(np.median([r['refresh_count'] for r in rows])) if rows else None,
            'by_gap_regime':by_regime,
            'idealized_refresh_semantics':'refresh removes future drift allowance but preserves current score interval',
            'rows':rows[:100]}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=1000); p.add_argument('--seed',type=int,default=0); p.add_argument('--relations',type=int,default=8); p.add_argument('--topk',type=int,default=3); p.add_argument('--out',default='research/novelty_critical/functional_selective_maintenance.json'); a=p.parse_args(argv)
    out=run(a.instances,a.seed,a.relations,a.topk); write_artifact_with_provenance(Path(a.out),out,protocol={'protocol_version':PROTOCOL_VERSION,'relations':a.relations,'topk':a.topk,'gap_regimes':_GAP_CENTRES},seed=a.seed,evidence_class='DEVELOPMENT_SYNTHETIC_MAINTENANCE',chain='FUNCTIONAL'); print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
