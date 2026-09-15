#!/usr/bin/env python3
"""Apply the actual-query adjacent average and classical change-of-measure bound.

Exact A recovery is the task in this analysis. It does not assert that every
allocation learner needs an exact-label pilot. Uses existing evidence, no new
Monte Carlo trials. The statistical lower bound is an analytic corollary, not
yet a Lean theorem about stopping times.
"""
import json
from pathlib import Path
from hashlib import sha256
import numpy as np
from experiment_d6_phase_boundary_cost import phase_parameters


def main():
    source=Path('research/d6_phase_boundary_20260908/growing_q_pilot.json')
    data=json.loads(source.read_text()); rows=[]
    for r in data['rows']:
        q,N=r['q'],r['N']; eta=1/(q*N)
        kl=(1-2*eta)*(np.log1p(-eta)-np.log(eta))
        lo=[]
        for side in [-1,1]:
            mu=phase_parameters(q)['mu_U']+side*r['epsilon']
            cap=.5*max(mu*mu/q,(1-mu)**2)
            lo.append(float(kl/cap))
        rows.append(dict(q=q,N=N,eta=eta,label_recovery_lower_min=min(lo),
            label_recovery_lower_max=max(lo),lower_fraction=max(lo)/N,
            scalar_pilot_samples=r['pilot_samples'],pilot_fraction=r['pilot_fraction'],
            pilot_over_lower=r['pilot_samples']/max(lo),
            qlog_qN_over_N=q*np.log(q*N)/N,
            known_A_lower_bound_applies_to_unknown_A=True))
    out=source.with_name('discovery_cost_bounds.json')
    out.write_text(json.dumps(dict(evidence_class='ANALYTIC_EXACT_LABEL_DISCOVERY_BOUNDS',
        source_sha256=sha256(source.read_bytes()).hexdigest(),
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,
        theorem='E_A tau >= kl(1-eta,eta) / (0.5*max(mu^2/q,(1-mu)^2))',
        source='https://www.jmlr.org/papers/volume17/kaufman16a/kaufman16a.pdf',
        scope=['Applies to algorithms uniformly eta-correct for exact hidden-set recovery.',
               'Assumes finite expected stopping time and actual variance-one Gaussian legal queries.',
               'Adjacent average and information accounting are Lean-certified; stopped change of measure is not.',
               'Does not establish a compulsory exact-label stage for low-regret allocation.']),indent=2)+'\n')
    for r in rows:
        if r['N']//r['q'] in [128,8192]: print({k:round(v,6) if isinstance(v,float) else v for k,v in r.items()})
    print(out)
if __name__=='__main__':main()
