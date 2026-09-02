"""Cost-aware completion mechanics for an *available* PAEC-style certificate.

Important scope: the random certificate-family experiment below validates the
runtime mechanics corresponding to D6-B1--B6.  It is NOT evidence that an
arbitrary Top-C pair has a PAEC certificate; EveryTopCPairHasPAEC remains an
open theorem dependency.  The same runner also reproduces the actual D6-B7
first-order insufficiency witness from the Lean module.
"""
from __future__ import annotations
import argparse,itertools,json,sys
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.experimental_extensions import arbitrary_full_world,d6_diagnostics
from research_chains.reference import product_reference_surrogate
from research_chains.novelty_completion import choose_cost_aware_certificate,robust_linear_certificate_bound
from research_chains.provenance import write_artifact_with_provenance
PROTOCOL_VERSION='d6_cost_aware_paec_completion_v1'

def _b7():
    add=np.zeros((2,2,2),float); inter=np.zeros((2,2,2),float)
    for x in np.ndindex(2,2,2):
        add[x]=1.0 if x[0]==1 else 0.0
        inter[x]=1.0 if ((x[0]==0 and x[1]==1 and x[2]==1) or (x[0]==1 and x[1]==0 and x[2]==0)) else 0.0
    q={j:np.asarray([1.,0.]) for j in range(3)}
    wa,wi=arbitrary_full_world(add),arbitrary_full_world(inter)
    _,ra,_=product_reference_surrogate(wa,q); _,ri,_=product_reference_surrogate(wi,q)
    resp_diff=float(max(np.max(np.abs(np.asarray(a)-np.asarray(b))) for a,b in zip(ra,ri)))
    da,di=d6_diagnostics(wa,q,1),d6_diagnostics(wi,q,1)
    A={tuple(x) for x in da['exact_optimal_sets']}; I={tuple(x) for x in di['exact_optimal_sets']}
    return {'response_max_abs_diff':resp_diff,'same_first_order':bool(resp_diff<=1e-12),'additive_optimal_singletons':[list(x) for x in sorted(A)],
            'interaction_optimal_singletons':[list(x) for x in sorted(I)],'full_singleton_optima_disjoint':A.isdisjoint(I),
            'same_topc_selected':da['chosen_topc']==di['chosen_topc'],'interaction_topc_regret':di['true_decision_regret']}

def _one_completion(rng,n_atoms=8,n_cert=4):
    # Synthetic *valid-certificate* family for the B1--B6 mechanics.  Atoms
    # and coefficients use both signs; coefficient signs are aligned with the
    # sampled atom on certificate support so every exact RHS is positive.
    atom=rng.uniform(-2.0,2.0,size=n_atoms)
    atom[np.abs(atom)<.2]=np.where(atom[np.abs(atom)<.2] >= 0,.2,-.2)
    costs=rng.uniform(.5,3.0,size=n_atoms); family=[]
    exact_rhs=[]
    for _ in range(n_cert):
        alpha=np.zeros(n_atoms)
        supp=rng.choice(n_atoms,size=int(rng.integers(2,max(3,n_atoms//2+1))),replace=False)
        alpha[supp]=np.sign(atom[supp])*rng.uniform(.25,1.5,size=len(supp))
        raw=float(np.dot(alpha,atom))
        correction=-float(rng.uniform(0,.12*raw))
        rhs=raw+correction
        if rhs <= 0:
            raise AssertionError('synthetic valid-certificate generator produced non-positive RHS')
        family.append({'alpha':alpha.tolist(),'correction':correction})
        exact_rhs.append(rhs)
    # One decision gap is simultaneously certified by every member of the
    # family.  This checks that the runtime experiment is operating on valid
    # certificate objects rather than arbitrary linear forms.
    decision_gap=.40*float(min(exact_rhs))  # because certificate statement is 2D <= RHS
    certificate_sound=[2.0*decision_gap <= rhs+1e-12 for rhs in exact_rhs]
    radius=rng.uniform(.2,1.0,size=n_atoms); lower=atom-radius; upper=atom+radius
    measured=set(); paid=0.0
    exact_bounds=[robust_linear_certificate_bound(c['alpha'],atom,atom,c['correction']) for c in family]
    # Declared decision tolerance chosen so at least one supplied valid
    # certificate can close after enough measurements.  Since correction is at
    # most 12% of the raw RHS, 0.60*min(exact certificate RHS) is above the
    # fully measured conservative bound of the minimising certificate, while
    # still strictly above the constructed decision gap.
    eps=.60*float(min(exact_rhs))
    steps=0
    while steps<n_atoms:
        choice=choose_cost_aware_certificate(family,lower,upper,costs,measured)
        # Any supplied certificate may close the decision; switching is sound.
        if min(r['robust_bound'] for r in choice['rows']) <= eps+1e-12:
            break
        # A completed but non-closing certificate has zero width and would
        # otherwise be selected forever.  Exclude such dead-end certificates
        # from the *next probe* choice while keeping them in the valid family.
        incomplete=[]
        for row in choice['rows']:
            alpha=np.asarray(family[row['index']]['alpha'])
            candidates=[r for r in np.flatnonzero(np.abs(alpha)>1e-12) if int(r) not in measured]
            if candidates:
                incomplete.append((row,candidates))
        if not incomplete:
            break
        row,candidates=min(incomplete,key=lambda rc:(rc[0]['uncertainty_width'],rc[0]['remaining_cost'],rc[0]['index']))
        cert=family[row['index']]; alpha=np.asarray(cert['alpha'])
        r=max(candidates,key=lambda j:(abs(alpha[j])*(upper[j]-lower[j])/costs[j],-int(j)))
        paid+=float(costs[r]); measured.add(int(r)); lower[r]=upper[r]=atom[r]; steps+=1
    final_rows=choose_cost_aware_certificate(family,lower,upper,costs,measured)['rows']
    final_bound=float(min(r['robust_bound'] for r in final_rows))
    return {
        'paid_cost':paid,'measure_all_cost':float(np.sum(costs)),'measured_atoms':steps,
        'decision_gap':decision_gap,'all_certificates_sound':bool(all(certificate_sound)),
        'final_robust_bound':final_bound,'completion_target_bound':float(eps),
        'completed_to_target':bool(final_bound<=eps+1e-9),
        'signed_coefficients_present':bool(any(np.any(np.asarray(c['alpha'])<0) for c in family)),
    }

def run(instances=500,seed=0):
    rng=np.random.default_rng(seed); rows=[_one_completion(rng) for _ in range(int(instances))]
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),
            'scope':'B1-B6 certificate-completion mechanics conditional on an available valid certificate family; not PAEC-existence evidence',
            'EveryTopCPairHasPAEC_assumed':False,'b7_exact_reproduction':_b7(),
            'all_synthetic_certificate_families_sound':bool(all(r['all_certificates_sound'] for r in rows)),
            'all_completion_targets_reached':bool(all(r['completed_to_target'] for r in rows)),
            'signed_coefficient_cases_present':bool(any(r['signed_coefficients_present'] for r in rows)),
            'mean_paid_cost_fraction_of_measure_all':float(np.mean([r['paid_cost']/r['measure_all_cost'] for r in rows])),
            'median_measured_atoms':float(np.median([r['measured_atoms'] for r in rows])),
            'completion_target':'declared epsilon chosen above the decision gap and within reach of at least one supplied valid certificate',
            'rows':rows[:100]}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=500); p.add_argument('--seed',type=int,default=0); p.add_argument('--out',default='research/novelty_critical/d6_cost_aware_paec.json'); a=p.parse_args(argv)
    out=run(a.instances,a.seed); write_artifact_with_provenance(Path(a.out),out,protocol={'protocol_version':PROTOCOL_VERSION,'instances':a.instances},seed=a.seed,evidence_class='DEVELOPMENT_CERTIFICATE_MECHANICS_PLUS_EXACT_B7',chain='D6'); print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
