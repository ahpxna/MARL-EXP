"""Support-family/scale utility lab for the operational MASTER certificate."""
from __future__ import annotations
import argparse,itertools,json,resource,time
from pathlib import Path
import sys
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.certificates import exact_optimum,global_extremizability_defect,lp_lower_bound,topk_indices,zeta_def
from research_chains.finite_world import FiniteResponseWorld
from research_chains.pairwise import operational_gamma
from research_chains.experimental_extensions import box_gamma_diagnostics
from research_chains.provenance import write_artifact_with_provenance
from research_chains.support import SupportModel

PROTOCOL_VERSION='master_certificate_utility_v2'
PROMOTION_FAMILIES=('cartesian','coextremizable','weak_coupling','moderate_coupling','strong_coupling','cancellation','nonnested','random_sparse','learned_noisy')
LEGACY_ONLY_FAMILIES=('support_uncertainty',)
FAMILIES=PROMOTION_FAMILIES+LEGACY_ONLY_FAMILIES

def _support(rng,m,family):
    full=list(itertools.product((0,1),repeat=m))
    if family=='cartesian': omega=full
    elif family=='coextremizable': omega=[(0,)*m,(1,)*m]+[a for a in full if rng.random()<.1]
    elif family in ('weak_coupling','moderate_coupling','strong_coupling'):
        keep={'weak_coupling':.8,'moderate_coupling':.5,'strong_coupling':.25}[family]; omega=[a for a in full if rng.random()<keep]
    elif family=='cancellation': omega=[a for a in full if sum(a)%2==0]
    elif family=='nonnested': omega=[a for a in full if (sum(a[:max(1,m//2)])<=1 or sum(a[max(1,m//2):])>=max(1,m//2)-1)]
    else: omega=[a for a in full if rng.random()<min(.4,12/len(full))]
    omega=set(omega); omega.update(((0,)*m,(1,)*m))
    for j in range(m):
        for u in (0,1):
            if not any(a[j]==u for a in omega): omega.add(tuple(u if x==j else 0 for x in range(m)))
    return SupportModel((2,)*m,tuple(sorted(omega)),key=family)

def _cell(rng,m,k,family,tolerance,solver_cell_limit,exact_work_limit,active_gamma='op'):
    support=_support(rng,m,family); primitives=tuple(rng.normal(size=2) for _ in range(m))
    if family=='cancellation': primitives=tuple(np.asarray([0.,(-1.)**j*(1+j/m)]) for j in range(m))
    world=FiniteResponseWorld(support,primitives); truth=world.component_spans()
    noise=rng.normal(scale=.08,size=m) if family=='learned_noisy' else rng.normal(scale=.02,size=m)
    estimate=truth+noise; error=np.abs(noise)+1e-12; selected=topk_indices(estimate,k)
    candidate=world.additive_radius(selected); combos=math_comb(m,k); work=combos*len(support.omega)
    exact_status='unavailable_scale'; exact=None; exact_seconds=None; exact_sets=None
    if work<=exact_work_limit:
        t=time.perf_counter(); exact,exact_sets=exact_optimum(world,k); exact_seconds=time.perf_counter()-t; exact_status='optimal'
    lp_status='unavailable_scale'; lp=None; lp_seconds=None; nodes=None
    if len(support.omega)<=solver_cell_limit:
        try:
            t=time.perf_counter(); lp,res=lp_lower_bound(world,k); lp_seconds=time.perf_counter()-t; lp_status='optimal'
            nodes=getattr(res,'mip_node_count',None)
        except Exception as exc: lp_status=f'failed_closed:{type(exc).__name__}'
    cert_started=time.perf_counter(); E=global_extremizability_defect(world)
    zeta=zeta_def(world,k) if work<=exact_work_limit else None
    gamma_op=operational_gamma(estimate,error,k,selected)
    box=box_gamma_diagnostics(estimate,error,k,selected)
    gamma_box=float(box['box_gamma'])
    geometry=E/2 if zeta is None else min(E/2,zeta/2)
    certificate_op=float(gamma_op+geometry)
    certificate_box=float(gamma_box+geometry)
    if active_gamma not in ('op','box'):
        raise ValueError("active_gamma must be 'op' or 'box'")
    certificate=certificate_op if active_gamma=='op' else certificate_box
    certificate_seconds=time.perf_counter()-cert_started
    regret=None if exact is None else candidate-exact
    return {'family':family,'m':m,'k':k,'support_cells':len(support.omega),'candidate':'Top-C',
        'candidate_loss':candidate,'exact_status':exact_status,'exact_optimum':exact,'exact_seconds':exact_seconds,
        'lp_status':lp_status,'lp_lower_bound':lp,'lp_seconds':lp_seconds,'solver_nodes':nodes,
        'zeta_half':None if zeta is None else zeta/2,'E_half':E/2,'regret':regret,
        'zeta_slack':None if regret is None or zeta is None else zeta/2-regret,
        'E_slack':None if regret is None else E/2-regret,
        'lp_slack':None if lp is None else candidate-lp,
        'gamma_operational':float(gamma_op),'gamma_box':float(gamma_box),
        'gamma_box_over_operational':float(gamma_box/max(float(gamma_op),1e-15)),
        'gamma_box_strict_tightening':bool(gamma_box<float(gamma_op)-1e-12),
        'certificate_operational':certificate_op,'certificate_box':certificate_box,
        'active_gamma':active_gamma,'certificate':certificate,
        'certificate_geometry':'min(E/2,zeta/2)' if zeta is not None else 'E/2',
        'covered':None if regret is None else bool(regret<=certificate+1e-10),
        'covered_operational':None if regret is None else bool(regret<=certificate_op+1e-10),
        'covered_box':None if regret is None else bool(regret<=certificate_box+1e-10),
        'false_safe':None if regret is None else bool(certificate<=tolerance and regret>tolerance+1e-10),
        'false_safe_operational':None if regret is None else bool(certificate_op<=tolerance and regret>tolerance+1e-10),
        'false_safe_box':None if regret is None else bool(certificate_box<=tolerance and regret>tolerance+1e-10),
        'fallback':bool(certificate>tolerance),
        'fallback_operational':bool(certificate_op>tolerance),'fallback_box':bool(certificate_box>tolerance),
        'family_semantics_warning':('legacy label: generated by generic sparse support, not an Omega-/Omega+ uncertainty bracket'
            if family=='support_uncertainty' else None),
        'certificate_seconds':certificate_seconds,
        'always_exact_seconds':exact_seconds,'ram_maxrss':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}

def math_comb(n,k):
    import math
    return math.comb(int(n),int(k))

def run(seed=0,instances=2,ms=(3,4,6,8,12,16),tolerances=(0,.01,.02,.05,.1,.2,.3,.5,1),families=PROMOTION_FAMILIES,solver_cell_limit=4096,exact_work_limit=2_000_000,active_gamma='op'):
    rng=np.random.default_rng(int(seed)); rows=[]
    for m in map(int,ms):
        ks=sorted({k for k in (1,2,m//2,m-2) if 0<k<m})
        for family in families:
            for k in ks:
                for _ in range(int(instances)):
                    base=_cell(rng,m,k,family,max(tolerances),solver_cell_limit,exact_work_limit,active_gamma)
                    for tol in tolerances:
                        row=dict(base); row['tolerance']=float(tol)
                        row['fallback']=bool(base['certificate']>tol)
                        row['fallback_operational']=bool(base['certificate_operational']>tol)
                        row['fallback_box']=bool(base['certificate_box']>tol)
                        row['false_safe']=None if base['regret'] is None else bool(base['certificate']<=tol and base['regret']>tol+1e-10)
                        row['false_safe_operational']=None if base['regret'] is None else bool(base['certificate_operational']<=tol and base['regret']>tol+1e-10)
                        row['false_safe_box']=None if base['regret'] is None else bool(base['certificate_box']<=tol and base['regret']>tol+1e-10)
                        rows.append(row)
    return {'protocol_version':PROTOCOL_VERSION,'evidence_class':'DEVELOPMENT_EMPIRICAL','seed':int(seed),
        'families':list(families),'m_grid':list(map(int,ms)),'tolerances':list(map(float,tolerances)),
        'active_gamma':active_gamma,'paired_gamma_evaluation':True,'rows':rows,
        'solver_policy':'non-optimal/failed/unavailable status never treated as a lower bound',
        'family_policy':'support_uncertainty is legacy-only and excluded from default promotion evidence',
        'milp_status':'NOT_IMPLEMENTED; exact enumeration and LP are reported separately'}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--seed',type=int,default=0); p.add_argument('--instances',type=int,default=2)
    p.add_argument('--m-grid',nargs='+',type=int,default=[3,4,6,8,12,16]); p.add_argument('--families',nargs='+',choices=FAMILIES,default=list(PROMOTION_FAMILIES))
    p.add_argument('--tolerances',nargs='+',type=float,default=[0,.01,.02,.05,.1,.2,.3,.5,1]); p.add_argument('--solver-cell-limit',type=int,default=4096); p.add_argument('--exact-work-limit',type=int,default=2_000_000)
    p.add_argument('--active-gamma',choices=['op','box'],default='op',help='runtime selector; both certificates are always reported on the same worlds')
    p.add_argument('--out',default='research/high_value_extensions/master/full_utility.json'); a=p.parse_args(argv)
    payload=run(a.seed,a.instances,a.m_grid,a.tolerances,a.families,a.solver_cell_limit,a.exact_work_limit,a.active_gamma)
    write_artifact_with_provenance(Path(a.out),payload,protocol={'protocol_version':PROTOCOL_VERSION,'m_grid':a.m_grid,'families':a.families,'tolerances':a.tolerances,'instances':a.instances,'active_gamma':a.active_gamma},seed=a.seed,evidence_class=payload['evidence_class'],chain='MASTER')
    print(json.dumps({k:v for k,v in payload.items() if k!='rows'}|{'row_count':len(payload['rows'])},indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
