"""D6 contrast-rank falsification utilities.

This module follows the current post-counterexample D6 semantics:

* full finite Cartesian action space;
* normalized product reference ``q``;
* product responses ``Q_i^q``;
* Top-C selected set from response spans;
* product-compression loss ``osc(F-sum_{i in S}Q_i(a_i))/2``;
* mixed-difference modulus ``delta_square``;
* centered local interaction profiles from the Lean contrast-rank branch.

The generated B1/B-product/B2 classes are rank-one at every coordinate by
construction.  B3 is an explicitly heuristic direct optimization over the
world table with a numerical rank-one penalty; survival is never reported as
proof.
"""
from __future__ import annotations

from dataclasses import dataclass
import itertools
import math
from typing import Mapping, Sequence

import numpy as np


Array = np.ndarray


def _validate_world(F: Array) -> tuple[int,int]:
    F=np.asarray(F,dtype=np.float64)
    if F.ndim < 2:
        raise ValueError("D6 balanced search requires at least two coordinates")
    if len(set(F.shape)) != 1:
        raise ValueError("current contrast-rank lab uses a common action alphabet")
    return int(F.ndim), int(F.shape[0])


def validate_reference(q: Sequence[Sequence[float]], m: int, K: int) -> Array:
    q=np.asarray(q,dtype=np.float64)
    if q.shape != (int(m),int(K)):
        raise ValueError(f"q must have shape {(m,K)}")
    if np.any(q < -1e-12):
        raise ValueError("reference weights must be non-negative")
    sums=np.sum(q,axis=1)
    if not np.allclose(sums,1.0,atol=1e-12,rtol=0.0):
        raise ValueError("every product-reference row must sum to one")
    return q


def product_response(F: Array, q: Sequence[Sequence[float]]) -> Array:
    F=np.asarray(F,dtype=np.float64); m,K=_validate_world(F); q=validate_reference(q,m,K)
    out=np.empty((m,K),dtype=np.float64)
    for i in range(m):
        for u in range(K):
            sl=[slice(None)]*m; sl[i]=u
            arr=np.asarray(F[tuple(sl)],dtype=np.float64)
            # Integrate the remaining axes in their original order.
            axes=[j for j in range(m) if j!=i]
            for axis_pos,j in reversed(list(enumerate(axes))):
                arr=np.tensordot(arr,q[j],axes=([axis_pos],[0]))
            out[i,u]=float(arr)
    return out


def response_spans(Q: Array) -> Array:
    Q=np.asarray(Q,dtype=np.float64)
    return np.max(Q,axis=1)-np.min(Q,axis=1)


def stable_topk(scores: Sequence[float], k: int) -> tuple[int,...]:
    scores=np.asarray(scores,dtype=np.float64)
    order=sorted(range(len(scores)),key=lambda i:(-float(scores[i]),int(i)))
    return tuple(sorted(order[:int(k)]))


def product_compression_loss(F: Array, Q: Array, selected: Sequence[int]) -> float:
    F=np.asarray(F,dtype=np.float64); m,K=_validate_world(F); Q=np.asarray(Q,dtype=np.float64)
    if Q.shape != (m,K): raise ValueError("Q shape mismatch")
    residual=F.copy()
    for j in map(int,selected):
        shape=[1]*m; shape[j]=K
        residual=residual-Q[j].reshape(shape)
    return 0.5*float(np.max(residual)-np.min(residual))


def delta_square(F: Array) -> float:
    """Exact finite D6 mixed-difference modulus.

    For fixed i,u,v, the mixed difference is the difference of the local
    contrast F(u,z_-i)-F(v,z_-i) at two complement contexts.  Hence its maximum
    absolute value is exactly the range of that contrast over contexts.
    """
    F=np.asarray(F,dtype=np.float64); m,K=_validate_world(F)
    best=0.0
    for i in range(m):
        M=np.moveaxis(F,i,0).reshape(K,-1)
        for u in range(K):
            for v in range(u+1,K):
                d=M[u]-M[v]
                best=max(best,float(np.max(d)-np.min(d)))
    return float(best)


def interaction_profile_matrices(F: Array, q: Sequence[Sequence[float]], anchor: int=0) -> tuple[Array,...]:
    F=np.asarray(F,dtype=np.float64); m,K=_validate_world(F); q=validate_reference(q,m,K)
    if not (0<=int(anchor)<K): raise ValueError("anchor outside alphabet")
    Q=product_response(F,q); mats=[]
    for i in range(m):
        M=np.moveaxis(F,i,0).reshape(K,-1)
        raw=M-M[int(anchor)][None,:]
        centered=raw-(Q[i]-Q[i,int(anchor)])[:,None]
        mats.append(np.asarray(centered,dtype=np.float64))
    return tuple(mats)


def rank_one_diagnostics(F: Array, q: Sequence[Sequence[float]], anchor: int=0, tol: float=1e-9) -> dict:
    mats=interaction_profile_matrices(F,q,anchor=anchor)
    rows=[]; worst_abs=0.0; worst_rel=0.0
    for i,M in enumerate(mats):
        s=np.linalg.svd(M,compute_uv=False)
        tail=float(np.linalg.norm(s[1:])) if s.size>1 else 0.0
        lead=float(s[0]) if s.size else 0.0
        rel=tail/max(lead,1e-15)
        worst_abs=max(worst_abs,tail); worst_rel=max(worst_rel,rel)
        rows.append({'coordinate':i,'singular_values':s.tolist(),'tail_l2':tail,'relative_tail':rel})
    return {
        'anchor':int(anchor),'by_coordinate':rows,
        'max_rank_one_tail_l2':float(worst_abs),'max_rank_one_relative_tail':float(worst_rel),
        'all_coordinates_rank_one':bool(worst_abs<=float(tol)),
        'tolerance':float(tol),
    }


def decision_diagnostics(F: Array, q: Sequence[Sequence[float]], *, rank_tol: float=1e-9) -> dict:
    F=np.asarray(F,dtype=np.float64); m,K=_validate_world(F)
    if m%2: raise ValueError("current hard D6 contrast-rank lab targets even balanced m")
    q=validate_reference(q,m,K); Q=product_response(F,q); C=response_spans(Q); k=m//2
    selected=stable_topk(C,k); complement=tuple(i for i in range(m) if i not in set(selected))
    selected_loss=product_compression_loss(F,Q,selected)
    candidates=[]
    for S in itertools.combinations(range(m),k):
        candidates.append((product_compression_loss(F,Q,S),tuple(S)))
    optimum,opt_sets=min(candidates,key=lambda x:(x[0],x[1]))
    all_opt=[S for loss,S in candidates if abs(loss-optimum)<=1e-10]
    regret=float(selected_loss-optimum)
    comp_loss=product_compression_loss(F,Q,complement)
    delta=delta_square(F)
    ratio=(2.0*regret/delta) if delta>1e-12 else (0.0 if regret<=1e-12 else float('inf'))
    comp_ratio=(2.0*(selected_loss-comp_loss)/delta) if delta>1e-12 else None
    rejected=[j for j in range(m) if j not in selected]
    margin=float(min(C[j] for j in selected)-max(C[j] for j in rejected)) if rejected else float('inf')
    rank=rank_one_diagnostics(F,q,tol=rank_tol)
    return {
        'm':m,'actions':K,'k':k,'delta_square':float(delta),
        'Q':Q.tolist(),'scores':C.tolist(),'selected':list(selected),'complement':list(complement),
        'selected_loss':float(selected_loss),'optimal_loss':float(optimum),'optimal_sets':[list(x) for x in all_opt],
        'complement_loss':float(comp_loss),'complement_is_optimal':bool(any(tuple(complement)==tuple(x) for x in all_opt)),
        'decision_regret':regret,'two_regret_over_delta':float(ratio),
        'complement_two_gap_over_delta':None if comp_ratio is None else float(comp_ratio),
        'target_m_minus_1':int(m-1),'violates_m_minus_1':bool(ratio>float(m-1)+1e-9),
        'strict_topc_margin':margin,'strict_topc':bool(margin>1e-10),
        'rank_one':rank,
    }


def _rational_choice(rng: np.random.Generator, values: Sequence[float]) -> float:
    return float(values[int(rng.integers(0,len(values)))])


def random_reference(rng: np.random.Generator, m: int, K: int, mode: str) -> Array:
    mode=str(mode)
    if mode=='point0':
        q=np.zeros((m,K),float); q[:,0]=1.0; return q
    if mode=='uniform': return np.full((m,K),1.0/K,float)
    if mode=='rational':
        q=[]
        for _ in range(m):
            raw=rng.integers(1,6,size=K).astype(float); q.append(raw/raw.sum())
        return np.asarray(q,float)
    raise ValueError(f'unknown reference mode {mode}')


def _phi_table(rng: np.random.Generator,m: int,K: int) -> Array:
    if K<3: raise ValueError("rank-one multivalued search requires K>=3")
    phi=np.zeros((m,K),float); phi[:,1]=1.0
    grid=(-2.0,-1.5,-1.0,-0.5,0.5,1.5,2.0,2.5,3.0)
    for i in range(m):
        for u in range(2,K):
            val=_rational_choice(rng,grid)
            # guarantee all nominal levels are distinct from anchor and action 1
            while abs(val)<1e-12 or abs(val-1.0)<1e-12 or any(abs(val-phi[i,v])<1e-12 for v in range(2,u)):
                val=_rational_choice(rng,grid)
            phi[i,u]=val
    return phi


def _additive_table(rng: np.random.Generator,m: int,K: int,scale: float=1.5) -> Array:
    grid=np.asarray([-2,-1.5,-1,-.5,0,.5,1,1.5,2],float)*float(scale)
    g=np.empty((m,K),float)
    for i in range(m):
        for u in range(K): g[i,u]=float(grid[int(rng.integers(0,len(grid)))])
        g[i]-=g[i,0]
    return g


def _evaluate_polynomial(phi: Array, coeffs: Mapping[int,float]) -> Array:
    m,K=phi.shape; F=np.zeros((K,)*m,dtype=np.float64)
    for action in np.ndindex(*((K,)*m)):
        total=0.0
        for mask,w in coeffs.items():
            prod=1.0
            for i in range(m):
                if int(mask)&(1<<i): prod*=float(phi[i,action[i]])
            total+=float(w)*prod
        F[action]=total
    return F


def _add_additive(F: Array,g: Array) -> Array:
    out=np.asarray(F,float).copy(); m,K=_validate_world(out)
    for i in range(m):
        shape=[1]*m; shape[i]=K; out+=g[i].reshape(shape)
    return out


def _normalize_interaction(F: Array) -> Array:
    d=delta_square(F)
    if d<=1e-12: return np.asarray(F,float)
    return np.asarray(F,float)/d


def generated_rank_one_world(rng: np.random.Generator, *, family: str, m: int=4, K: int=3,
                             reference_mode: str='uniform') -> tuple[Array,Array,dict]:
    """Generate B1/B-product/B2 rank-one worlds with rational-grid parameters."""
    family=str(family); m=int(m); K=int(K)
    phi=_phi_table(rng,m,K); g=_additive_table(rng,m,K)
    coeffs={}
    weight_grid=(-2.0,-1.5,-1.0,-0.5,0.5,1.0,1.5,2.0)
    if family=='B1_pairwise':
        for i,j in itertools.combinations(range(m),2):
            coeffs[(1<<i)|(1<<j)]=_rational_choice(rng,weight_grid)
    elif family=='Bproduct':
        coeffs[(1<<m)-1]=_rational_choice(rng,weight_grid)
    elif family=='B2_multiaffine':
        for mask in range(1,1<<m):
            if int(mask).bit_count()>=2:
                # Sparse/dense mixture improves morphology coverage.
                coeffs[mask]=0.0 if rng.random()<.25 else _rational_choice(rng,weight_grid)
        if not any(abs(x)>1e-12 for x in coeffs.values()): coeffs[(1<<m)-1]=1.0
    else:
        raise ValueError(f'unknown generated family {family}')
    interaction=_normalize_interaction(_evaluate_polynomial(phi,coeffs))
    F=_add_additive(interaction,g)
    q=random_reference(rng,m,K,reference_mode)
    spec={'family':family,'phi':phi.tolist(),'g':g.tolist(),
          'coefficients':{str(int(k)):float(v) for k,v in coeffs.items()},
          'reference_mode':reference_mode,'q':q.tolist()}
    return F,q,spec


def search_generated_rank_one(*, family: str, instances: int, seed: int, m_values=(4,), K: int=3,
                              reference_modes=('point0','uniform','rational'), rank_tol=1e-8) -> dict:
    rng=np.random.default_rng(int(seed)); best=None; killed=None; rank_failures=0
    by_m={}
    for idx in range(int(instances)):
        m=int(m_values[idx%len(m_values)]); mode=str(reference_modes[(idx//len(m_values))%len(reference_modes)])
        F,q,spec=generated_rank_one_world(rng,family=family,m=m,K=int(K),reference_mode=mode)
        diag=decision_diagnostics(F,q,rank_tol=rank_tol)
        if not diag['rank_one']['all_coordinates_rank_one']:
            rank_failures+=1
        row={'index':idx,'spec':spec,'diagnostics':diag}
        if best is None or diag['two_regret_over_delta']>best['diagnostics']['two_regret_over_delta']:
            best=row
        mm=by_m.setdefault(str(m),{'n':0,'best_ratio':-float('inf'),'kill_count':0,'strict_count':0})
        mm['n']+=1; mm['best_ratio']=max(mm['best_ratio'],float(diag['two_regret_over_delta']))
        mm['kill_count']+=int(diag['violates_m_minus_1']); mm['strict_count']+=int(diag['strict_topc'])
        if diag['violates_m_minus_1'] and diag['rank_one']['all_coordinates_rank_one'] and killed is None:
            killed=row
    for mm in by_m.values():
        mm['strict_fraction']=float(mm['strict_count']/max(1,mm['n']))
    return {
        'family':family,'instances':int(instances),'seed':int(seed),'m_values':list(map(int,m_values)),'actions':int(K),
        'reference_modes':list(reference_modes),'rank_one_construction_failures':int(rank_failures),
        'candidate_killed':bool(killed is not None),'first_counterexample':killed,'best_witness':best,'by_m':by_m,
        'scope':'rank-one by scalar-latent construction; survival is falsification evidence, not proof',
    }


def direct_rank_one_penalty_search(*, seed: int=0, restarts: int=2, steps: int=100,
                                  m: int=4, K: int=3, lr: float=.0002,
                                  rank_tol: float=1e-5, penalty: float=100_000_000.0) -> dict:
    """B3 heuristic direct table search with a numerical rank-one penalty.

    It starts from exact B2 rank-one worlds but optimizes the full K^m table.
    A putative counterexample is accepted only after an independent NumPy SVD
    post-check satisfies ``rank_tol``.  No survival result from this heuristic
    is treated as proof of the universal rank-one conjecture.
    """
    try:
        import torch
    except Exception as exc:  # pragma: no cover - fail-closed portability path
        return {'available':False,'reason':f'{type(exc).__name__}: {exc}','candidate_killed':False}
    torch.manual_seed(int(seed)); rng=np.random.default_rng(int(seed)); m=int(m); K=int(K)
    if m%2: raise ValueError('B3 current implementation requires even m')
    actions=np.asarray(list(np.ndindex(*((K,)*m))),dtype=np.int64); n=len(actions); k=m//2
    subset_list=list(itertools.combinations(range(m),k))

    best=None; accepted=0
    for restart in range(int(restarts)):
        init,q,_=generated_rank_one_world(rng,family='B2_multiaffine',m=m,K=K,reference_mode='uniform')
        F=torch.tensor(init.reshape(-1),dtype=torch.float64,requires_grad=True)
        q_t=torch.tensor(q,dtype=torch.float64)
        action_t=torch.tensor(actions,dtype=torch.long)
        # Linear product-response map.
        W=[]
        for i in range(m):
            for u in range(K):
                weights=[]
                for a in actions:
                    if int(a[i])!=u: weights.append(0.0); continue
                    p=1.0
                    for j in range(m):
                        if j!=i: p*=float(q[j,int(a[j])])
                    weights.append(p)
                W.append(weights)
        W=torch.tensor(np.asarray(W),dtype=torch.float64)
        opt=torch.optim.Adam([F],lr=float(lr))
        for _ in range(int(steps)):
            opt.zero_grad()
            Q=(W@F).reshape(m,K)
            scores=Q.max(1).values-Q.min(1).values
            selected=torch.topk(scores,k=k,largest=True,sorted=False).indices
            def loss_for(ids):
                residual=F
                for j in ids:
                    residual=residual-Q[j,action_t[:,j]]
                return .5*(residual.max()-residual.min())
            Lsel=loss_for(selected)
            losses=torch.stack([loss_for(list(S)) for S in subset_list])
            regret=Lsel-losses.min()
            Ft=F.reshape(*((K,)*m))
            deltas=[]; rank_pen=torch.tensor(0.0,dtype=torch.float64)
            for i in range(m):
                M=torch.movedim(Ft,i,0).reshape(K,-1)
                for u in range(K):
                    for v in range(u+1,K):
                        d=M[u]-M[v]; deltas.append(d.max()-d.min())
                raw=M-M[0:1]
                prof=raw-(Q[i]-Q[i,0]).reshape(K,1)
                s=torch.linalg.svdvals(prof)
                if len(s)>1: rank_pen=rank_pen+torch.sum(s[1:]**2)
            delta=torch.stack(deltas).max().clamp_min(1e-8)
            ratio=2.0*regret/delta
            scale_pen=1e-5*torch.mean((F/delta)**2)
            objective=-ratio+float(penalty)*rank_pen/(delta**2)+scale_pen
            objective.backward(); opt.step()
        arr=F.detach().cpu().numpy().reshape((K,)*m)
        diag=decision_diagnostics(arr,q,rank_tol=float(rank_tol))
        valid=bool(diag['rank_one']['max_rank_one_tail_l2']<=float(rank_tol)*max(1.0,delta_square(arr)))
        accepted+=int(valid)
        row={'restart':restart,'valid_rank_one_postcheck':valid,'diagnostics':diag,
             'F':arr.tolist() if diag['violates_m_minus_1'] and valid else None,'q':q.tolist()}
        if best is None or (valid,float(diag['two_regret_over_delta']))>(best['valid_rank_one_postcheck'],float(best['diagnostics']['two_regret_over_delta'])):
            best=row
    killed=bool(best and best['valid_rank_one_postcheck'] and best['diagnostics']['violates_m_minus_1'])
    return {'available':True,'seed':int(seed),'restarts':int(restarts),'steps':int(steps),'m':m,'actions':K,
            'rank_tol':float(rank_tol),'accepted_rank_one_postchecks':int(accepted),'candidate_killed':killed,
            'best_witness':best,
            'scope':'heuristic direct full-table optimization with numerical rank-one postcheck; survival is not proof'}


def adversarial_multiaffine_rank_one_search(*, seed: int=0, restarts: int=4, steps: int=250,
                                            m: int=4, K: int=3, lr: float=.03) -> dict:
    """Continuous adversarial search inside the exact B2 rank-one class.

    The parameterization itself guarantees all-coordinate interaction rank one:
    arbitrary additive rows plus a full multiaffine scalar-latent interaction
    core.  Unlike the B3 penalty search, no numerical rank constraint is used.
    """
    try:
        import torch
    except Exception as exc:  # pragma: no cover
        return {'available':False,'reason':f'{type(exc).__name__}: {exc}','candidate_killed':False}
    torch.manual_seed(int(seed)); m=int(m); K=int(K)
    if m%2: raise ValueError('balanced D6 adversarial search requires even m')
    actions_np=np.asarray(list(np.ndindex(*((K,)*m))),dtype=np.int64)
    actions=torch.tensor(actions_np,dtype=torch.long)
    masks=[mask for mask in range(1,1<<m) if mask.bit_count()>=2]
    subsets=list(itertools.combinations(range(m),m//2))
    best=None
    for restart in range(int(restarts)):
        t=torch.nn.Parameter(torch.randn(m,max(0,K-2),dtype=torch.float64))
        core=torch.nn.Parameter(torch.randn(len(masks),dtype=torch.float64)*.4)
        g=torch.nn.Parameter(torch.randn(m,K,dtype=torch.float64)*.5)
        q_logits=torch.nn.Parameter(torch.zeros(m,K,dtype=torch.float64)+.05*torch.randn(m,K,dtype=torch.float64))
        opt=torch.optim.Adam([t,core,g,q_logits],lr=float(lr))
        for step in range(int(steps)):
            opt.zero_grad()
            phi=torch.zeros(m,K,dtype=torch.float64)
            phi[:,1]=1.0
            if K>2: phi[:,2:]=t
            F=torch.zeros(len(actions_np),dtype=torch.float64)
            # Additive gauge/cell steering.
            for i in range(m): F=F+g[i,actions[:,i]]
            # Full multiaffine interaction core.
            for c,mask in zip(core,masks):
                term=torch.ones(len(actions_np),dtype=torch.float64)
                for i in range(m):
                    if mask&(1<<i): term=term*phi[i,actions[:,i]]
                F=F+c*term
            q=torch.softmax(q_logits,dim=1)
            Q=[]
            for i in range(m):
                qi=[]
                for u in range(K):
                    w=torch.ones(len(actions_np),dtype=torch.float64)
                    for j in range(m):
                        if j!=i: w=w*q[j,actions[:,j]]
                    w=w*(actions[:,i]==u).to(torch.float64)
                    qi.append(torch.sum(w*F))
                Q.append(torch.stack(qi))
            Q=torch.stack(Q)
            scores=Q.max(1).values-Q.min(1).values
            selected=torch.topk(scores,k=m//2,largest=True,sorted=False).indices
            def lset(ids):
                res=F
                for j in ids: res=res-Q[j,actions[:,j]]
                return .5*(res.max()-res.min())
            Ls=lset(selected); losses=torch.stack([lset(S) for S in subsets]); regret=Ls-losses.min()
            Ft=F.reshape(*((K,)*m)); dlist=[]
            for i in range(m):
                M=torch.movedim(Ft,i,0).reshape(K,-1)
                for u in range(K):
                    for v in range(u+1,K):
                        d=M[u]-M[v]; dlist.append(d.max()-d.min())
            delta=torch.stack(dlist).max().clamp_min(1e-8)
            ratio=2.0*regret/delta
            # Scale/gauge regularization prevents runaway additive values while
            # leaving the scale-free decision ratio as the primary objective.
            reg=1e-4*(torch.mean(g**2)+torch.mean(core**2))+1e-5*torch.mean(t**2)
            loss=-ratio+reg
            loss.backward(); opt.step()
            if step%20==0 or step==int(steps)-1:
                arr=F.detach().cpu().numpy().reshape((K,)*m); qn=q.detach().cpu().numpy()
                diag=decision_diagnostics(arr,qn,rank_tol=1e-7)
                row={'restart':restart,'step':step,'diagnostics':diag,
                     'phi':phi.detach().cpu().numpy().tolist(),'g':g.detach().cpu().numpy().tolist(),
                     'core':{str(mask):float(core[idx].detach().cpu()) for idx,mask in enumerate(masks)},
                     'q':qn.tolist()}
                if best is None or float(diag['two_regret_over_delta'])>float(best['diagnostics']['two_regret_over_delta']): best=row
    killed=bool(best and best['diagnostics']['violates_m_minus_1'] and best['diagnostics']['rank_one']['all_coordinates_rank_one'])
    return {'available':True,'seed':int(seed),'restarts':int(restarts),'steps':int(steps),'m':m,'actions':K,
            'candidate_killed':killed,'best_witness':best,
            'scope':'continuous adversarial optimization inside exact scalar-latent full-multiaffine rank-one parameterization; survival is not proof'}
