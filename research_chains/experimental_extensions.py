"""High-value experimental diagnostics for the CIG-AMF extension programme.

This module deliberately separates deterministic/falsification diagnostics from
claims that require confirmatory or external evidence.  It is development-only
infrastructure and does not change the frozen V7 learner, estimands, or gates.
"""
from __future__ import annotations

import itertools
import math
import time
from dataclasses import dataclass
from typing import Iterable, Mapping, Sequence

import numpy as np

from .certificates import exact_optimum, global_extremizability_defect, topk_indices, zeta_def
from .finite_world import FiniteResponseWorld
from .pairwise import operational_gamma, pairwise_master_bound
from .reference import ConditionalReferenceKernel, product_reference_surrogate
from .support import SupportModel


def _normalise_probabilities(values: Sequence[float]) -> np.ndarray:
    arr = np.asarray(values, dtype=np.float64)
    if arr.ndim != 1 or arr.size == 0 or np.any(arr < 0.0) or not np.all(np.isfinite(arr)):
        raise ValueError("probabilities must be a finite non-negative vector")
    total = float(arr.sum())
    if total <= 0.0:
        raise ValueError("probabilities must have positive mass")
    return arr / total


def total_variation(p: Sequence[float], q: Sequence[float]) -> float:
    p = _normalise_probabilities(p); q = _normalise_probabilities(q)
    if p.shape != q.shape:
        raise ValueError("probability vectors must align")
    return 0.5 * float(np.abs(p - q).sum())


def kernel_row_vector(kernel: ConditionalReferenceKernel, source_action: int) -> tuple[tuple[tuple[int, ...], ...], np.ndarray]:
    support = sorted({
        tuple(joint[j] for j in range(len(kernel.action_sizes)) if j != kernel.source)
        for row in kernel.by_source_action.values() for joint in row
    })
    lookup = {}
    for joint, prob in kernel.by_source_action[int(source_action)].items():
        key = tuple(joint[j] for j in range(len(kernel.action_sizes)) if j != kernel.source)
        lookup[key] = lookup.get(key, 0.0) + float(prob)
    return tuple(support), np.asarray([lookup.get(x, 0.0) for x in support], dtype=np.float64)


def kernel_sup_tv(left: ConditionalReferenceKernel, right: ConditionalReferenceKernel) -> float:
    if left.source != right.source or left.action_sizes != right.action_sizes:
        raise ValueError("kernels must share source and action alphabet")
    complement = [j for j in range(len(left.action_sizes)) if j != left.source]
    keys = list(itertools.product(*(range(left.action_sizes[j]) for j in complement)))
    worst = 0.0
    for a in range(left.action_sizes[left.source]):
        def row(kernel):
            lookup = {}
            for joint, prob in kernel.by_source_action[a].items():
                key = tuple(joint[j] for j in complement)
                lookup[key] = lookup.get(key, 0.0) + float(prob)
            return np.asarray([lookup.get(key, 0.0) for key in keys], dtype=np.float64)
        worst = max(worst, total_variation(row(left), row(right)))
    return float(worst)


def mix_kernel(kernel: ConditionalReferenceKernel, rng: np.random.Generator, mixing: float) -> ConditionalReferenceKernel:
    """Mix every conditional row with a random row; TV perturbation <= mixing."""
    mixing = float(mixing)
    if not 0.0 <= mixing <= 1.0:
        raise ValueError("mixing must lie in [0,1]")
    full = list(np.ndindex(*kernel.action_sizes)); rows = {}
    for a in range(kernel.action_sizes[kernel.source]):
        compatible = [x for x in full if x[kernel.source] == a]
        lookup = {x: float(kernel.by_source_action[a].get(x, 0.0)) for x in compatible}
        random_row = rng.dirichlet(np.ones(len(compatible)))
        rows[a] = {
            x: (1.0 - mixing) * lookup[x] + mixing * float(random_row[i])
            for i, x in enumerate(compatible)
        }
    return ConditionalReferenceKernel(kernel.source, kernel.action_sizes, rows, key=f"mix_{mixing:g}")


def reference_uncertainty_diagnostics(world: FiniteResponseWorld, truth: ConditionalReferenceKernel, estimate: ConditionalReferenceKernel) -> dict:
    if truth.source != estimate.source:
        raise ValueError("reference source mismatch")
    eps = kernel_sup_tv(truth, estimate)
    m_true = truth.complement_expectation(world)
    m_hat = estimate.complement_expectation(world)
    # Exact osc(H) for H(a_-j)=sum_{l!=j} f_l(a_l), matching RU1/RU2.
    complement=[j for j in range(world.support.n_relations) if j!=truth.source]
    h_values=[]
    for vals in itertools.product(*(range(world.support.action_sizes[j]) for j in complement)):
        h_values.append(sum(float(world.primitives[j][a]) for j,a in zip(complement,vals)))
    h_span=float(np.ptp(np.asarray(h_values,dtype=np.float64))) if h_values else 0.0
    pointwise = float(np.max(np.abs(m_true - m_hat)))
    chi_true = truth.isolation_deviation(world); chi_hat = estimate.isolation_deviation(world)
    measured_true = float(np.ptp(truth.response_vector(world, true_response=False)))
    measured_hat = float(np.ptp(estimate.response_vector(world, true_response=False)))
    primitive = world.component_span(truth.source)
    ref_radius = chi_hat + 2.0 * h_span * eps
    return {
        "epsilon_kernel_tv": eps,
        "complement_span": float(h_span),
        "pointwise_neutral_error": pointwise,
        "pointwise_tv_rhs": float(h_span * eps),
        "pointwise_violation": pointwise - float(h_span * eps),
        "chi_true": float(chi_true),
        "chi_hat": float(chi_hat),
        "chi_abs_error": abs(float(chi_true - chi_hat)),
        "chi_tv_rhs": float(2.0 * h_span * eps),
        "chi_violation": abs(float(chi_true - chi_hat)) - float(2.0 * h_span * eps),
        "primitive_span": float(primitive),
        "measured_span_true_kernel": measured_true,
        "measured_span_estimated_kernel": measured_hat,
        "reference_error_radius": float(ref_radius),
        "score_interval_violation": abs(measured_hat - primitive) - float(ref_radius),
    }


def empirical_kernel_from_counts(
    *, source: int, action_sizes: Sequence[int], counts: Mapping[int, Mapping[tuple[int, ...], int]], smoothing: float = 0.5, key: str = "empirical",
) -> ConditionalReferenceKernel:
    sizes = tuple(int(x) for x in action_sizes); full = list(np.ndindex(*sizes)); rows = {}
    for a in range(sizes[source]):
        compatible = [x for x in full if x[source] == a]
        vals = np.asarray([float(counts.get(a, {}).get(x, 0)) + float(smoothing) for x in compatible])
        vals /= vals.sum()
        rows[a] = {x: float(vals[i]) for i, x in enumerate(compatible)}
    return ConditionalReferenceKernel(source, sizes, rows, key=key)


def sample_kernel_counts(
    kernel: ConditionalReferenceKernel, total_budget: int, rng: np.random.Generator, mode: str = "passive", passive_probs: Sequence[float] | None = None,
) -> tuple[dict[int, dict[tuple[int, ...], int]], np.ndarray]:
    """Simulate reference acquisition with explicit acquisition semantics.

    ``targeted`` is intentionally the historical balanced least-observed
    scheduler.  ``uncertainty_targeted`` is a genuinely adaptive policy: after
    a small pilot it repeatedly samples the source-action row with the largest
    Dirichlet-posterior multinomial uncertainty proxy.  The latter uses only
    observations collected so far; the true kernel is used solely to generate
    the next synthetic observation.
    """
    total_budget = int(total_budget)
    if total_budget <= 0:
        raise ValueError("budget must be positive")
    n_actions = kernel.action_sizes[kernel.source]
    if passive_probs is None:
        passive_probs = np.geomspace(1.0, 0.1, n_actions)
    passive_probs = _normalise_probabilities(passive_probs)

    complement = [j for j in range(len(kernel.action_sizes)) if j != kernel.source]
    keys = list(itertools.product(*(range(kernel.action_sizes[j]) for j in complement)))
    truth_probs = {}
    for a in range(n_actions):
        lookup = {}
        for joint, prob in kernel.by_source_action[a].items():
            key = tuple(joint[j] for j in complement)
            lookup[key] = lookup.get(key, 0.0) + float(prob)
        truth_probs[a] = _normalise_probabilities([lookup.get(key, 0.0) for key in keys])

    counts = {a: {} for a in range(n_actions)}
    source_counts = np.zeros(n_actions, dtype=int)

    def draw_row(a: int, n: int) -> None:
        if n <= 0:
            return
        draws = rng.multinomial(int(n), truth_probs[int(a)])
        source_counts[int(a)] += int(n)
        for key, count in zip(keys, draws):
            if int(count) <= 0:
                continue
            joint = [0] * len(kernel.action_sizes)
            joint[kernel.source] = int(a)
            for j, value in zip(complement, key):
                joint[j] = value
            joint = tuple(joint)
            counts[int(a)][joint] = counts[int(a)].get(joint, 0) + int(count)

    if mode == "passive":
        alloc = rng.multinomial(total_budget, passive_probs).astype(int)
        for a, n in enumerate(alloc):
            draw_row(a, int(n))
    elif mode == "randomized":
        alloc = rng.multinomial(total_budget, np.full(n_actions, 1.0 / n_actions)).astype(int)
        for a, n in enumerate(alloc):
            draw_row(a, int(n))
    elif mode == "targeted":
        # Historical stratified/balanced scheduler retained for backwards
        # compatibility.  It is NOT uncertainty-adaptive.
        base, rem = divmod(total_budget, n_actions)
        alloc = np.full(n_actions, base, dtype=int)
        if rem:
            alloc[rng.choice(n_actions, size=rem, replace=False)] += 1
        for a, n in enumerate(alloc):
            draw_row(a, int(n))
    elif mode == "uncertainty_targeted":
        # Give every source action coverage when the budget permits, then adapt.
        pilot = min(2, total_budget // n_actions)
        if pilot > 0:
            for a in range(n_actions):
                draw_row(a, pilot)
        remaining = total_budget - int(source_counts.sum())
        smoothing = 0.5
        while remaining > 0:
            scores = []
            for a in range(n_actions):
                observed = np.asarray([counts[a].get(tuple([a if j == kernel.source else key[complement.index(j)] for j in range(len(kernel.action_sizes))]), 0) for key in keys], dtype=np.float64)
                alpha = observed + smoothing
                alpha0 = float(alpha.sum())
                p = alpha / alpha0
                # Posterior expected multinomial variance / sample-size proxy.
                # Larger for poorly sampled/high-entropy rows.
                score = math.sqrt(max(0.0, float(np.sum(p * (1.0 - p))) / (alpha0 + 1.0)))
                scores.append(score)
            max_score = max(scores)
            candidates = [a for a, score in enumerate(scores) if abs(score - max_score) <= 1e-15]
            a = int(rng.choice(candidates))
            draw_row(a, 1)
            remaining -= 1
    else:
        raise ValueError(f"unknown acquisition mode {mode}")

    if int(np.sum(source_counts)) != total_budget:
        raise AssertionError("source allocation did not conserve budget")
    return counts, source_counts




def ru2_factor_two_sharpness_diagnostics() -> dict:
    # Exact Fin2 x Fin2 Lean witness: uniform rows versus separated rows, H=(0,1).
    ku=np.asarray([[0.5,0.5],[0.5,0.5]],dtype=np.float64)
    ks=np.asarray([[1.0,0.0],[0.0,1.0]],dtype=np.float64)
    H=np.asarray([0.0,1.0],dtype=np.float64)
    tv=np.asarray([0.5*np.abs(ku[a]-ks[a]).sum() for a in range(2)])
    eu=ku@H; es=ks@H; lhs=abs(float(np.ptp(eu)-np.ptp(es))); rhs=2.0*float(np.ptp(H))*float(np.max(tv))
    return {'rowwise_tv':tv.tolist(),'epsilon':float(np.max(tv)),'uniform_expectations':eu.tolist(),'separated_expectations':es.tolist(),'lhs_chi_difference':lhs,'rhs_two_oscH_epsilon':rhs,'equality_residual':lhs-rhs,'sharpness_reproduced':bool(abs(lhs-rhs)<=1e-12 and abs(lhs-1.0)<=1e-12)}

def box_gamma_diagnostics(estimated_scores: Sequence[float], errors: Sequence[float], k: int, selected: Sequence[int] | None = None) -> dict:
    """Independent-interval-box tightening aligned with LeanPairwiseBoxRegretV1.

    For small m we also enumerate every interval-box vertex and verify that the
    fixed-selected modular retained-score regret never exceeds boxGamma.
    """
    chat=np.asarray(estimated_scores,dtype=np.float64); e=np.asarray(errors,dtype=np.float64)
    if chat.ndim!=1 or e.shape!=chat.shape or np.any(e<0) or not np.all(np.isfinite(chat)) or not np.all(np.isfinite(e)):
        raise ValueError("invalid score interval")
    m=chat.size; k=int(k); selected=topk_indices(chat,k) if selected is None else tuple(int(j) for j in selected)
    if len(set(selected))!=k: raise ValueError("selected must contain k unique indices")
    lower=chat-e; upper=chat+e; sel=set(selected)
    adv=np.asarray([lower[j] if j in sel else upper[j] for j in range(m)],dtype=np.float64)
    adv_top=topk_indices(adv,k)
    box=0.5*(float(np.sum(adv[list(adv_top)]))-float(np.sum(lower[list(selected)])))
    op=operational_gamma(chat,e,k,selected)
    worst_vertex=-float('inf'); worst_vertex_scores=None
    if m<=14:
        for bits in itertools.product((0,1),repeat=m):
            c=np.where(np.asarray(bits,dtype=bool),upper,lower)
            true_top=topk_indices(c,k)
            regret=0.5*(float(np.sum(c[list(true_top)]))-float(np.sum(c[list(selected)])))
            if regret>worst_vertex:
                worst_vertex=regret; worst_vertex_scores=c.tolist()
    else:
        worst_vertex=float('nan')
    return {
      'box_gamma':float(max(0.0,box)),'operational_gamma':float(op),
      'tightening':float(op-box),'strict_tightening':bool(box<op-1e-12),
      'box_le_operational_violation':float(box-op),
      'vertex_worst_score_regret':float(worst_vertex),
      'vertex_exactness_gap':float(box-worst_vertex) if np.isfinite(worst_vertex) else None,
      'vertex_bound_violation':float(worst_vertex-box) if np.isfinite(worst_vertex) else None,
      'worst_vertex_scores':worst_vertex_scores,'selected':list(selected),'adversary_top':list(adv_top),
    }


def box_gamma_lean_witness_diagnostics() -> dict:
    # Lean witness: Chat=(0,0,0), e=(2,0,0), selected={0}, k=1.
    out=box_gamma_diagnostics([0.,0.,0.],[2.,0.,0.],1,[0])
    out['lean_expected_box_gamma']=1.0; out['lean_expected_operational_gamma']=2.0
    out['lean_witness_reproduced']=bool(abs(out['box_gamma']-1.0)<=1e-12 and abs(out['operational_gamma']-2.0)<=1e-12)
    return out


def probability_lift_diagnostics(*, repetitions: int = 5000, seed: int = 0, m: int = 6, k: int = 2, alpha: float = 0.05, n: int = 64) -> dict:
    """Known-Gaussian one-shot audit of good-event -> false-certificate inclusion.

    This is not a new concentration theorem. It checks that the operational
    interval certificate never fails on the simultaneous score-coverage event
    and reports empirical bad-event/false-certificate rates.
    """
    from scipy.stats import norm
    rng=np.random.default_rng(seed); m=int(m); k=int(k); reps=int(repetitions); n=int(n)
    if not (0<alpha<1) or not (0<k<=m) or reps<=0 or n<=0: raise ValueError('invalid probability-lift configuration')
    true=np.linspace(0.,0.8,m)+0.03*np.sin(np.arange(m));
    if m>=3:
        true[-2]=2.0; true[-1]=3.0
    sigma=np.linspace(.7,1.3,m)
    z=float(norm.ppf(1-float(alpha)/(2*m))); e=z*sigma/np.sqrt(n)
    true_top=set(topk_indices(true,k)); good=bad=false_cert=false_on_good=certified=0
    for _ in range(reps):
        est=true+rng.normal(scale=sigma/np.sqrt(n)); covered=bool(np.all(np.abs(est-true)<=e+1e-12))
        cert=bool(np.min((est-e)[list(topk_indices(est,k))]) > np.max((est+e)[[j for j in range(m) if j not in set(topk_indices(est,k))]]) if k<m else True)
        wrong=set(topk_indices(est,k))!=true_top
        good+=int(covered); bad+=int(not covered); certified+=int(cert)
        false_cert+=int(cert and wrong); false_on_good+=int(cert and wrong and covered)
    return {'repetitions':reps,'seed':int(seed),'alpha':float(alpha),'m':m,'k':k,'n':n,'z':z,
      'good_event_rate':good/reps,'bad_event_rate':bad/reps,'certified_rate':certified/reps,
      'false_certificate_rate':false_cert/reps,'false_certificate_on_good_event_count':false_on_good,
      'set_inclusion_violation_count':false_on_good,'empirical_false_le_bad':bool(false_cert<=bad),
      'nominal_bad_event_upper_target':float(alpha)}


def two_world_lower_bound_diagnostics(target1: float, target2: float, prediction: float) -> dict:
    sep=abs(float(target1)-float(target2)); e1=abs(float(prediction)-float(target1)); e2=abs(float(prediction)-float(target2)); worst=max(e1,e2); rhs=sep/2.0
    return {'target1':float(target1),'target2':float(target2),'prediction':float(prediction),'half_separation':rhs,'worst_error':worst,'violation':rhs-worst}

def quadratic_variance(covariance: Sequence[Sequence[float]], vector: Sequence[float]) -> float:
    sigma = np.asarray(covariance, dtype=np.float64); v = np.asarray(vector, dtype=np.float64)
    if sigma.shape != (v.size, v.size) or not np.all(np.isfinite(sigma)):
        raise ValueError("covariance/vector dimensions do not align")
    return float(v @ sigma @ v)


def capacity_contrast(n_actions: int, argmax: int, argmin: int) -> np.ndarray:
    v = np.zeros(int(n_actions), dtype=np.float64); v[int(argmax)] = 1.0; v[int(argmin)] = -1.0; return v


def random_psd(rng: np.random.Generator, n: int, jitter: float = 0.05) -> np.ndarray:
    A = rng.normal(size=(n, n)); sigma = A @ A.T / max(1, n); sigma += float(jitter) * np.eye(n); return sigma


def covariance_design_misranking_search(instances: int = 10000, seed: int = 0, n: int = 3) -> dict:
    rng = np.random.default_rng(seed); best = None
    for idx in range(int(instances)):
        s1 = random_psd(rng, n); s2 = random_psd(rng, n)
        v = rng.normal(size=n); v /= max(np.linalg.norm(v), 1e-12)
        diag1 = quadratic_variance(np.diag(np.diag(s1)), v); diag2 = quadratic_variance(np.diag(np.diag(s2)), v)
        full1 = quadratic_variance(s1, v); full2 = quadratic_variance(s2, v)
        if (diag1 < diag2 and full1 > full2) or (diag2 < diag1 and full2 > full1):
            best = {"index": idx, "vector": v.tolist(), "sigma_a": s1.tolist(), "sigma_b": s2.tolist(), "diag_a":diag1,"diag_b":diag2,"full_a":full1,"full_b":full2}; break
    return {"found": best is not None, "witness": best, "instances": int(instances), "seed": int(seed)}


def lean_covariance_reversal_witness_diagnostics() -> dict:
    """Reproduce the exact Fin-2 PSD witness formalized in the Lean extension."""
    sigma_a=np.asarray([[1.0,0.9],[0.9,1.0]],dtype=np.float64)
    sigma_b=np.asarray([[0.6,-0.5],[-0.5,0.6]],dtype=np.float64)
    v=np.asarray([1.0,-1.0],dtype=np.float64)
    diag_a=quadratic_variance(np.diag(np.diag(sigma_a)),v)
    diag_b=quadratic_variance(np.diag(np.diag(sigma_b)),v)
    full_a=quadratic_variance(sigma_a,v); full_b=quadratic_variance(sigma_b,v)
    eig_a=np.linalg.eigvalsh(sigma_a); eig_b=np.linalg.eigvalsh(sigma_b)
    return {
      "sigma_a":sigma_a.tolist(),"sigma_b":sigma_b.tolist(),"vector":v.tolist(),
      "sigma_a_min_eigenvalue":float(np.min(eig_a)),"sigma_b_min_eigenvalue":float(np.min(eig_b)),
      "diag_a":diag_a,"diag_b":diag_b,"full_a":full_a,"full_b":full_b,
      "psd":bool(np.min(eig_a)>=-1e-12 and np.min(eig_b)>=-1e-12),
      "diagonal_prefers_b":bool(diag_b<diag_a),"full_prefers_a":bool(full_a<full_b),
      "reversal":bool(diag_b<diag_a and full_a<full_b),
    }


def mixed_difference(world: FiniteResponseWorld, i: int, x: Sequence[int], c: Sequence[int]) -> float:
    x = tuple(int(a) for a in x); c = tuple(int(a) for a in c); i = int(i)
    ci_x = list(x); ci_x[i] = c[i]
    xi_c = list(c); xi_c[i] = x[i]
    return float(world.true_value(x) - world.true_value(tuple(ci_x)) - world.true_value(tuple(xi_c)) + world.true_value(c))


def hybrid_action(x: Sequence[int], c: Sequence[int], k: int) -> tuple[int, ...]:
    """LeanProductMixedDifferenceV4.hybrid: coordinates < k come from c, the rest from x."""
    x=tuple(int(a) for a in x); c=tuple(int(a) for a in c); k=int(k)
    if len(x)!=len(c): raise ValueError("hybrid actions must align")
    return tuple(c[j] if j<k else x[j] for j in range(len(x)))


def product_prob(action: Sequence[int], marginals: Mapping[int, Sequence[float]]) -> float:
    p = 1.0
    for j, a in enumerate(action): p *= float(np.asarray(marginals[j], dtype=np.float64)[int(a)])
    return float(p)


def d6_diagnostics(world: FiniteResponseWorld, marginals: Mapping[int, Sequence[float]], k: int) -> dict:
    """D6 diagnostics aligned with the active Lean telescoping identity.

    Q1/Q2/Q3 use the *hybrid* arguments from LeanProductMixedDifferenceV4.
    The fixed coordinate order leaves the final coordinate out of the telescoping
    sum, exactly as the Fin(n+1) theorem does.  Generic all-coordinate deltas are
    still reported for the original worst-case D6 bound.
    """
    sizes = world.support.action_sizes; full = tuple(world.support.full_product())
    if set(world.support.omega) != set(full):
        return {"applicable": False, "reason": "support_not_full_cartesian"}
    q = {j: _normalise_probabilities(marginals[j]) for j in range(len(sizes))}
    if any(q[j].shape != (sizes[j],) for j in range(len(sizes))):
        return {"applicable": False, "reason": "invalid_product_marginal"}
    baseline, rows, surrogate = product_reference_surrogate(world, q)
    errors = np.asarray([world.true_value(a) - surrogate(a) for a in full], dtype=np.float64)
    sup_error = float(np.max(np.abs(errors)))
    expected_abs = float(sum(product_prob(a, q) * abs(world.true_value(a) - surrogate(a)) for a in full))
    m=len(sizes)
    # Original uniform modulus ranges over every coordinate/x/c.
    all_coordinate_delta=[]
    for i in range(m):
        vals=[abs(mixed_difference(world,i,x,c)) for x in full for c in full]
        all_coordinate_delta.append(float(max(vals,default=0.0)))
    delta_square=float(max(all_coordinate_delta,default=0.0))
    worst_rhs=float(max(0,m-1)*delta_square)

    # Q1/Q2/Q3: exact hybrid telescoping terms for i=0,...,m-2.
    telescoping_coordinate_delta=[]; qabs_uniform=[]; qsigned_uniform=[]
    pointwise_qabs_rhs=[]; pointwise_qsigned_rhs=[]
    pointwise_residual_identity_error=[]
    for x in full:
        abs_terms=[]; signed_terms=[]
        for i in range(max(0,m-1)):
            dvals=[]; probs=[]
            for c in full:
                h=hybrid_action(x,c,i)
                dvals.append(mixed_difference(world,i,h,c)); probs.append(product_prob(c,q))
            dvals=np.asarray(dvals,dtype=np.float64); probs=np.asarray(probs,dtype=np.float64)
            abs_terms.append(float(np.sum(probs*np.abs(dvals))))
            signed_terms.append(float(np.sum(probs*dvals)))
        pointwise_qabs_rhs.append(float(np.sum(abs_terms)))
        pointwise_qsigned_rhs.append(float(np.sum(np.abs(signed_terms))))
        pointwise_residual_identity_error.append(abs((world.true_value(x)-surrogate(x))-float(np.sum(signed_terms))))
    for i in range(max(0,m-1)):
        raw=[]; abs_by_x=[]; signed_by_x=[]
        for x in full:
            dvals=[]; probs=[]
            for c in full:
                h=hybrid_action(x,c,i)
                dvals.append(mixed_difference(world,i,h,c)); probs.append(product_prob(c,q))
            dvals=np.asarray(dvals,dtype=np.float64); probs=np.asarray(probs,dtype=np.float64)
            raw.extend(np.abs(dvals).tolist())
            abs_by_x.append(float(np.sum(probs*np.abs(dvals))))
            signed_by_x.append(abs(float(np.sum(probs*dvals))))
        telescoping_coordinate_delta.append(float(max(raw,default=0.0)))
        qabs_uniform.append(float(max(abs_by_x,default=0.0)))
        qsigned_uniform.append(float(max(signed_by_x,default=0.0)))
    coordinate_sum_rhs=float(sum(all_coordinate_delta[:max(0,m-1)]))
    hybrid_coordinate_sum_rhs=float(sum(telescoping_coordinate_delta))
    qavg_sum_rhs=float(sum(qabs_uniform))
    qsigned_sum_rhs=float(sum(qsigned_uniform))
    qavg_pointwise_uniform_rhs=float(max(pointwise_qabs_rhs,default=0.0))
    qsigned_pointwise_uniform_rhs=float(max(pointwise_qsigned_rhs,default=0.0))
    qavg_distributional_rhs=float(sum(product_prob(x,q)*pointwise_qabs_rhs[idx] for idx,x in enumerate(full)))
    qsigned_distributional_rhs=float(sum(product_prob(x,q)*pointwise_qsigned_rhs[idx] for idx,x in enumerate(full)))

    score = np.asarray([float(np.ptp(row)) for row in rows], dtype=np.float64)
    components = tuple(np.asarray(row, dtype=np.float64) - float(baseline) for row in rows)
    def compression_loss(retained):
        retained = {int(j) for j in retained}
        residuals = np.asarray([world.true_value(a)-sum(components[j][a[j]] for j in retained) for a in full],dtype=np.float64)
        return 0.5*float(np.ptp(residuals))
    chosen=topk_indices(score,int(k)); optimum=float("inf")
    for retained in itertools.combinations(range(m),int(k)): optimum=min(optimum,compression_loss(retained))
    true_loss=compression_loss(chosen); decision_regret=float(true_loss-optimum)
    decision_rhs=float(2.0*worst_rhs)
    decision_candidate_half_rhs=float(0.5*worst_rhs)

    # Separately typed q-L1 objective for Q5.  Evaluate whether Top-C is actually
    # surrogate-optimal before applying the conditional 2*mean-error transfer.
    def ql1_loss(H, retained):
        retained={int(j) for j in retained}
        return float(sum(product_prob(a,q)*abs(H(a)-sum(rows[j][a[j]] for j in retained)) for a in full))
    surrogate_fn=lambda a: surrogate(a)
    ql1_selected_sur=ql1_loss(surrogate_fn,chosen)
    ql1_opt_sur=float("inf"); ql1_opt_true=float("inf"); ql1_best=None
    for retained in itertools.combinations(range(m),int(k)):
        s=ql1_loss(surrogate_fn,retained); t=ql1_loss(world.true_value,retained)
        if s<ql1_opt_sur-1e-12: ql1_opt_sur=s
        if t<ql1_opt_true-1e-12: ql1_opt_true=t; ql1_best=tuple(retained)
    ql1_true_selected=ql1_loss(world.true_value,chosen)
    ql1_surrogate_optimal=bool(ql1_selected_sur<=ql1_opt_sur+1e-10)
    ql1_regret=float(ql1_true_selected-ql1_opt_true)
    ql1_transfer_rhs=float(2.0*expected_abs)
    ql1_conditional_violation=float(ql1_regret-ql1_transfer_rhs) if ql1_surrogate_optimal else None

    return {
        "applicable": True, "baseline": float(baseline), "delta_square": delta_square,
        "all_coordinate_delta":all_coordinate_delta,"telescoping_coordinate_delta":telescoping_coordinate_delta,
        "qavg_abs_delta":qabs_uniform,"qsigned_abs_delta":qsigned_uniform,
        "surrogate_sup_error":sup_error,"surrogate_expected_abs_q":expected_abs,
        "worst_case_rhs":worst_rhs,"coordinate_sum_rhs":coordinate_sum_rhs,"hybrid_coordinate_sum_rhs":hybrid_coordinate_sum_rhs,"qavg_sum_rhs":qavg_sum_rhs,"qsigned_sum_rhs":qsigned_sum_rhs,
        "qavg_pointwise_uniform_rhs":qavg_pointwise_uniform_rhs,"qsigned_pointwise_uniform_rhs":qsigned_pointwise_uniform_rhs,
        "qavg_distributional_rhs":qavg_distributional_rhs,"qsigned_distributional_rhs":qsigned_distributional_rhs,
        "residual_identity_worst_error":float(max(pointwise_residual_identity_error,default=0.0)),
        "worst_case_violation":sup_error-worst_rhs,
        "coordinate_sum_violation":sup_error-coordinate_sum_rhs,
        "hybrid_coordinate_sum_violation":sup_error-hybrid_coordinate_sum_rhs,
        "qavg_uniform_candidate_violation":sup_error-qavg_sum_rhs,
        "qsigned_uniform_candidate_violation":sup_error-qsigned_sum_rhs,
        "qavg_pointwise_uniform_violation":sup_error-qavg_pointwise_uniform_rhs,
        "qsigned_pointwise_uniform_violation":sup_error-qsigned_pointwise_uniform_rhs,
        "qavg_distributional_candidate_violation":expected_abs-qavg_distributional_rhs,
        "qsigned_distributional_candidate_violation":expected_abs-qsigned_distributional_rhs,
        "surrogate_tightness":sup_error/worst_rhs if worst_rhs>0 else (0.0 if sup_error==0 else float("inf")),
        "chosen_topc":list(chosen),"true_decision_regret":decision_regret,"decision_rhs":decision_rhs,
        "decision_candidate_half_rhs":decision_candidate_half_rhs,"decision_candidate_half_violation":decision_regret-decision_candidate_half_rhs,
        "decision_violation":decision_regret-decision_rhs,
        "decision_tightness":decision_regret/decision_rhs if decision_rhs>0 else (0.0 if decision_regret==0 else float("inf")),
        "decision_ratio_to_worst_rhs":decision_regret/worst_rhs if worst_rhs>0 else (0.0 if decision_regret==0 else float("inf")),
        "qL1":{"topc_surrogate_loss":ql1_selected_sur,"surrogate_optimum":ql1_opt_sur,"topc_surrogate_optimal":ql1_surrogate_optimal,
               "true_topc_loss":ql1_true_selected,"true_optimum":ql1_opt_true,"true_optimum_set":list(ql1_best) if ql1_best is not None else None,
               "true_regret":ql1_regret,"transfer_rhs":ql1_transfer_rhs,"conditional_violation":ql1_conditional_violation},
    }

def arbitrary_full_world(values: np.ndarray) -> FiniteResponseWorld:
    values = np.asarray(values, dtype=np.float64)
    sizes = tuple(int(x) for x in values.shape); full = tuple(np.ndindex(*sizes)); residual = {a: float(values[a]) for a in full}
    primitives = tuple(np.zeros(size, dtype=np.float64) for size in sizes)
    return FiniteResponseWorld(SupportModel(sizes, full, key="full"), primitives, residual=residual)


def d6_sharpness_search(*, instances: int = 5000, seed: int = 0, m_values: Sequence[int] = (2,3,4), alphabet: int = 2) -> dict:
    rng = np.random.default_rng(seed); best_sur = (-1.0, None); best_dec = (-1.0, None); best_joint = (-1.0, None)
    for idx in range(int(instances)):
        m = int(m_values[idx % len(m_values)]); shape = (int(alphabet),) * m
        # integer-valued tables make witnesses easy to reconstruct/formalize.
        values = rng.integers(-3, 4, size=shape).astype(np.float64)
        world = arbitrary_full_world(values); marg = {j: np.full(shape[j], 1.0/shape[j]) for j in range(m)}; k = int(rng.integers(1, m+1))
        row = d6_diagnostics(world, marg, k)
        if not row.get("applicable"): continue
        sur = float(row["surrogate_tightness"]); dec = float(row["decision_tightness"])
        joint = min(sur, dec)
        witness = {"values": values.tolist(), "m":m,"k":k,"surrogate_tightness":sur,"decision_tightness":dec,"delta_square":row["delta_square"],"surrogate_sup_error":row["surrogate_sup_error"],"decision_regret":row["true_decision_regret"]}
        if np.isfinite(sur) and sur > best_sur[0]: best_sur=(sur,witness)
        if np.isfinite(dec) and dec > best_dec[0]: best_dec=(dec,witness)
        if np.isfinite(joint) and joint > best_joint[0]: best_joint=(joint,witness)
    return {"instances":int(instances),"seed":int(seed),"best_surrogate_ratio":best_sur[0],"best_surrogate_witness":best_sur[1],"best_decision_ratio":best_dec[0],"best_decision_witness":best_dec[1],"best_joint_min_ratio":best_joint[0],"best_joint_witness":best_joint[1]}


def d6_decision_adversarial_search(*, instances: int = 500, steps: int = 25, seed: int = 0, m_values: Sequence[int] = (3,4), alphabet: int = 2) -> dict:
    """Targeted falsification search for the proposed half-factor decision bound.

    Objective is regret / ((m-1) delta_square).  The proposed improved bound
    corresponds to ratio <= 1/2.  Search uses integer response tables plus a
    small local hill-climb and non-uniform product references.  It is a
    falsifier only: surviving this search is not a proof.
    """
    rng=np.random.default_rng(seed); best=(-float('inf'),None); qgrid=(0.1,0.25,0.5,0.75,0.9)
    for restart in range(int(instances)):
        m=int(m_values[restart % len(m_values)]); shape=(int(alphabet),)*m
        values=rng.integers(-4,5,size=shape).astype(np.float64)
        probs=[float(rng.choice(qgrid)) for _ in range(m)]
        k=int(rng.integers(1,max(2,m)))
        def marginals(ps):
            if alphabet != 2:
                return {j:np.full(alphabet,1.0/alphabet) for j in range(m)}
            return {j:np.asarray([ps[j],1.0-ps[j]],dtype=np.float64) for j in range(m)}
        def score(table,ps):
            row=d6_diagnostics(arbitrary_full_world(table),marginals(ps),k)
            den=float(row['worst_case_rhs'])
            ratio=float(row['true_decision_regret']/den) if den>1e-12 else (0.0 if row['true_decision_regret']<=1e-12 else float('inf'))
            return ratio,row
        current,current_row=score(values,probs)
        if np.isfinite(current) and current>best[0]:
            best=(current,{'values':values.tolist(),'m':m,'k':k,'product_probs':probs.copy(),'ratio_to_worst_rhs':current,'candidate_half_violation':float(current_row['decision_candidate_half_violation']),'decision_regret':float(current_row['true_decision_regret']),'worst_case_rhs':float(current_row['worst_case_rhs'])})
        for _ in range(int(steps)):
            cand=values.copy(); cand_probs=probs.copy()
            if rng.random()<0.8:
                idx=tuple(int(rng.integers(0,alphabet)) for _ in range(m)); cand[idx]+=float(rng.choice((-2,-1,1,2)))
            else:
                j=int(rng.integers(0,m)); cand_probs[j]=float(rng.choice(qgrid))
            candidate,candidate_row=score(cand,cand_probs)
            if candidate>=current-1e-15:
                values,probs,current,current_row=cand,cand_probs,candidate,candidate_row
                if np.isfinite(candidate) and candidate>best[0]:
                    best=(candidate,{'values':values.tolist(),'m':m,'k':k,'product_probs':probs.copy(),'ratio_to_worst_rhs':candidate,'candidate_half_violation':float(candidate_row['decision_candidate_half_violation']),'decision_regret':float(candidate_row['true_decision_regret']),'worst_case_rhs':float(candidate_row['worst_case_rhs'])})
    return {'instances':int(instances),'steps':int(steps),'seed':int(seed),'candidate_ratio_threshold':0.5,'best_ratio_to_worst_rhs':float(best[0]),'candidate_killed':bool(best[0]>0.5+1e-10),'best_witness':best[1]}


def epsilon_good_sets(loss_matrix: Sequence[Sequence[float]], epsilon: float) -> list[set[int]]:
    loss = np.asarray(loss_matrix, dtype=np.float64)
    if loss.ndim != 2 or not np.all(np.isfinite(loss)):
        raise ValueError("loss matrix must be finite models x decisions")
    out = []
    for row in loss:
        best = float(np.min(row)); out.append({int(i) for i, value in enumerate(row) if value <= best + float(epsilon) + 1e-12})
    return out


def representation_necessity_diagnostics(loss_matrix: Sequence[Sequence[float]], summaries: Sequence[int], epsilon: float) -> dict:
    """Finite-fiber diagnostic for QN1/QN2/QN4.

    A summary-based epsilon-good rule exists on a fiber iff the intersection of
    epsilon-good decision sets on that fiber is nonempty.  When it exists, this
    routine constructs one canonical rule (minimum-index common decision) and
    verifies its worst regret directly.
    """
    loss = np.asarray(loss_matrix, dtype=np.float64); summaries = np.asarray(summaries)
    if loss.ndim!=2 or loss.shape[0] != summaries.size:
        raise ValueError("one summary per model required")
    good = epsilon_good_sets(loss, epsilon); violations=[]; fibers={}; intersections={}; rule={}; realized=[]
    for idx, s in enumerate(summaries.tolist()): fibers.setdefault(str(s), []).append(idx)
    for key, models in fibers.items():
        intersection = set(range(loss.shape[1]))
        for i in models: intersection &= good[i]
        intersections[key]=sorted(intersection)
        if not intersection:
            violations.append({"summary":key,"models":models,"good_sets":[sorted(good[i]) for i in models]})
            continue
        chosen=min(intersection); rule[key]=int(chosen)
        for i in models:
            realized.append(float(loss[i,chosen]-np.min(loss[i])))
    return {
      "epsilon":float(epsilon),"fibers":fibers,"good_sets":[sorted(x) for x in good],
      "fiber_intersections":intersections,"common_good_failure_count":len(violations),"failures":violations,
      "constructive_summary_rule":rule,"constructive_rule_exists":len(violations)==0,
      "constructive_rule_max_regret":float(max(realized,default=0.0)),
      "constructive_rule_valid":bool(len(violations)==0 and max(realized,default=0.0)<=float(epsilon)+1e-10),
    }


def best_nested_prefix_regret(world: FiniteResponseWorld) -> dict:
    """Exact best all-budget nested chain via subset-lattice dynamic programming.

    This replaces factorial ranking enumeration.  For every retained subset we
    precompute the support-aware radius, then solve the minimax path from empty
    set to the full set on the subset lattice in O(m 2^m) transitions.
    """
    m=world.support.n_relations
    subsets=[frozenset(S) for r in range(m+1) for S in itertools.combinations(range(m),r)]
    value={S:float(world.additive_radius(tuple(sorted(S)))) for S in subsets}
    opt={k:min(value[S] for S in subsets if len(S)==k) for k in range(m+1)}
    regret={S:float(value[S]-opt[len(S)]) for S in subsets}
    empty=frozenset(); dp={empty:regret[empty]}; parent={empty:None}
    for k in range(1,m+1):
        for S in [x for x in subsets if len(x)==k]:
            candidates=[]
            for j in sorted(S):
                P=frozenset(set(S)-{j}); candidates.append((max(dp[P],regret[S]),j,P))
            best_cost,jbest,pbest=min(candidates,key=lambda x:(x[0],x[1]))
            dp[S]=float(best_cost); parent[S]=pbest
    full=frozenset(range(m)); chain=[]; cur=full
    while cur and parent[cur] is not None:
        chain.append(cur); cur=parent[cur]
    chain=list(reversed(chain))
    order=[]; prev=frozenset()
    for S in chain:
        added=sorted(set(S)-set(prev));
        if added: order.append(int(added[0]))
        prev=S
    per_budget=[float(regret[S]) for S in chain]
    spans=world.component_spans(); topc_order=tuple(sorted(range(m), key=lambda j:(-spans[j],j)))
    topc_regs=[float(value[frozenset(topc_order[:k])]-opt[k]) for k in range(1,m+1)]
    zetas=[zeta_def(world,k)/2.0 for k in range(1,m+1)]
    E=global_extremizability_defect(world)/2.0
    full_support=set(world.support.full_product()); missing_fraction=1.0-len(world.support.omega)/len(full_support)
    return {"best_nested_max_regret":float(dp[full]),"best_nested_order":order,"best_nested_per_budget":per_budget,"topc_max_regret":float(max(topc_regs,default=0.0)),"topc_per_budget":topc_regs,"max_zeta_half":float(max(zetas,default=0.0)),"E_half":float(E),"support_missing_fraction":float(missing_fraction),"zeta_bounds_best_nested_violation":float(dp[full]-max(zetas,default=0.0)),"algorithm":"subset_lattice_minimax_dp","subset_state_count":int(2**m)}


def all_optimal_extension_defect(world: FiniteResponseWorld, nested_result: Mapping | None = None) -> dict:
    """Support-radius version of the surviving 106,130-world Structural candidate.

    For each budget k and *every* optimal k-set, measure the least objective
    regret needed to extend it to a (k+1)-set; take the worst such value.
    The open candidate is best_nested_max_regret <= m * defect.
    """
    m=world.support.n_relations
    levels={0:[tuple()]}
    best={0:float(world.additive_radius(tuple()))}
    for k in range(1,m+1):
        value,sets=exact_optimum(world,k)
        best[k]=float(value); levels[k]=[tuple(sorted(map(int,S))) for S in sets]
    per_level=[]
    for k in range(0,m):
        worst_over_opt=0.0
        details=[]
        for S in levels[k]:
            sset=set(S); candidates=[]
            for T in itertools.combinations(range(m),k+1):
                if sset.issubset(T): candidates.append(float(world.additive_radius(T)-best[k+1]))
            local=min(candidates) if candidates else float('inf')
            worst_over_opt=max(worst_over_opt,local); details.append({'set':list(S),'best_extension_regret':float(local)})
        per_level.append({'k':k,'defect':float(worst_over_opt),'details':details})
    defect=float(max([x['defect'] for x in per_level],default=0.0))
    target=(best_nested_prefix_regret(world) if nested_result is None else nested_result)['best_nested_max_regret']
    return {'all_optimal_extension_defect':defect,'m_times_defect':float(m*defect),'best_nested_max_regret':float(target),'candidate_violation':float(target-m*defect),'per_level':per_level}


def cascade_evaluation(world: FiniteResponseWorld, estimated_scores: Sequence[float], errors: Sequence[float], k: int, tolerance: float) -> dict:
    selected = topk_indices(estimated_scores, int(k)); z = zeta_def(world,int(k)); eta=world.residual_supnorm()
    gamma = operational_gamma(estimated_scores,errors,int(k),selected); cert=pairwise_master_bound(gamma,z,eta)
    # Compute the exact optimum once.  We need it both to audit the candidate
    # certificate and, when necessary, to model the exact fallback branch.
    t0=time.perf_counter(); optimum, sets=exact_optimum(world,int(k),true_loss=True); exact_runtime=time.perf_counter()-t0
    candidate_regret=float(world.true_compression_loss(selected)-optimum)
    start=time.perf_counter()
    if cert <= float(tolerance):
        chosen=selected; fallback=False; branch_exact_runtime=0.0
    else:
        chosen=sets[0]; fallback=True; branch_exact_runtime=exact_runtime
    total_runtime=time.perf_counter()-start + branch_exact_runtime
    regret=float(world.true_compression_loss(chosen)-optimum)
    return {
        "certificate":float(cert),"tolerance":float(tolerance),"fallback":bool(fallback),
        "candidate_regret":candidate_regret,"regret":regret,
        "certificate_safe":bool((not fallback and candidate_regret<=max(float(tolerance),1e-9)) or fallback),
        "exact_runtime_seconds":float(branch_exact_runtime),"exact_optimum_runtime_seconds":float(exact_runtime),
        "cascade_runtime_seconds":float(total_runtime),
    }


def product_anova_decomposition(world: FiniteResponseWorld, marginals: Mapping[int, Sequence[float]]) -> dict:
    """Exact finite functional ANOVA under an independent product reference.

    Intended only as a small-domain experimental baseline for D6.  Returns
    weighted L2 mass by interaction order and reconstruction error.
    """
    sizes=world.support.action_sizes; m=len(sizes); full=tuple(world.support.full_product())
    if set(world.support.omega)!=set(full):
        raise ValueError("product ANOVA baseline requires full Cartesian support")
    q={j:_normalise_probabilities(marginals[j]) for j in range(m)}
    subsets=[S for r in range(m+1) for S in itertools.combinations(range(m),r)]
    components={}
    # Each component is a mapping from local assignment tuple to value.
    for S in subsets:
        S=tuple(S); table={}
        assignments=list(itertools.product(*(range(sizes[j]) for j in S))) if S else [()]
        others=[j for j in range(m) if j not in S]
        for local in assignments:
            fixed=dict(zip(S,local)); cond=0.0
            for other_values in itertools.product(*(range(sizes[j]) for j in others)):
                action=[0]*m; p=1.0
                for j,val in fixed.items(): action[j]=val
                for j,val in zip(others,other_values): action[j]=val; p*=float(q[j][val])
                cond+=p*world.true_value(tuple(action))
            lower=0.0
            for r in range(len(S)):
                for T in itertools.combinations(S,r):
                    key=tuple(fixed[j] for j in T); lower+=components[tuple(T)][key]
            table[local]=float(cond-lower)
        components[S]=table
    masses={r:0.0 for r in range(m+1)}
    reconstruction=0.0
    for a in full:
        recon=0.0
        p=product_prob(a,q)
        for S,table in components.items():
            val=table[tuple(a[j] for j in S)]; recon+=val; masses[len(S)]+=p*val*val
        reconstruction=max(reconstruction,abs(recon-world.true_value(a)))
    return {"l2_mass_by_order":{str(r):float(v) for r,v in masses.items()},"higher_order_l2_mass":float(sum(v for r,v in masses.items() if r>=2)),"reconstruction_sup_error":float(reconstruction)}
