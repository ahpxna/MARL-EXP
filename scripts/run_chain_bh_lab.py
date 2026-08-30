"""Deterministic/randomized B+H certificate laboratory (development only)."""
from __future__ import annotations

# Allow both `python -m scripts.<runner>` and direct `python scripts/<runner>.py`.
import sys
from pathlib import Path as _BootstrapPath
_REPO_ROOT = _BootstrapPath(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
import argparse, json
from pathlib import Path
import numpy as np

from research_chains.certificates import (
    deficit_terms, exact_optimum, fixed_subset_radius_error_bound,
    global_extremizability_defect, lp_lower_bound, quotient_sup_distance,
    support_bracket_regret_bound, topc_regret, topk_indices, zeta_def,
    delta_k_circ,
)
from research_chains.finite_world import FiniteResponseWorld
from research_chains.support import SupportBracket, SupportModel, projected_span_bracket
from research_chains.provenance import atomic_json

PROTOCOL_VERSION = "chain_bh_exact_lab_v3"


def _world(rng, m=4):
    sizes = (2,) * m
    full = list(np.ndindex(*sizes))
    mask = rng.random(len(full)) < rng.uniform(0.35, 0.9)
    omega = [a for a, keep in zip(full, mask) if keep]
    if not omega: omega = [full[int(rng.integers(len(full)))]]
    # Ensure every coordinate has at least one projected action; automatic for nonempty support.
    primitives = tuple(rng.normal(size=size) for size in sizes)
    eta_scale = float(rng.uniform(0.0, 0.35))
    residual = {
        tuple(a): float(rng.uniform(-eta_scale, eta_scale)) for a in full
    }
    return FiniteResponseWorld(
        SupportModel(sizes, tuple(omega), key="truth"), primitives,
        residual=residual,
    )


def run(instances=500, seed=0):
    rng = np.random.default_rng(seed)
    worst = {
        "deficit_identity": 0.0,
        "zeta_half": 0.0,
        "E_half": 0.0,
        "lp": 0.0,
        "support_bracket": 0.0,
        "span_bracket": 0.0,
        "gauge_stability": 0.0,
        "delta_circ_fixed_subset": 0.0,
        "two_delta_circ": 0.0,
        "cert_master": 0.0,
    }
    failures = []
    rows = []
    for idx in range(int(instances)):
        world = _world(rng)
        m = world.support.n_relations
        k = int(rng.integers(1, m + 1))
        for omitted_size in range(1, m + 1):
            import itertools
            for omitted in itertools.combinations(range(m), omitted_size):
                t = deficit_terms(world, omitted)
                err = abs(t["d"] - (t["e_plus"] + t["e_minus"]))
                worst["deficit_identity"] = max(worst["deficit_identity"], err)
                if t["d"] < -1e-9 or err > 1e-9:
                    failures.append({"kind":"deficit", "idx":idx, "omitted":omitted, "terms":t})
        regret = topc_regret(world, k)
        z = zeta_def(world, k); E = global_extremizability_defect(world)
        worst["zeta_half"] = max(worst["zeta_half"], regret - z/2)
        worst["E_half"] = max(worst["E_half"], regret - E/2)
        lb, _ = lp_lower_bound(world, k)
        opt, _ = exact_optimum(world, k)
        worst["lp"] = max(worst["lp"], lb - opt)
        spans = world.component_spans(); topc = topk_indices(spans, k)
        # Build a valid lower/upper support bracket around truth.
        truth = set(world.support.omega); full = set(world.support.full_product())
        lower_items = [a for a in truth if rng.random() < 0.65]
        if not lower_items: lower_items = [next(iter(truth))]
        upper = tuple(sorted(truth | {a for a in full-truth if rng.random() < 0.30}))
        bracket = SupportBracket(
            SupportModel(world.support.action_sizes, tuple(lower_items), key="lower"),
            SupportModel(world.support.action_sizes, upper, key="upper"),
        )
        bound = support_bracket_regret_bound(world, bracket, topc, k)
        actual = world.additive_radius(topc) - opt
        worst["support_bracket"] = max(worst["support_bracket"], actual - bound)
        cminus, cplus = projected_span_bracket(world.primitives, bracket)
        ctrue = world.component_spans()
        span_violation = max(float(np.max(cminus-ctrue)), float(np.max(ctrue-cplus)))
        worst["span_bracket"] = max(worst["span_bracket"], span_violation)

        # B8/B9 native learned-component perturbation.  Add deliberately large
        # arbitrary gauges plus bounded shape noise so the experiment fails if
        # the implementation accidentally uses raw ||fhat-f||_inf.
        shape_noises = tuple(
            rng.uniform(-rng.uniform(0.0, 0.25), rng.uniform(0.0, 0.25), size=v.shape)
            for v in world.primitives
        )
        # Rebuild symmetric bounded shape noise; the two independent bounds
        # above can reverse, so normalise explicitly.
        shape_noises = tuple(
            np.asarray(noise, dtype=np.float64) for noise in shape_noises
        )
        gauges = rng.normal(loc=0.0, scale=50.0, size=m)
        estimated_primitives = tuple(
            world.primitives[j] + shape_noises[j] + float(gauges[j]) for j in range(m)
        )
        shape_only_primitives = tuple(
            world.primitives[j] + shape_noises[j] for j in range(m)
        )
        estimated_world = FiniteResponseWorld(world.support, estimated_primitives)
        shape_world = FiniteResponseWorld(world.support, shape_only_primitives)
        deltas = np.asarray([
            quotient_sup_distance(est, true)
            for est, true in zip(estimated_primitives, world.primitives)
        ], dtype=np.float64)
        deltas_shape = np.asarray([
            quotient_sup_distance(est, true)
            for est, true in zip(shape_only_primitives, world.primitives)
        ], dtype=np.float64)
        gauge_violation = float(np.max(np.abs(deltas - deltas_shape)))
        # Radius/certificate geometry must also be invariant to component gauges.
        estimated_topc = topk_indices(estimated_world.component_spans(), k)
        shape_topc = topk_indices(shape_world.component_spans(), k)
        gauge_violation = max(
            gauge_violation,
            abs(estimated_world.additive_radius(estimated_topc) - shape_world.additive_radius(shape_topc)),
            abs(global_extremizability_defect(estimated_world) - global_extremizability_defect(shape_world)),
        )
        estimated_lb, _ = lp_lower_bound(estimated_world, k)
        shape_lb, _ = lp_lower_bound(shape_world, k)
        gauge_violation = max(gauge_violation, abs(estimated_lb - shape_lb))
        worst["gauge_stability"] = max(worst["gauge_stability"], gauge_violation)

        fixed_retained = tuple(topc)
        fixed_bound, _ = fixed_subset_radius_error_bound(
            world, estimated_primitives, fixed_retained
        )
        fixed_error = abs(
            estimated_world.additive_radius(fixed_retained)
            - world.additive_radius(fixed_retained)
        )
        fixed_violation = fixed_error - fixed_bound
        worst["delta_circ_fixed_subset"] = max(
            worst["delta_circ_fixed_subset"], fixed_violation
        )

        delta_k = delta_k_circ(deltas, k)
        estimated_opt, estimated_opt_sets = exact_optimum(estimated_world, k)
        estimated_selector = tuple(estimated_opt_sets[0])
        two_delta_actual = world.additive_radius(estimated_selector) - opt
        two_delta_violation = two_delta_actual - 2.0 * delta_k
        worst["two_delta_circ"] = max(
            worst["two_delta_circ"], two_delta_violation
        )

        estimated_E = global_extremizability_defect(estimated_world)
        estimated_topc_radius = estimated_world.additive_radius(estimated_topc)
        cert_geometry = min(
            estimated_E / 2.0,
            estimated_topc_radius - estimated_lb,
        )
        eta = world.residual_supnorm()
        true_opt, _ = exact_optimum(world, k, true_loss=True)
        true_regret = world.true_compression_loss(estimated_topc) - true_opt
        cert_rhs = cert_geometry + 2.0 * delta_k + 2.0 * eta
        cert_violation = true_regret - cert_rhs
        worst["cert_master"] = max(worst["cert_master"], cert_violation)

        if max(
            regret-z/2, regret-E/2, lb-opt, actual-bound, span_violation,
            gauge_violation, fixed_violation, two_delta_violation, cert_violation,
        ) > 1e-8:
            failures.append({
                "kind":"bound", "idx":idx, "k":k, "regret":regret,
                "zeta":z, "E":E, "lp":lb, "opt":opt,
                "support_bound":bound, "gauge_violation":gauge_violation,
                "fixed_delta_circ_violation":fixed_violation,
                "two_delta_circ_violation":two_delta_violation,
                "cert_master_violation":cert_violation,
            })
        rows.append({
            "k":k,"regret":regret,"zeta_half":z/2,"E_half":E/2,
            "lp_gap":opt-lb,"support_bound":bound,"delta_k_circ":delta_k,
            "true_regret_estimated_topc":true_regret,"cert_rhs":cert_rhs,
        })
    return {"protocol_version":PROTOCOL_VERSION,"development_only":True,"instances":int(instances),"seed":int(seed),"failures":failures[:20],"failure_count":len(failures),"worst_violation":worst,"summary":{"mean_regret":float(np.mean([r['regret'] for r in rows])),"nonzero_regret_fraction":float(np.mean([r['regret']>1e-12 for r in rows]))}}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument("--instances",type=int,default=500); p.add_argument("--seed",type=int,default=0); p.add_argument("--out",default="research/new_chains_v2/chain_bh/summary.json"); a=p.parse_args(argv)
    payload=run(a.instances,a.seed); atomic_json(Path(a.out),payload); print(json.dumps({k:payload[k] for k in ('protocol_version','instances','failure_count','worst_violation')},indent=2)); return 0 if payload['failure_count']==0 else 2
if __name__=='__main__': raise SystemExit(main())
