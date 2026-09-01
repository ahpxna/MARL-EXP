"""Theorem-directed falsification of the open D6 half-factor candidate.

Optimizes normalized decision regret, supports local search from an existing
near-boundary witness, and records proof-relevant mechanism diagnostics.
This runner is a falsifier, never a proof.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from research_chains.provenance import write_artifact_with_provenance

PROTOCOL_VERSION = "d6_h3_transfer_counterexample_optimizer_v4"


def _actions(m, alphabet):
    return tuple(itertools.product(range(alphabet), repeat=m))


def _half_range(values):
    return (max(values) - min(values)) / 2


def _update(x, i, u):
    y = list(x); y[i] = u
    return tuple(y)


def _evaluate(values, m, k, q):
    alphabet = int(values.shape[0]); actions = _actions(m, alphabet)
    weights = {a: float(np.prod([q[j][a[j]] for j in range(m)])) for a in actions}
    baseline = sum(weights[a] * float(values[a]) for a in actions)
    rows = []
    for j in range(m):
        rows.append(tuple(sum(
            float(values[a]) * np.prod([q[ell][a[ell]] for ell in range(m) if ell != j])
            for a in actions if a[j] == u
        ) for u in range(alphabet)))
    surrogate = {a: sum(rows[j][a[j]] for j in range(m)) - (m - 1) * baseline for a in actions}
    approximation_error = {a: float(values[a]) - surrogate[a] for a in actions}
    sup_error = max(abs(v) for v in approximation_error.values())
    delta = 0.0
    for i in range(m):
        for x in actions:
            for c in actions:
                mixed = (float(values[x]) - float(values[_update(x, i, c[i])])
                         - float(values[_update(c, i, x[i])]) + float(values[c]))
                delta = max(delta, abs(mixed))
    scores = [max(row) - min(row) for row in rows]
    order = sorted(range(m), key=lambda j: (-scores[j], j))
    chosen = tuple(sorted(order[:k]))
    score_margin = scores[order[k - 1]] - scores[order[k]] if k < m else 0.0
    components = [tuple(v - baseline for v in row) for row in rows]

    def residual(S, world):
        kept = set(S)
        return {a: world[a] - sum(components[j][a[j]] for j in kept) for a in actions}

    def true_loss(S):
        r = residual(S, {a: float(values[a]) for a in actions})
        return _half_range(tuple(r.values())), r

    def surrogate_loss(S):
        return _half_range(tuple(residual(S, surrogate).values()))

    subset_rows = [(S, *true_loss(S), surrogate_loss(S)) for S in itertools.combinations(range(m), k)]
    optimum = min(x[1] for x in subset_rows)
    optimum_rows = [x for x in subset_rows if abs(x[1] - optimum) <= 1e-10]
    chosen_row = next(x for x in subset_rows if x[0] == chosen)
    opt_row = optimum_rows[0]
    surrogate_optimum = min(x[3] for x in subset_rows)
    true_second = min((x[1] for x in subset_rows if x[1] > optimum + 1e-10), default=optimum)
    regret = chosen_row[1] - optimum
    rhs = (m - 1) * delta

    def extremal(row):
        r = row[2]
        hi = max(actions, key=lambda a: (r[a], a)); lo = min(actions, key=lambda a: (r[a], a))
        return {"max_residual_action": list(hi), "max_residual_error": approximation_error[hi],
                "min_residual_action": list(lo), "min_residual_error": approximation_error[lo]}

    selected_transfer = chosen_row[1] - chosen_row[3]
    optimal_transfer = opt_row[1] - opt_row[3]
    transfer_rows = [(row[0], row[1] - row[3]) for row in subset_rows]
    h3_competitor, minimum_transfer = min(transfer_rows, key=lambda item: (item[1], item[0]))
    h3_transfer_difference = selected_transfer - minimum_transfer
    h3_ratio = h3_transfer_difference / rhs if rhs > 1e-12 else (
        0.0 if h3_transfer_difference <= 1e-12 else float("inf"))
    q_values = [float(x) for row in q.values() for x in row]
    near_tie = score_margin <= max(1e-10, .1 * max(scores, default=0.0))
    localized = sum(abs(v) >= .9 * sup_error for v in approximation_error.values()) <= 2 if sup_error else False
    if selected_transfer > 0 and optimal_transfer < 0:
        mechanism = "TWO_TRANSFER_ERRORS_ADVERSE"
    elif near_tie:
        mechanism = "SURROGATE_RANKING_NEAR_TIE"
    elif max(q_values) - min(q_values) >= .75:
        mechanism = "Q_SKEW_CONCENTRATION"
    elif localized:
        mechanism = "LOCALIZED_HIGHER_ORDER_ERROR"
    elif selected_transfer * optimal_transfer > 0:
        mechanism = "ONE_SIDE_CANCELLATION"
    else:
        mechanism = "MIXED_OR_UNCLASSIFIED"

    return {
        "delta_square": delta, "product_surrogate_sup_error": sup_error,
        "worst_case_rhs": rhs, "true_decision_regret": regret,
        "decision_candidate_half_rhs": rhs / 2,
        "decision_candidate_half_violation": regret - rhs / 2,
        "chosen_topc": list(chosen), "exact_optimal_sets": [list(x[0]) for x in optimum_rows],
        "selected_true_loss": chosen_row[1], "true_optimum_loss": optimum,
        "selected_surrogate_loss": chosen_row[3], "true_optimum_set_surrogate_loss": opt_row[3],
        "surrogate_optimum_loss": surrogate_optimum,
        "surrogate_objective_difference_topc_vs_true_opt": chosen_row[3] - opt_row[3],
        "topc_score_margin": score_margin, "true_optimum_margin": true_second - optimum,
        "selected_transfer_error": selected_transfer, "optimal_transfer_error": optimal_transfer,
        "h3_competitor": list(h3_competitor),
        "h3_minimum_competitor_transfer_error": minimum_transfer,
        "h3_transfer_difference": h3_transfer_difference,
        "h3_ratio": h3_ratio,
        "h3_candidate_half_violation": h3_transfer_difference - rhs / 2,
        "selected_extremal_errors": extremal(chosen_row), "optimal_extremal_errors": extremal(opt_row),
        "mechanism_class": mechanism,
        "reference_q": {str(j): q[j].tolist() for j in range(m)},
    }


def _score(values, m, k, q):
    detail = _evaluate(values, m, k, q)
    return float(detail["h3_ratio"]), detail


def _sample_q(rng, m, alphabet, mode):
    if mode == "uniform": return {j: np.full(alphabet, 1 / alphabet) for j in range(m)}
    if mode == "boundary": return {j: np.eye(alphabet)[int(rng.integers(0, alphabet))] for j in range(m)}
    if mode == "skewed": return {j: rng.dirichlet(np.full(alphabet, .12)) for j in range(m)}
    if mode == "random": return {j: rng.dirichlet(np.ones(alphabet)) for j in range(m)}
    raise ValueError(f"unknown q mode: {mode}")


def _number(value):
    if isinstance(value, str) and "/" in value:
        a, b = value.split("/", 1); return float(a) / float(b)
    return float(value)


def _numeric_array(values):
    array=np.asarray(values,dtype=object)
    return np.asarray([_number(x) for x in array.reshape(-1)],dtype=float).reshape(array.shape)


def _read_witness(path):
    if not path: return None
    payload = json.loads(Path(path).read_text())
    for key in ("best_witness", "best_ratio_witness", "counterexample"):
        if isinstance(payload, dict) and payload.get(key): payload = payload[key]; break
    return payload


def _lift_witness(witness, m, alphabet, q_mode, rng):
    if not witness: return None, None, "random"
    raw = _numeric_array(witness.get("values", []))
    source_shape = tuple(witness.get("shape", []))
    if source_shape: raw = raw.reshape(source_shape)
    target = np.zeros((alphabet,) * m, dtype=float)
    for index in np.ndindex(target.shape):
        source = tuple(min(index[j], raw.shape[j] - 1) for j in range(raw.ndim))
        target[index] = raw[source]
    q = _sample_q(rng, m, alphabet, q_mode)
    source_q = witness.get("reference_q")
    if source_q:
        rows = list(source_q.values()) if isinstance(source_q, dict) else source_q
        for j, row in enumerate(rows[:m]):
            vals = np.asarray([_number(x) for x in row], dtype=float)
            if len(vals) == alphabet and vals.sum() > 0: q[j] = vals / vals.sum()
    return target, q, "lifted_duplicate_or_alphabet_extension"


def _mutate(x, q, rng, value_clip, optimize_q):
    y = x.copy(); qy = {j: row.copy() for j, row in q.items()}
    modes = ["interaction_cell", "localized_spike", "higher_order_block"]
    if optimize_q: modes += ["q_logit", "asymmetric_marginal"]
    mode = modes[int(rng.integers(0, len(modes)))]
    if mode in {"q_logit", "asymmetric_marginal"}:
        j = int(rng.integers(0, len(qy))); logits = np.log(np.maximum(qy[j], 1e-12))
        logits[int(rng.integers(0, len(logits)))] += float(rng.normal(0, 1.2 if mode == "asymmetric_marginal" else .5))
        logits -= np.max(logits); qy[j] = np.exp(logits); qy[j] /= qy[j].sum()
    elif mode == "higher_order_block":
        coords = rng.choice(x.ndim, size=int(rng.integers(2, x.ndim + 1)), replace=False)
        levels = [int(rng.integers(0, x.shape[j])) for j in coords]; change = float(rng.choice([-2., -1., 1., 2.]))
        for index in np.ndindex(x.shape):
            if all(index[j] == u for j, u in zip(coords, levels)):
                y[index] = np.clip(y[index] + change, -value_clip, value_clip)
    else:
        index = tuple(int(rng.integers(0, s)) for s in x.shape)
        choices = [-3., -2., -1., 1., 2., 3.] if mode == "localized_spike" else [-2., -1., 1., 2.]
        y[index] = np.clip(y[index] + rng.choice(choices), -value_clip, value_clip)
    return y, qy, mode


def run(restarts=2000, steps=200, m=3, alphabet=2, k=1, seed=0, value_clip=8.0,
        temp0=.5, q_mode="uniform", optimize_q=False, seed_witness=None, local_restart_fraction=.5):
    rng = np.random.default_rng(int(seed)); shape = (int(alphabet),) * int(m)
    source = _read_witness(seed_witness)
    lifted_x, lifted_q, seed_transform = _lift_witness(source, m, alphabet, q_mode, rng)
    best = (-1.0, None, None, None); killed = False; accepts = {}; improvements = {}
    for restart in range(int(restarts)):
        use_local = lifted_x is not None and restart < max(1, int(restarts * float(local_restart_fraction)))
        if use_local:
            x = lifted_x.copy() + (rng.normal(0, .05, size=shape) if restart else 0)
            q = {j: row.copy() for j, row in lifted_q.items()}
        else:
            x = rng.integers(-3, 4, size=shape).astype(float); q = _sample_q(rng, m, alphabet, q_mode)
        current, detail = _score(x, m, k, q); temp = float(temp0)
        if current > best[0]: best = (current, x.copy(), detail, "initial")
        for _ in range(int(steps)):
            y, qy, mutation = _mutate(x, q, rng, float(value_clip), bool(optimize_q))
            score, candidate = _score(y, m, k, qy)
            if score >= current or rng.random() < math.exp((score - current) / max(temp, 1e-8)):
                accepts[mutation] = accepts.get(mutation, 0) + 1; x, q, current, detail = y, qy, score, candidate
            if score > best[0]:
                improvements[mutation] = improvements.get(mutation, 0) + 1; best = (score, y.copy(), candidate, mutation)
            if score > .5 + 1e-12: killed = True; break
            temp *= .985
        if killed: break
    ratio, values, detail, best_mutation = best
    packed = None if values is None else {"values": values.tolist(), "shape": list(values.shape),
        "m": int(m), "alphabet": int(alphabet), "k": int(k),
        "optimized_objective": "J_H3=(T(selected)-min_equal_cardinality_T(T))/(m-1)delta",
        "best_h3_ratio": float(ratio), "best_mutation": best_mutation, **detail}
    return {"protocol_version": PROTOCOL_VERSION, "evidence_class": "DIRECTED_FALSIFICATION_NOT_PROOF",
        "candidate_threshold": .5, "candidate_killed": bool(killed), "restarts_requested": int(restarts),
        "steps_per_restart": int(steps), "seed": int(seed), "m": int(m), "alphabet": int(alphabet),
        "k": int(k), "q_mode": q_mode, "optimize_q": bool(optimize_q), "seed_witness": seed_witness,
        "seed_transform": seed_transform, "local_restart_fraction": float(local_restart_fraction),
        "mutation_accepts": accepts, "mutation_improvements": improvements, "best_witness": packed}


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--restarts", type=int, default=2000); p.add_argument("--steps", type=int, default=200)
    p.add_argument("--m", type=int, default=3); p.add_argument("--alphabet", type=int, default=2)
    p.add_argument("--k", type=int, default=1); p.add_argument("--seed", type=int, default=100)
    p.add_argument("--value-clip", type=float, default=8); p.add_argument("--temp0", type=float, default=.5)
    p.add_argument("--q-mode", choices=["uniform", "random", "skewed", "boundary"], default="uniform")
    p.add_argument("--optimize-q", action="store_true"); p.add_argument("--seed-witness", default=None)
    p.add_argument("--local-restart-fraction", type=float, default=.5)
    p.add_argument("--out", default="research/high_value_extensions/d6/counterexample_optimizer.json")
    a = p.parse_args(argv)
    payload = run(a.restarts, a.steps, a.m, a.alphabet, a.k, a.seed, a.value_clip, a.temp0,
                  a.q_mode, a.optimize_q, a.seed_witness, a.local_restart_fraction)
    write_artifact_with_provenance(Path(a.out), payload, protocol={
        "protocol_version": PROTOCOL_VERSION, "m": a.m, "alphabet": a.alphabet, "k": a.k,
        "restarts": a.restarts, "steps": a.steps, "q_mode": a.q_mode,
        "optimize_q": a.optimize_q, "seed_witness": a.seed_witness,
    }, seed=a.seed, evidence_class=payload["evidence_class"], chain="D6")
    print(json.dumps(payload, indent=2))
    return 2 if payload["candidate_killed"] else 0


if __name__ == "__main__": raise SystemExit(main())
