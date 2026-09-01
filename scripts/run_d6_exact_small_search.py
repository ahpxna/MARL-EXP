"""Exact-rational, theorem-directed search for the D6 half-factor candidate.

Full enumeration is used only when the finite domain is genuinely exhausted.
Larger m/alphabet settings use an explicitly labelled selected-interaction
slice; those results are never reported as exhaustive over all response tables.
"""
from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from research_chains.provenance import write_artifact_with_provenance

PROTOCOL_VERSION = "d6_exact_product_q_h3_search_v4"


def _half_range(vals):
    return (max(vals) - min(vals)) / 2


def _joint_weight(action, q):
    out = Fraction(1)
    for coordinate, value in enumerate(action):
        out *= q[coordinate][value]
    return out


def _replace(action, coordinate, value):
    out = list(action)
    out[coordinate] = value
    return tuple(out)


def evaluate(values, m, k, q=None, alphabet=2):
    m, k, alphabet = int(m), int(k), int(alphabet)
    actions = tuple(itertools.product(range(alphabet), repeat=m))
    if len(values) != len(actions):
        raise ValueError("one exact value is required per joint action")
    F = {a: Fraction(v) for a, v in zip(actions, values)}
    if q is None:
        q = tuple(tuple(Fraction(1, alphabet) for _ in range(alphabet)) for _ in range(m))
    q = tuple(tuple(Fraction(x) for x in row) for row in q)
    if len(q) != m or any(len(row) != alphabet for row in q):
        raise ValueError("q must contain one alphabet-width marginal per coordinate")
    if any(any(x < 0 for x in row) or sum(row) != 1 for row in q):
        raise ValueError("q marginals must be nonnegative and normalized")

    weights = {a: _joint_weight(a, q) for a in actions}
    baseline = sum((F[a] * weights[a] for a in actions), Fraction(0))
    rows = []
    for j in range(m):
        row = []
        for aj in range(alphabet):
            value = Fraction(0)
            for a in actions:
                if a[j] != aj:
                    continue
                complement_weight = Fraction(1)
                for ell in range(m):
                    if ell != j:
                        complement_weight *= q[ell][a[ell]]
                value += F[a] * complement_weight
            row.append(value)
        rows.append(tuple(row))

    surrogate = {
        a: sum((rows[j][a[j]] for j in range(m)), Fraction(0)) - (m - 1) * baseline
        for a in actions
    }
    approximation_error = {a: F[a] - surrogate[a] for a in actions}
    sup_error = max(abs(v) for v in approximation_error.values())
    delta = Fraction(0)
    for i in range(m):
        for x in actions:
            for c in actions:
                mixed = F[x] - F[_replace(x, i, c[i])] - F[_replace(c, i, x[i])] + F[c]
                delta = max(delta, abs(mixed))

    scores = [max(row) - min(row) for row in rows]
    order = sorted(range(m), key=lambda j: (-scores[j], j))
    chosen = tuple(sorted(order[:k]))
    components = [tuple(v - baseline for v in row) for row in rows]

    def true_loss(S):
        retained = set(S)
        residual = {
            a: F[a] - sum((components[j][a[j]] for j in retained), Fraction(0))
            for a in actions
        }
        return _half_range(tuple(residual.values())), residual

    def surrogate_loss(S):
        retained = set(S)
        residual = {
            a: surrogate[a] - sum((components[j][a[j]] for j in retained), Fraction(0))
            for a in actions
        }
        return _half_range(tuple(residual.values()))

    subset_rows = []
    for S in itertools.combinations(range(m), k):
        loss, residual = true_loss(S)
        subset_rows.append((S, loss, surrogate_loss(S), residual))
    optimum = min(x[1] for x in subset_rows)
    optimal_sets = [x for x in subset_rows if x[1] == optimum]
    selected_row = next(x for x in subset_rows if x[0] == chosen)
    selected_loss, selected_surrogate_loss = selected_row[1], selected_row[2]
    surrogate_optimum = min(x[2] for x in subset_rows)
    true_second = min((x[1] for x in subset_rows if x[1] > optimum), default=optimum)
    score_margin = scores[order[k - 1]] - scores[order[k]] if k < m else Fraction(0)
    regret = selected_loss - optimum
    approx_rhs = Fraction(m - 1) * delta
    candidate = approx_rhs / 2
    ratio = regret / approx_rhs if approx_rhs else Fraction(0)

    best_opt = optimal_sets[0]
    def extremal_error_record(row):
        residual = row[3]
        max_action = max(actions, key=lambda a: (residual[a], a))
        min_action = min(actions, key=lambda a: (residual[a], a))
        return {
            "max_residual_action": max_action,
            "max_residual_approximation_error": approximation_error[max_action],
            "min_residual_action": min_action,
            "min_residual_approximation_error": approximation_error[min_action],
        }

    selected_transfer = selected_loss - selected_surrogate_loss
    optimal_transfer = best_opt[1] - best_opt[2]
    transfer_rows = [(row[0], row[1] - row[2]) for row in subset_rows]
    h3_competitor, minimum_transfer = min(transfer_rows, key=lambda item: (item[1], item[0]))
    h3_transfer_difference = selected_transfer - minimum_transfer
    h3_ratio = h3_transfer_difference / approx_rhs if approx_rhs else (
        Fraction(0) if h3_transfer_difference <= 0 else None)
    q_values = [x for row in q for x in row]
    near_tie = score_margin <= max(scores, default=Fraction(0)) / 10
    error_large = sum(abs(v) * 10 >= sup_error * 9 for v in approximation_error.values()) if sup_error else len(actions)
    if selected_transfer > 0 and optimal_transfer < 0:
        mechanism = "TWO_TRANSFER_ERRORS_ADVERSE"
    elif near_tie:
        mechanism = "SURROGATE_RANKING_NEAR_TIE"
    elif max(q_values) - min(q_values) >= Fraction(3, 4):
        mechanism = "Q_SKEW_CONCENTRATION"
    elif error_large <= 2:
        mechanism = "LOCALIZED_HIGHER_ORDER_ERROR"
    elif selected_transfer * optimal_transfer > 0:
        mechanism = "ONE_SIDE_CANCELLATION"
    else:
        mechanism = "MIXED_OR_UNCLASSIFIED"

    return {
        "delta": delta, "sup_error": sup_error, "approx_rhs": approx_rhs,
        "regret": regret, "candidate_rhs": candidate, "ratio": ratio,
        "chosen": chosen, "optimal_set": best_opt[0], "optimum": optimum,
        "selected_loss": selected_loss,
        "selected_surrogate_loss": selected_surrogate_loss,
        "surrogate_optimum": surrogate_optimum,
        "surrogate_optimality_gap_selected": selected_surrogate_loss - surrogate_optimum,
        "topc_score_margin": score_margin,
        "true_optimum_margin": true_second - optimum,
        "selected_extremal_errors": extremal_error_record(selected_row),
        "optimal_extremal_errors": extremal_error_record(best_opt),
        "selected_transfer_error": selected_transfer,
        "optimal_transfer_error": optimal_transfer,
        "h3_competitor": h3_competitor,
        "h3_minimum_competitor_transfer_error": minimum_transfer,
        "h3_transfer_difference": h3_transfer_difference,
        "h3_ratio": h3_ratio,
        "h3_candidate_half_violation": h3_transfer_difference - candidate,
        "mechanism_class": mechanism,
        "q": q,
    }


def fs(x):
    x = Fraction(x)
    return f"{x.numerator}/{x.denominator}"


def _compositions(total, width):
    if width == 1:
        yield (total,)
        return
    for head in range(total + 1):
        for tail in _compositions(total - head, width - 1):
            yield (head,) + tail


def marginal_grid(alphabet, q_grid, denominator, include_boundary):
    alphabet = int(alphabet)
    if alphabet == 2 and q_grid:
        return tuple((1 - Fraction(p), Fraction(p)) for p in q_grid)
    rows = []
    for counts in _compositions(int(denominator), alphabet):
        if not include_boundary and any(c == 0 for c in counts):
            continue
        rows.append(tuple(Fraction(c, int(denominator)) for c in counts))
    uniform = tuple(Fraction(1, alphabet) for _ in range(alphabet))
    if uniform not in rows:
        rows.append(uniform)
    return tuple(sorted(set(rows)))


def _selected_interaction_worlds(m, alphabet, radius):
    actions = tuple(itertools.product(range(alphabet), repeat=m))
    yield tuple(Fraction(0) for _ in actions)
    for amplitude in range(1, int(radius) + 1):
        for sign in (-1, 1):
            amp = Fraction(sign * amplitude)
            for location in actions:
                yield tuple(amp if a == location else Fraction(0) for a in actions)
            for order in range(2, m + 1):
                for subset in itertools.combinations(range(m), order):
                    yield tuple(amp if all(a[j] == alphabet - 1 for j in subset) else Fraction(0) for a in actions)
            yield tuple(amp if sum(a) % 2 else -amp for a in actions)


def run(m=3, k_values=(1, 2), value_radius=1, anchor_zero=True,
        stop_on_counterexample=False, q_grid=(Fraction(1, 2),), alphabet=2,
        world_family="full", q_denominator=4, include_boundary_q=False,
        max_worlds=None, max_reference_vectors=None):
    m, alphabet = int(m), int(alphabet)
    cells = alphabet ** m
    marginals = marginal_grid(alphabet, tuple(Fraction(x) for x in q_grid), q_denominator, include_boundary_q)
    q_vectors_all = tuple(itertools.product(marginals, repeat=m))
    q_vectors = q_vectors_all[: int(max_reference_vectors)] if max_reference_vectors else q_vectors_all
    reference_grid_complete = len(q_vectors) == len(q_vectors_all)

    if world_family == "full":
        vals = range(-int(value_radius), int(value_radius) + 1)
        iterator = itertools.product(vals, repeat=cells - 1 if anchor_zero else cells)
        nominal_world_count = len(vals) ** (cells - 1 if anchor_zero else cells)
        if max_worlds is None and nominal_world_count * max(1, len(q_vectors)) > 50_000_000:
            raise ValueError(
                "full exact grid is too large; provide --max-worlds (labelled exact slice) "
                "or --world-family selected_interactions"
            )
        def worlds():
            for index, tail in enumerate(iterator):
                if max_worlds is not None and index >= int(max_worlds):
                    break
                yield (0,) + tuple(tail) if anchor_zero else tuple(tail)
    elif world_family == "selected_interactions":
        selected = tuple(dict.fromkeys(_selected_interaction_worlds(m, alphabet, value_radius)))
        nominal_world_count = len(selected)
        def worlds():
            yield from selected[: int(max_worlds)] if max_worlds else selected
    else:
        raise ValueError("unknown world_family")

    total = evaluated = 0
    best = witness = None
    killed = False
    for values in worlds():
        total += 1
        for q in q_vectors:
            evaluated += 1
            for k in k_values:
                if not 1 <= int(k) < m:
                    continue
                result = evaluate(values, m, int(k), q, alphabet)
                objective = result["h3_ratio"]
                if objective is not None and (best is None or objective > best[0]):
                    best = (objective, values, int(k), result)
                if result["h3_transfer_difference"] > result["candidate_rhs"]:
                    killed = True
                    witness = (values, int(k), result)
                    if stop_on_counterexample:
                        break
            if killed and stop_on_counterexample:
                break
        if killed and stop_on_counterexample:
            break

    def pack(item):
        if item is None:
            return None
        values, k, result = (item[1], item[2], item[3]) if len(item) == 4 else item
        def error_record(record):
            return {
                "max_residual_action": list(record["max_residual_action"]),
                "max_residual_approximation_error": fs(record["max_residual_approximation_error"]),
                "min_residual_action": list(record["min_residual_action"]),
                "min_residual_approximation_error": fs(record["min_residual_approximation_error"]),
            }
        return {
            "values": [fs(x) for x in values], "shape": [alphabet] * m,
            "k": int(k),
            "reference_q": [[fs(x) for x in row] for row in result["q"]],
            "delta_square": fs(result["delta"]),
            "surrogate_sup_error": fs(result["sup_error"]),
            "approximation_rhs": fs(result["approx_rhs"]),
            "decision_regret": fs(result["regret"]),
            "candidate_half_rhs": fs(result["candidate_rhs"]),
            "ratio_regret_over_approx_rhs": fs(result["ratio"]),
            "chosen_topc": list(result["chosen"]),
            "true_optimal_set": list(result["optimal_set"]),
            "true_optimum_loss": fs(result["optimum"]),
            "surrogate_loss_topc": fs(result["selected_surrogate_loss"]),
            "surrogate_optimum": fs(result["surrogate_optimum"]),
            "surrogate_optimality_gap_topc": fs(result["surrogate_optimality_gap_selected"]),
            "topc_score_margin": fs(result["topc_score_margin"]),
            "true_optimum_margin": fs(result["true_optimum_margin"]),
            "selected_extremal_errors": error_record(result["selected_extremal_errors"]),
            "optimal_extremal_errors": error_record(result["optimal_extremal_errors"]),
            "selected_transfer_error": fs(result["selected_transfer_error"]),
            "optimal_transfer_error": fs(result["optimal_transfer_error"]),
            "h3_competitor": list(result["h3_competitor"]),
            "h3_minimum_competitor_transfer_error": fs(
                result["h3_minimum_competitor_transfer_error"]),
            "h3_transfer_difference": fs(result["h3_transfer_difference"]),
            "h3_ratio": None if result["h3_ratio"] is None else fs(result["h3_ratio"]),
            "h3_candidate_half_violation": fs(result["h3_candidate_half_violation"]),
            "mechanism_class": result["mechanism_class"],
        }

    world_grid_complete = total == nominal_world_count
    return {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": "EXHAUSTIVE_FINITE_EXACT_RATIONAL" if world_grid_complete and reference_grid_complete else "EXACT_RATIONAL_SELECTED_SLICE",
        "m": m, "alphabet": alphabet, "k_values": list(map(int, k_values)),
        "value_radius": int(value_radius), "world_family": world_family,
        "anchor_zero": bool(anchor_zero),
        "marginal_grid": [[fs(x) for x in row] for row in marginals],
        "reference_vectors_total": len(q_vectors_all),
        "reference_vectors_evaluated": len(q_vectors),
        "reference_vectors": len(q_vectors),
        "reference_grid_complete": reference_grid_complete,
        "worlds_nominal": nominal_world_count, "worlds_enumerated": total,
        "world_grid_complete": world_grid_complete,
        "world_reference_pairs_evaluated": evaluated,
        "candidate": "T(S_C)-T(T) <= (m-1)*delta_square/2 for every equal-cardinality T",
        "optimized_objective": "J_H3=(T(S_C)-min_T T(T))/((m-1)*delta_square)",
        "candidate_killed": killed, "counterexample": pack(witness),
        "best_ratio_witness": pack(best),
    }


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--m", type=int, default=3)
    p.add_argument("--alphabet", type=int, default=2)
    p.add_argument("--k-values", nargs="+", type=int, default=[1, 2])
    p.add_argument("--value-radius", type=int, default=1)
    p.add_argument("--world-family", choices=("full", "selected_interactions"), default="full")
    p.add_argument("--q-grid", nargs="+", default=["1/2"])
    p.add_argument("--q-denominator", type=int, default=4)
    p.add_argument("--include-boundary-q", action="store_true")
    p.add_argument("--max-worlds", type=int, default=None)
    p.add_argument("--max-reference-vectors", type=int, default=None)
    p.add_argument("--no-anchor-zero", action="store_true")
    p.add_argument("--stop-on-counterexample", action="store_true")
    p.add_argument("--out", default="research/high_value_extensions/d6/exact_small.json")
    a = p.parse_args(argv)
    payload = run(a.m, tuple(a.k_values), a.value_radius, not a.no_anchor_zero,
                  a.stop_on_counterexample, tuple(Fraction(x) for x in a.q_grid),
                  a.alphabet, a.world_family, a.q_denominator,
                  a.include_boundary_q, a.max_worlds, a.max_reference_vectors)
    write_artifact_with_provenance(Path(a.out), payload, protocol={
        "protocol_version": PROTOCOL_VERSION, "m": a.m, "alphabet": a.alphabet,
        "k_values": a.k_values, "value_radius": a.value_radius, "world_family": a.world_family,
        "q_grid": a.q_grid, "q_denominator": a.q_denominator,
    }, evidence_class=payload["evidence_class"], chain="D6")
    print(json.dumps(payload, indent=2))
    return 2 if payload["candidate_killed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
