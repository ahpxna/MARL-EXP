"""B3: direct raw-world D6 search constrained by centred-profile minors.

Unlike the B1/B-product/B2 factor generators, this tool optimizes raw world
values.  Its equality constraints are an independent pivot basis for *all*
2-by-2 centred-profile minors.  A floating optimizer outcome is only a lead:
it is rationalized and then verified with the exact evaluator before it may be
reported as a counterexample.

The initial protocol is intentionally limited to m=4, K=3.  Raw finite-
difference SLSQP is not a credible m=6/8 solver; reporting it as such would
create false coverage.  Those dimensions require an analytic-gradient or
exact constrained solver in a later, separately declared B3 extension.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import random
import sys
from typing import Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from research_chains.provenance import write_artifact_with_provenance
from scripts.run_d6_half_factor_lemma_falsification import evaluate_float
from scripts.run_d6_rankone_falsification import (
    actions, evaluate_candidate, feature_values, fraction_text, make_world,
    q_payload, reference_rows, world_payload,
)


PROTOCOL_VERSION = "d6_direct_rankone_profile_minor_search_v1"
EVIDENCE_CLASS = "NUMERICAL_LEAD_WITH_EXACT_RATIONAL_RECHECK"


def _response_float(flat: np.ndarray, q: np.ndarray, m: int, alphabet: int) -> np.ndarray:
    tensor = flat.reshape((alphabet,) * m)
    out = np.zeros((m, alphabet), dtype=float)
    for i in range(m):
        other = [j for j in range(m) if j != i]
        for u in range(alphabet):
            total = 0.0
            for values in itertools.product(range(alphabet), repeat=m - 1):
                point = [0] * m
                point[i] = u
                weight = 1.0
                for j, value in zip(other, values):
                    point[j] = value
                    weight *= q[j, value]
                total += weight * tensor[tuple(point)]
            out[i, u] = total
    return out


def _profile_matrix(flat: np.ndarray, q: np.ndarray, m: int, alphabet: int, i: int) -> np.ndarray:
    tensor = flat.reshape((alphabet,) * m)
    response = _response_float(flat, q, m, alphabet)
    rows = []
    for zminus in itertools.product(range(alphabet), repeat=m - 1):
        z = [0] * m
        for j, value in zip((j for j in range(m) if j != i), zminus):
            z[j] = value
        row = []
        for u in range(1, alphabet):
            a_u = list(z); a_u[i] = u
            a_0 = list(z); a_0[i] = 0
            row.append((tensor[tuple(a_u)] - tensor[tuple(a_0)]) - (response[i, u] - response[i, 0]))
        rows.append(row)
    return np.asarray(rows, dtype=float).T  # non-anchor action x context


def _minor_basis(flat: np.ndarray, q: np.ndarray, m: int, alphabet: int, pivots: Sequence[int]) -> np.ndarray:
    values = []
    for i in range(m):
        profile = _profile_matrix(flat, q, m, alphabet, i)
        pivot = int(pivots[i])
        # K=3 gives a 2 by (#contexts) matrix.  These equations are exactly
        # equivalent to all its 2x2 minors when the fixed pivot column is
        # nonzero; starts choose a nonzero pivot, and post-check verifies all
        # minors without relying on that condition.
        for col in range(profile.shape[1]):
            values.append(profile[0, col] * profile[1, pivot] - profile[0, pivot] * profile[1, col])
    return np.asarray(values, dtype=float)


def _float_q(rows: Sequence[Sequence[Fraction]]) -> np.ndarray:
    return np.asarray([[float(v) for v in row] for row in rows], dtype=float)


def _raw_to_exact(flat: np.ndarray, m: int, alphabet: int, denominator: int) -> dict:
    values = [Fraction(float(v)).limit_denominator(int(denominator)) for v in flat]
    return {a: values[index] for index, a in enumerate(actions(m, alphabet))}


def _initial_world(rng: random.Random, m: int, alphabet: int) -> dict:
    # Starting only on a feasible rank-one point stabilizes SLSQP.  The
    # optimizer itself subsequently operates on raw F-values and minors.
    world, _ = make_world("B2_multiaffine", m, alphabet, rng, 3, Fraction(1, 2))
    return world


def run(args: argparse.Namespace) -> dict:
    m, alphabet = int(args.m), int(args.alphabet)
    if (m, alphabet) != (4, 3):
        return {
            "protocol_version": PROTOCOL_VERSION,
            "status": "BLOCKED_NOT_RUN",
            "reason": "v1 has a declared raw-world SLSQP scope of m=4,K=3 only; m=6/8 need an analytic-gradient or exact direct solver.",
            "m": m, "alphabet": alphabet,
        }
    try:
        from scipy.optimize import minimize
    except ModuleNotFoundError:
        return {
            "protocol_version": PROTOCOL_VERSION,
            "status": "BLOCKED_REQUIRED_RUNTIME",
            "reason": "B3 v1 needs scipy.optimize.SLSQP; select the project Python runtime that provides SciPy rather than silently substituting an optimizer.",
            "m": m, "alphabet": alphabet,
        }
    rng = random.Random(int(args.seed))
    q_rows = reference_rows(m, alphabet, args.reference_mode)
    q = _float_q(q_rows)
    all_actions = actions(m, alphabet)
    leads = []
    exact_counterexample = None
    for restart in range(int(args.restarts)):
        start_world = _initial_world(rng, m, alphabet)
        x0 = np.asarray([float(start_world[a]) for a in all_actions], dtype=float)
        scale = max(1.0, float(np.max(np.abs(x0))))
        x0 = x0 / scale
        profiles = [_profile_matrix(x0, q, m, alphabet, i) for i in range(m)]
        pivots = [int(np.argmax(np.max(np.abs(profile), axis=0))) for profile in profiles]

        def objective(x: np.ndarray) -> float:
            arr = x.reshape((alphabet,) * m)
            details = evaluate_float(arr, q, m // 2)
            delta = float(details["delta_square"])
            if delta <= 1e-12:
                return 0.0
            return -float(2.0 * details["true_decision_regret"] / delta)

        constraints = {"type": "eq", "fun": lambda x, p=tuple(pivots): _minor_basis(x, q, m, alphabet, p)}
        bounds = [(0.0, 0.0)] + [(-1.0, 1.0)] * (len(x0) - 1)
        opt = minimize(
            objective, x0, method="SLSQP", bounds=bounds, constraints=constraints,
            options={"maxiter": int(args.maxiter), "ftol": float(args.ftol), "disp": False},
        )
        raw_details = evaluate_float(opt.x.reshape((alphabet,) * m), q, m // 2)
        raw_ratio = 0.0 if raw_details["delta_square"] == 0 else float(2.0 * raw_details["true_decision_regret"] / raw_details["delta_square"])
        exact_world = _raw_to_exact(opt.x, m, alphabet, int(args.rational_denominator))
        exact = evaluate_candidate(exact_world, q_rows, m, alphabet)
        lead = {
            "restart": restart, "optimizer_success": bool(opt.success), "optimizer_status": int(opt.status),
            "optimizer_message": str(opt.message), "raw_ratio": raw_ratio,
            "max_minor_abs": float(np.max(np.abs(_minor_basis(opt.x, q, m, alphabet, pivots)))),
            "exact_rank_one_verified": bool(exact["rank_one_verified"]),
            "exact_strict_violation": bool(exact["strict_violation"]),
            "exact": exact,
        }
        leads.append(lead)
        if exact["rank_one_verified"] and exact["strict_violation"]:
            exact_counterexample = {
                "restart": restart, "lead": lead, "q": q_payload(q_rows),
                "world": world_payload(exact_world, all_actions),
            }
            break
    return {
        "protocol_version": PROTOCOL_VERSION, "evidence_class": EVIDENCE_CLASS,
        "development_only": True, "stage": "B3_direct_rank_one", "m": m, "alphabet": alphabet,
        "reference_mode": args.reference_mode, "seed": int(args.seed), "restarts": int(args.restarts),
        "rational_denominator": int(args.rational_denominator), "leads": leads,
        "counterexample": exact_counterexample,
        "status": "KILLED" if exact_counterexample else "NO_EXACT_COUNTEREXAMPLE_FROM_NUMERICAL_LEADS",
        "interpretation": "Only an exact-rational recheck can kill the rank-one law. A failed/non-exact numerical lead is not negative evidence for or against it.",
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--m", type=int, default=4)
    parser.add_argument("--alphabet", type=int, default=3)
    parser.add_argument("--reference-mode", choices=["uniform", "point0", "skew_cycle"], default="point0")
    parser.add_argument("--restarts", type=int, default=4)
    parser.add_argument("--maxiter", type=int, default=80)
    parser.add_argument("--ftol", type=float, default=1e-9)
    parser.add_argument("--rational-denominator", type=int, default=40)
    parser.add_argument("--seed", type=int, default=20260903)
    parser.add_argument("--out", required=True)
    args = parser.parse_args(argv)
    result = run(args)
    write_artifact_with_provenance(
        Path(args.out), result,
        protocol={"protocol_version": PROTOCOL_VERSION, "stage": "B3_direct_rank_one", "m": args.m,
                  "alphabet": args.alphabet, "reference_mode": args.reference_mode,
                  "restarts": args.restarts, "maxiter": args.maxiter, "rational_denominator": args.rational_denominator},
        seed=int(args.seed), evidence_class=EVIDENCE_CLASS, chain="D6",
    )
    print(json.dumps({"status": result["status"], "leads": len(result.get("leads", [])), "out": args.out}, indent=2))
    return 2 if result["status"] == "KILLED" else 0


if __name__ == "__main__":
    raise SystemExit(main())
