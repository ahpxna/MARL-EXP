"""Exact-rational falsifier for the D6 interaction-contrast-rank hypothesis.

This is deliberately a falsifier, never a proof engine.  It evaluates the
same finite product-response, mixed-difference, Top-C, and compression-loss
semantics used by the D6 Python labs, using :class:`fractions.Fraction`.

The model stages are deliberately nested only as *search families*:

* ``B1_pairwise``: additive terms plus ``w_ij phi_i phi_j``;
* ``B_product``: additive terms plus one full product term;
* ``B2_multiaffine``: additive terms plus all higher-order feature products.

Every candidate is independently checked to have rank-one centred local
interaction profiles at every coordinate.  A strict witness satisfying
``2D > (m - 1) delta_square`` kills the proposed rank-one ``m-1`` law within
the searched family.  Survival is explicitly not a proof.

``B3_direct_rank_one`` is intentionally fail-closed: it is not represented by
one of the factor models above, so this runner refuses to call it tested.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import random
import sys
from typing import Callable, Iterable, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from research_chains.provenance import write_artifact_with_provenance


PROTOCOL_VERSION = "d6_interaction_contrast_rank_falsification_v1"
EVIDENCE_CLASS = "EXACT_RATIONAL_FALSIFICATION_NOT_PROOF"
Stage = str
Action = tuple[int, ...]
World = dict[Action, Fraction]


def actions(m: int, alphabet: int) -> tuple[Action, ...]:
    return tuple(itertools.product(range(alphabet), repeat=m))


def subsets_of_size(m: int, k: int) -> tuple[tuple[int, ...], ...]:
    return tuple(itertools.combinations(range(m), k))


def product(xs: Iterable[Fraction]) -> Fraction:
    out = Fraction(1)
    for value in xs:
        out *= value
    return out


def replace(a: Action, i: int, u: int) -> Action:
    return a[:i] + (int(u),) + a[i + 1 :]


def contexts(m: int, alphabet: int, i: int) -> tuple[Action, ...]:
    """Full tuples whose i-th coordinate is the anchor 0."""
    return tuple(a for a in actions(m, alphabet) if a[i] == 0)


def reference_rows(m: int, alphabet: int, mode: str) -> tuple[tuple[Fraction, ...], ...]:
    if mode == "uniform":
        row = tuple(Fraction(1, alphabet) for _ in range(alphabet))
        return (row,) * m
    if mode == "point0":
        row = (Fraction(1),) + (Fraction(0),) * (alphabet - 1)
        return (row,) * m
    if mode == "skew_cycle":
        # A fixed interior rational product reference with different marginals.
        if alphabet != 3:
            raise ValueError("skew_cycle is defined for K=3 only")
        base = (
            (Fraction(1, 2), Fraction(1, 3), Fraction(1, 6)),
            (Fraction(1, 6), Fraction(1, 2), Fraction(1, 3)),
            (Fraction(1, 3), Fraction(1, 6), Fraction(1, 2)),
        )
        return tuple(base[i % len(base)] for i in range(m))
    raise ValueError(f"unknown reference mode: {mode}")


def joint_weight(q: Sequence[Sequence[Fraction]], a: Action) -> Fraction:
    return product(q[i][a[i]] for i in range(len(q)))


def response_table(world: World, q: Sequence[Sequence[Fraction]], all_actions: Sequence[Action]) -> tuple[tuple[Fraction, ...], ...]:
    m = len(q)
    alphabet = len(q[0])
    table: list[tuple[Fraction, ...]] = []
    for i in range(m):
        row = []
        for u in range(alphabet):
            total = Fraction(0)
            for z in contexts(m, alphabet, i):
                total += world[replace(z, i, u)] * product(q[j][z[j]] for j in range(m) if j != i)
            row.append(total)
        table.append(tuple(row))
    return tuple(table)


def delta_square(world: World, m: int, alphabet: int) -> Fraction:
    """Exact D6 mixed-difference maximum, optimized through contrast ranges."""
    out = Fraction(0)
    for i in range(m):
        ctx = contexts(m, alphabet, i)
        for u in range(alphabet):
            for v in range(alphabet):
                vals = [world[replace(z, i, u)] - world[replace(z, i, v)] for z in ctx]
                out = max(out, max(vals) - min(vals))
    return out


def all_equal_budget_losses(world: World, response: Sequence[Sequence[Fraction]], q: Sequence[Sequence[Fraction]], all_actions: Sequence[Action], k: int) -> dict[tuple[int, ...], Fraction]:
    """Compute every size-k loss while forming product components only once."""
    baseline = sum((world[a] * joint_weight(q, a) for a in all_actions), Fraction(0))
    components = tuple(tuple(response[i][u] - baseline for u in range(len(response[i]))) for i in range(len(response)))
    families = subsets_of_size(len(response), k)
    minima = {S: None for S in families}
    maxima = {S: None for S in families}
    for a in all_actions:
        # This retains exact Fraction semantics, but avoids recomputing the
        # reference baseline and individual coordinate components per subset.
        local = tuple(components[i][a[i]] for i in range(len(response)))
        for S in families:
            residual = world[a] - sum((local[i] for i in S), Fraction(0))
            old_min, old_max = minima[S], maxima[S]
            minima[S] = residual if old_min is None or residual < old_min else old_min
            maxima[S] = residual if old_max is None or residual > old_max else old_max
    return {S: (maxima[S] - minima[S]) / 2 for S in families}


def interaction_profile(world: World, response: Sequence[Sequence[Fraction]], i: int, u: int, z: Action) -> Fraction:
    """psi_{i,u} at anchor action 0; z[i] is intentionally ignored."""
    return (world[replace(z, i, u)] - world[replace(z, i, 0)]) - (response[i][u] - response[i][0])


def rank_one_check(world: World, response: Sequence[Sequence[Fraction]], m: int, alphabet: int) -> tuple[bool, dict | None]:
    """Verify all 2-by-2 profile minors exactly for every coordinate.

    A literal pair-of-context loop is quadratic in ``K^(m-1)``.  The pivot
    calculation below is its exact equivalent: a finite profile matrix has
    rank at most one iff every row is proportional to one nonzero pivot row
    (or all rows are zero).  It is therefore still an all-minor check, but
    avoids repeating the same determinant identities thousands of times.
    """
    for i in range(m):
        ctx = contexts(m, alphabet, i)
        profiles = {
            u: tuple(interaction_profile(world, response, i, u, z) for z in ctx)
            for u in range(1, alphabet)
        }
        pivot: tuple[int, int] | None = None
        for u, row in profiles.items():
            for position, value in enumerate(row):
                if value != 0:
                    pivot = (u, position)
                    break
            if pivot is not None:
                break
        if pivot is None:
            continue
        pivot_u, pivot_position = pivot
        pivot_row = profiles[pivot_u]
        pivot_value = pivot_row[pivot_position]
        for u, row in profiles.items():
            for position, value in enumerate(row):
                determinant = value * pivot_value - row[pivot_position] * pivot_row[position]
                if determinant != 0:
                    return False, {
                        "coordinate": i, "actions": [u, pivot_u],
                        "contexts": [list(ctx[position]), list(ctx[pivot_position])],
                        "minor": fraction_text(determinant),
                    }
    return True, None


def feature_values(alphabet: int) -> tuple[Fraction, ...]:
    if alphabet != 3:
        raise ValueError("current falsification protocol starts with K=3")
    return (Fraction(-1), Fraction(0), Fraction(1))


def make_world(stage: Stage, m: int, alphabet: int, rng: random.Random, coefficient_radius: int, density: Fraction) -> tuple[World, dict]:
    phi = feature_values(alphabet)
    additive = tuple(tuple(Fraction(rng.randint(-coefficient_radius, coefficient_radius)) for _ in range(alphabet)) for _ in range(m))
    higher: dict[tuple[int, ...], Fraction] = {}
    if stage == "B1_pairwise":
        for ij in itertools.combinations(range(m), 2):
            higher[ij] = Fraction(rng.randint(-coefficient_radius, coefficient_radius))
    elif stage == "B_product":
        higher[tuple(range(m))] = Fraction(rng.randint(-coefficient_radius, coefficient_radius))
    elif stage == "B2_multiaffine":
        for size in range(2, m + 1):
            for term in itertools.combinations(range(m), size):
                if Fraction(rng.randrange(density.denominator), density.denominator) < density:
                    higher[term] = Fraction(rng.randint(-coefficient_radius, coefficient_radius))
    else:
        raise ValueError(f"factor generator does not support {stage}")
    out: World = {}
    for a in actions(m, alphabet):
        value = sum((additive[i][a[i]] for i in range(m)), Fraction(0))
        for term, coeff in higher.items():
            value += coeff * product(phi[a[i]] for i in term)
        out[a] = value
    return out, {
        "additive": [[fraction_text(v) for v in row] for row in additive],
        "higher_order": {"/".join(map(str, term)): fraction_text(coeff) for term, coeff in higher.items()},
        "feature": [fraction_text(v) for v in phi],
    }


def fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def world_payload(world: World, all_actions: Sequence[Action]) -> list[dict]:
    return [{"action": list(a), "value": fraction_text(world[a])} for a in all_actions]


def q_payload(q: Sequence[Sequence[Fraction]]) -> list[list[str]]:
    return [[fraction_text(value) for value in row] for row in q]


def evaluate_candidate(world: World, q: Sequence[Sequence[Fraction]], m: int, alphabet: int) -> dict:
    all_actions = actions(m, alphabet)
    response = response_table(world, q, all_actions)
    scores = tuple(max(row) - min(row) for row in response)
    k = m // 2
    selected = tuple(sorted(sorted(range(m), key=lambda i: (-scores[i], i))[:k]))
    all_losses = all_equal_budget_losses(world, response, q, all_actions, k)
    selected_loss = all_losses[selected]
    optimum = min(all_losses.values())
    best_competitors = [S for S, value in all_losses.items() if value == optimum]
    delta = delta_square(world, m, alphabet)
    doubled_gap = 2 * (selected_loss - optimum)
    bound = (m - 1) * delta
    rank_one, minor = rank_one_check(world, response, m, alphabet)
    return {
        "rank_one_verified": rank_one,
        "rank_one_failure": minor,
        "scores": [fraction_text(x) for x in scores],
        "selected": list(selected),
        "selected_loss": fraction_text(selected_loss),
        "optimal_loss": fraction_text(optimum),
        "best_competitors": [list(S) for S in best_competitors],
        "delta_square": fraction_text(delta),
        "doubled_decision_gap": fraction_text(doubled_gap),
        "m_minus_one_delta": fraction_text(bound),
        "strict_violation": doubled_gap > bound,
    }


def run_stage(args: argparse.Namespace) -> dict:
    stage = str(args.stage)
    if stage == "B3_direct_rank_one":
        return {
            "protocol_version": PROTOCOL_VERSION,
            "status": "BLOCKED_NOT_RUN",
            "stage": stage,
            "reason": "Direct rank-one search needs a separate integrability-preserving constrained solver; factor families cannot certify it.",
        }
    if stage not in {"B1_pairwise", "B_product", "B2_multiaffine"}:
        raise ValueError(f"unknown stage: {stage}")
    if int(args.alphabet) != 3:
        raise ValueError("this protocol is pre-registered for K=3")
    rng = random.Random(int(args.seed))
    m_values = tuple(int(m) for m in args.m_values)
    q_modes = tuple(args.reference_modes)
    rows: list[dict] = []
    kill: dict | None = None
    for m in m_values:
        if m % 2:
            raise ValueError("balanced Top-C test needs even m")
        for trial in range(int(args.trials)):
            world, model = make_world(stage, m, int(args.alphabet), rng, int(args.coefficient_radius), Fraction(str(args.density)))
            for q_mode in q_modes:
                q = reference_rows(m, int(args.alphabet), q_mode)
                result = evaluate_candidate(world, q, m, int(args.alphabet))
                # The declared model should be a rank-one subclass; fail closed if
                # a coding/semantic mismatch makes that statement false.
                if not result["rank_one_verified"]:
                    kill = {
                        "kind": "MODEL_CLASS_SEMANTICS_FAILURE", "m": m, "trial": trial,
                        "reference_mode": q_mode, "model": model, "result": result,
                        "world": world_payload(world, actions(m, int(args.alphabet))), "q": q_payload(q),
                    }
                    break
                if result["strict_violation"]:
                    kill = {
                        "kind": "EXACT_RANK_ONE_COUNTEREXAMPLE", "m": m, "trial": trial,
                        "reference_mode": q_mode, "model": model, "result": result,
                        "world": world_payload(world, actions(m, int(args.alphabet))), "q": q_payload(q),
                    }
                    break
                rows.append({"m": m, "trial": trial, "reference_mode": q_mode, **result})
            if kill is not None:
                break
        if kill is not None:
            break
    return {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": EVIDENCE_CLASS,
        "development_only": True,
        "stage": stage,
        "alphabet": int(args.alphabet),
        "m_values_requested": list(m_values),
        "m_values_completed": sorted(set(row["m"] for row in rows)),
        "reference_modes": list(q_modes),
        "seed": int(args.seed),
        "trials_per_dimension": int(args.trials),
        "coefficient_radius": int(args.coefficient_radius),
        "multiaffine_density": str(args.density),
        "evaluations_completed": len(rows),
        "counterexample": kill,
        "status": "KILLED" if kill and kill["kind"] == "EXACT_RANK_ONE_COUNTEREXAMPLE" else ("INVALID_MODEL_SEMANTICS" if kill else "SURVIVED_SEARCH_NOT_PROVED"),
        "interpretation": (
            "An exact witness kills the rank-one m-1 hypothesis within this searched family. "
            "A surviving finite search is not a theorem and must not trigger a Lean universal proof."
        ),
        "rows": rows,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=["B1_pairwise", "B_product", "B2_multiaffine", "B3_direct_rank_one"], required=True)
    parser.add_argument("--m-values", nargs="+", type=int, default=[4])
    parser.add_argument("--alphabet", type=int, default=3)
    parser.add_argument("--trials", type=int, default=100)
    parser.add_argument("--coefficient-radius", type=int, default=3)
    parser.add_argument("--density", default="1/2", help="B2 coefficient inclusion probability, e.g. 1/2")
    parser.add_argument("--reference-modes", nargs="+", default=["uniform", "point0", "skew_cycle"])
    parser.add_argument("--seed", type=int, default=20260903)
    parser.add_argument("--out", required=True)
    args = parser.parse_args(argv)
    result = run_stage(args)
    write_artifact_with_provenance(
        Path(args.out), result,
        protocol={
            "protocol_version": PROTOCOL_VERSION, "stage": args.stage,
            "m_values": list(map(int, args.m_values)), "alphabet": int(args.alphabet),
            "trials": int(args.trials), "coefficient_radius": int(args.coefficient_radius),
            "density": str(args.density), "reference_modes": list(args.reference_modes),
        },
        seed=int(args.seed), evidence_class=EVIDENCE_CLASS, chain="D6",
    )
    print(json.dumps({
        "status": result["status"], "stage": result["stage"],
        "evaluations_completed": result.get("evaluations_completed", 0),
        "counterexample_kind": None if result.get("counterexample") is None else result["counterexample"]["kind"],
        "out": args.out,
    }, indent=2))
    return 2 if result["status"] == "KILLED" else 0


if __name__ == "__main__":
    raise SystemExit(main())
