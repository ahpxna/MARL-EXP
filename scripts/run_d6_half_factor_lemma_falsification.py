"""Falsification lab for the open D6 half-factor lemma chain.

This script is deliberately independent of the Lean proof.  It tests three
statements on finite product-reference worlds:

  H3-old:
    transfer(S_C) - transfer(T) <= (m-1)*delta_square/2

  H3-prime:
    transfer(S_C) - transfer(T)
      <= surrogate_loss(T) - surrogate_loss(S_C)
         + (m-1)*delta_square/2

  H3-direct:
    true_loss(S_C) - true_loss(T) <= (m-1)*delta_square/2

H3-prime and H3-direct are algebraically identical.  The runner checks that
identity numerically (float mode) and exactly (Fraction mode).

The tool is a falsifier only.  No amount of survival constitutes proof.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

PROTOCOL_VERSION = "d6_half_factor_lemma_falsification_v1"
EVIDENCE_CLASS = "FALSIFICATION_NOT_PROOF"


def _atomic_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    tmp.replace(path)


def _actions(m: int, alphabet: int):
    return tuple(itertools.product(range(alphabet), repeat=m))


def _subsets(m: int, k: int):
    return tuple(itertools.combinations(range(m), k))


def _prod(xs):
    out = xs[0] / xs[0] if xs else 1  # exact 1 for Fraction, numeric 1 otherwise
    for x in xs:
        out *= x
    return out


def _half_range(vals):
    return (max(vals) - min(vals)) / 2


def _validate_q_float(q: Sequence[Sequence[float]], alphabet: int, atol: float = 1e-10):
    arr = np.asarray(q, dtype=float)
    if arr.ndim != 2 or arr.shape[1] != alphabet:
        raise ValueError(f"q must have shape (m,{alphabet}), got {arr.shape}")
    if not np.all(np.isfinite(arr)):
        raise ValueError("q contains non-finite values")
    if np.any(arr < -atol):
        raise ValueError("q contains negative probability")
    sums = arr.sum(axis=1)
    if not np.allclose(sums, 1.0, atol=atol, rtol=0.0):
        raise ValueError(f"q marginals must already be normalized; sums={sums.tolist()}")
    arr = np.maximum(arr, 0.0)
    return arr


def _validate_q_exact(q: Sequence[Sequence[Fraction]], alphabet: int):
    if any(len(row) != alphabet for row in q):
        raise ValueError("wrong q alphabet size")
    for row in q:
        if any(x < 0 for x in row):
            raise ValueError("negative q probability")
        if sum(row, Fraction(0)) != 1:
            raise ValueError(f"exact q marginal is not normalized: {row}")
    return tuple(tuple(x for x in row) for row in q)


def _evaluate_core(values, q):
    """Generic evaluator for float or Fraction scalar types."""
    shape = tuple(len(row) for row in q)
    m = len(shape)
    if len(set(shape)) != 1:
        raise ValueError("all coordinates must share one alphabet size in this lab")
    alphabet = shape[0]
    actions = _actions(m, alphabet)

    # values may be ndarray or nested lists
    def F(a):
        x = values
        for idx in a:
            x = x[idx]
        return x.item() if hasattr(x, "item") else x

    def qweight(a, skip=None):
        factors = [q[j][a[j]] for j in range(m) if j != skip]
        if not factors:
            sample = q[0][0]
            return sample * 0 + 1
        out = factors[0] * 0 + 1
        for z in factors:
            out *= z
        return out

    baseline = sum((F(a) * qweight(a) for a in actions), F(actions[0]) * 0)

    rows = []
    for j in range(m):
        row = []
        for aj in range(alphabet):
            val = sum(
                (F(a) * qweight(a, skip=j) for a in actions if a[j] == aj),
                F(actions[0]) * 0,
            )
            row.append(val)
        rows.append(tuple(row))

    components = [
        tuple(rows[j][aj] - baseline for aj in range(alphabet))
        for j in range(m)
    ]
    surrogate = {
        a: sum((rows[j][a[j]] for j in range(m)), baseline * 0)
           - (m - 1) * baseline
        for a in actions
    }

    score = [max(row) - min(row) for row in rows]

    delta = baseline * 0
    for i in range(m):
        for x in actions:
            for c in actions:
                ci = list(x)
                ci[i] = c[i]
                xc = list(c)
                xc[i] = x[i]
                d = F(x) - F(tuple(ci)) - F(tuple(xc)) + F(c)
                ad = abs(d)
                if ad > delta:
                    delta = ad

    def true_loss(S):
        S = set(S)
        residual = []
        for a in actions:
            kept = sum((components[j][a[j]] for j in S), baseline * 0)
            residual.append(F(a) - kept)
        return _half_range(residual)

    def surrogate_loss(S):
        S = set(S)
        residual = []
        for a in actions:
            kept = sum((components[j][a[j]] for j in S), baseline * 0)
            residual.append(surrogate[a] - kept)
        return _half_range(residual)

    return {
        "m": m,
        "alphabet": alphabet,
        "actions": actions,
        "baseline": baseline,
        "rows": rows,
        "components": components,
        "surrogate": surrogate,
        "score": score,
        "delta_square": delta,
        "true_loss": true_loss,
        "surrogate_loss": surrogate_loss,
    }


def evaluate_float(values, q, k: int):
    arr = np.asarray(values, dtype=float)
    m = arr.ndim
    if len(set(arr.shape)) != 1:
        raise ValueError("values must be a hypercube tensor")
    alphabet = arr.shape[0]
    q = _validate_q_float(q, alphabet)
    if q.shape[0] != m:
        raise ValueError(f"q has {q.shape[0]} coordinates but values has m={m}")
    core = _evaluate_core(arr, q)
    order = sorted(range(m), key=lambda j: (-float(core["score"][j]), j))
    selected = tuple(sorted(order[:k]))
    return _lemma_diagnostics(core, selected, k, exact=False)


def evaluate_exact(values, q, k: int):
    # values must already contain Fraction-compatible scalars
    m = len(q)
    alphabet = len(q[0])
    q = _validate_q_exact(q, alphabet)
    core = _evaluate_core(values, q)
    order = sorted(range(m), key=lambda j: (-core["score"][j], j))
    selected = tuple(sorted(order[:k]))
    return _lemma_diagnostics(core, selected, k, exact=True)


def _lemma_diagnostics(core, selected, k: int, exact: bool):
    m = core["m"]
    delta = core["delta_square"]
    half_rhs = (m - 1) * delta / 2
    approx_rhs = (m - 1) * delta
    true_S = core["true_loss"](selected)
    surr_S = core["surrogate_loss"](selected)
    transfer_S = true_S - surr_S

    rows = []
    for T in _subsets(m, k):
        true_T = core["true_loss"](T)
        surr_T = core["surrogate_loss"](T)
        transfer_T = true_T - surr_T
        slack = surr_T - surr_S
        v_old = transfer_S - transfer_T - half_rhs
        v_prime = transfer_S - transfer_T - slack - half_rhs
        v_direct = true_S - true_T - half_rhs
        identity_gap = v_prime - v_direct
        rows.append({
            "competitor": T,
            "is_nontrivial_competitor": tuple(T) != tuple(selected),
            "true_loss_T": true_T,
            "surrogate_loss_T": surr_T,
            "transfer_T": transfer_T,
            "surrogate_slack": slack,
            "V_old": v_old,
            "V_slack": v_prime,
            "V_direct": v_direct,
            "identity_gap": identity_gap,
        })

    best_true = min(r["true_loss_T"] for r in rows)
    regret = true_S - best_true
    ratio = regret / approx_rhs if approx_rhs != 0 else (regret * 0)

    max_old = max(r["V_old"] for r in rows)
    max_slack = max(r["V_slack"] for r in rows)
    max_direct = max(r["V_direct"] for r in rows)
    nontrivial = [r for r in rows if r["is_nontrivial_competitor"]]
    # k=0 or k=m has no distinct equal-budget competitor.  Those regimes are
    # not useful for directed falsification, so fall back to the full rows only
    # to keep the evaluator total.
    objective_rows = nontrivial or rows
    max_old_nontrivial = max(r["V_old"] for r in objective_rows)
    max_slack_nontrivial = max(r["V_slack"] for r in objective_rows)
    max_direct_nontrivial = max(r["V_direct"] for r in objective_rows)
    max_identity = max(abs(r["identity_gap"]) for r in rows)

    if exact and max_identity != 0:
        raise AssertionError(f"exact H3-prime/direct identity failed: {max_identity}")
    if not exact and float(max_identity) > 1e-10:
        raise AssertionError(f"floating H3-prime/direct identity failed: {max_identity}")

    return {
        "selected": selected,
        "score": core["score"],
        "delta_square": delta,
        "half_rhs": half_rhs,
        "approx_rhs": approx_rhs,
        "true_loss_selected": true_S,
        "surrogate_loss_selected": surr_S,
        "transfer_selected": transfer_S,
        "true_optimum": best_true,
        "true_decision_regret": regret,
        "ratio_regret_over_approx_rhs": ratio,
        "H3_old_max_violation": max_old,
        "H3_slack_max_violation": max_slack,
        "H3_direct_max_violation": max_direct,
        "H3_old_max_violation_nontrivial": max_old_nontrivial,
        "H3_slack_max_violation_nontrivial": max_slack_nontrivial,
        "H3_direct_max_violation_nontrivial": max_direct_nontrivial,
        "H3_prime_direct_identity_max_abs": max_identity,
        "competitors": rows,
    }


def _fraction_payload(x):
    if isinstance(x, Fraction):
        return f"{x.numerator}/{x.denominator}"
    if isinstance(x, tuple):
        return [_fraction_payload(v) for v in x]
    if isinstance(x, list):
        return [_fraction_payload(v) for v in x]
    if isinstance(x, dict):
        return {str(k): _fraction_payload(v) for k, v in x.items()}
    return x


def _q_grid_binary():
    return (
        (Fraction(3, 4), Fraction(1, 4)),
        (Fraction(1, 2), Fraction(1, 2)),
        (Fraction(1, 4), Fraction(3, 4)),
    )


def run_exact(m=2, k_values=(1,), value_radius=2, anchor_zero=True,
              stop_on_counterexample=False):
    if m < 2:
        raise ValueError("m must be >=2")
    alphabet = 2
    n_cells = alphabet ** m
    lattice = tuple(range(-int(value_radius), int(value_radius) + 1))
    q_rows = _q_grid_binary()
    q_vectors = tuple(itertools.product(q_rows, repeat=m))

    if anchor_zero:
        value_iter = (
            (0,) + tail
            for tail in itertools.product(lattice, repeat=n_cells - 1)
        )
        worlds_nominal = len(lattice) ** (n_cells - 1)
    else:
        value_iter = itertools.product(lattice, repeat=n_cells)
        worlds_nominal = len(lattice) ** n_cells

    max_old = None
    max_slack = None
    max_direct = None
    best_ratio = None
    best_old_witness = None
    best_direct_witness = None
    best_ratio_witness = None
    worlds = 0
    pairs = 0
    killed = False

    for flat in value_iter:
        worlds += 1
        # nested hypercube
        # Force the whole exact path into Fraction arithmetic.  Leaving the
        # lattice values as Python ints can make the max mixed difference an
        # int, after which `/ 2` would silently produce a float.
        exact_flat = tuple(Fraction(int(v), 1) for v in flat)
        arr = np.asarray(exact_flat, dtype=object).reshape((2,) * m)
        values = arr.tolist()
        for q in q_vectors:
            for k in k_values:
                d = evaluate_exact(values, q, int(k))
                pairs += 1
                old = d["H3_old_max_violation"]
                slack = d["H3_slack_max_violation"]
                direct = d["H3_direct_max_violation"]
                ratio = d["ratio_regret_over_approx_rhs"]

                witness = {
                    "values": [str(int(v)) for v in flat],
                    "q": q,
                    "k": int(k),
                    "diagnostics": d,
                }
                if max_old is None or old > max_old:
                    max_old, best_old_witness = old, witness
                if max_slack is None or slack > max_slack:
                    max_slack = slack
                if max_direct is None or direct > max_direct:
                    max_direct, best_direct_witness = direct, witness
                if best_ratio is None or ratio > best_ratio:
                    best_ratio, best_ratio_witness = ratio, witness

                if direct > 0:
                    killed = True
                    if stop_on_counterexample:
                        break
            if killed and stop_on_counterexample:
                break
        if killed and stop_on_counterexample:
            break

    payload = {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": "EXHAUSTIVE_FINITE_EXACT_RATIONAL",
        "mode": "exact",
        "m": int(m),
        "alphabet": 2,
        "k_values": [int(k) for k in k_values],
        "value_radius": int(value_radius),
        "anchor_zero": bool(anchor_zero),
        "worlds_nominal": int(worlds_nominal),
        "worlds_enumerated": int(worlds),
        "q_vectors": int(len(q_vectors)),
        "world_q_k_evaluations": int(pairs),
        "H3_old_killed": bool(max_old is not None and max_old > 0),
        "H3_direct_killed": bool(max_direct is not None and max_direct > 0),
        "half_factor_candidate_killed": bool(killed),
        "H3_old_max_violation": max_old or Fraction(0),
        "H3_slack_max_violation": max_slack or Fraction(0),
        "H3_direct_max_violation": max_direct or Fraction(0),
        "best_ratio_regret_over_approx_rhs": best_ratio or Fraction(0),
        "best_H3_old_witness": best_old_witness,
        "best_H3_direct_witness": best_direct_witness,
        "best_ratio_witness": best_ratio_witness,
        "interpretation": (
            "Any exact H3_direct_max_violation > 0 kills the half-factor conjecture. "
            "H3-old may fail while H3-direct survives. Survival is not proof."
        ),
    }
    return _fraction_payload(payload)


def _softmax(logits):
    z = np.asarray(logits, dtype=float)
    z = z - np.max(z, axis=1, keepdims=True)
    e = np.exp(np.clip(z, -60, 60))
    return e / e.sum(axis=1, keepdims=True)


def _initial_logits(rng, m, alphabet, q_mode):
    if q_mode == "uniform":
        return np.zeros((m, alphabet), dtype=float)
    if q_mode == "random":
        return rng.normal(0.0, 1.0, size=(m, alphabet))
    if q_mode == "skewed":
        z = rng.normal(0.0, 0.3, size=(m, alphabet))
        for j in range(m):
            z[j, j % alphabet] += 3.0
        return z
    if q_mode == "boundary":
        z = np.full((m, alphabet), -8.0, dtype=float)
        for j in range(m):
            z[j, j % alphabet] = 8.0
        return z
    raise ValueError(q_mode)


def _objective(d, target):
    if target == "old":
        return float(d["H3_old_max_violation_nontrivial"])
    if target == "direct":
        return float(d["H3_direct_max_violation_nontrivial"])
    if target == "ratio":
        return float(d["ratio_regret_over_approx_rhs"])
    raise ValueError(target)


def run_directed(restarts=2000, steps=300, m=3, alphabet=2, k=1, seed=701,
                 value_clip=8.0, q_mode="random", optimize_q=True,
                 target="direct", temp0=0.5):
    rng = np.random.default_rng(int(seed))
    shape = (int(alphabet),) * int(m)
    best_score = -math.inf
    best = None
    killed = False

    for _restart in range(int(restarts)):
        values = rng.integers(-3, 4, size=shape).astype(float)
        logits = _initial_logits(rng, m, alphabet, q_mode)
        q = _softmax(logits)
        d = evaluate_float(values, q, k)
        score = _objective(d, target)
        temp = float(temp0)

        if score > best_score:
            best_score = score
            best = (values.copy(), logits.copy(), d)

        for _step in range(int(steps)):
            y = values.copy()
            z = logits.copy()

            mutate_q = bool(optimize_q and rng.random() < 0.35)
            if mutate_q:
                j = int(rng.integers(0, m))
                a = int(rng.integers(0, alphabet))
                z[j, a] += float(rng.normal(0.0, 1.0))
                z[j] = np.clip(z[j], -20.0, 20.0)
            else:
                idx = tuple(int(rng.integers(0, alphabet)) for _ in range(m))
                y[idx] = np.clip(
                    y[idx] + rng.choice([-2.0, -1.0, 1.0, 2.0]),
                    -float(value_clip), float(value_clip)
                )

            qy = _softmax(z)
            dy = evaluate_float(y, qy, k)
            sy = _objective(dy, target)
            accept = sy >= score or rng.random() < math.exp(
                (sy - score) / max(temp, 1e-8)
            )
            if accept:
                values, logits, d, score = y, z, dy, sy

            if sy > best_score:
                best_score = sy
                best = (y.copy(), z.copy(), dy)

            if float(dy["H3_direct_max_violation"]) > 1e-10:
                killed = True
                best = (y.copy(), z.copy(), dy)
                best_score = sy
                break
            temp *= 0.985
        if killed:
            break

    values, logits, d = best
    q = _softmax(logits)
    return {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": EVIDENCE_CLASS,
        "mode": "directed",
        "target": target,
        "restarts_requested": int(restarts),
        "steps_per_restart": int(steps),
        "seed": int(seed),
        "m": int(m),
        "alphabet": int(alphabet),
        "k": int(k),
        "q_mode": q_mode,
        "optimize_q": bool(optimize_q),
        "half_factor_candidate_killed": bool(
            float(d["H3_direct_max_violation"]) > 1e-10
        ),
        "H3_old_killed": bool(float(d["H3_old_max_violation"]) > 1e-10),
        "best_objective": float(best_score),
        "best_witness": {
            "values": values.tolist(),
            "reference_q": q.tolist(),
            "diagnostics": _json_float(d),
        },
    }


def _json_float(x):
    if isinstance(x, np.generic):
        return x.item()
    if isinstance(x, tuple):
        return [_json_float(v) for v in x]
    if isinstance(x, list):
        return [_json_float(v) for v in x]
    if isinstance(x, dict):
        return {str(k): _json_float(v) for k, v in x.items()}
    if isinstance(x, (float, int, str, bool)) or x is None:
        return x
    return float(x)


def _parse_reference_q(raw, m, alphabet):
    if raw is None:
        return np.full((m, alphabet), 1.0 / alphabet, dtype=float)
    if isinstance(raw, dict):
        rows = []
        for j in range(m):
            row = raw.get(str(j), raw.get(j))
            if row is None:
                raise ValueError(f"reference_q missing coordinate {j}")
            rows.append(row)
        return np.asarray(rows, dtype=float)
    return np.asarray(raw, dtype=float)


def audit_json(path: Path):
    payload = json.loads(path.read_text(encoding="utf-8"))
    witness = payload.get("best_witness", payload)
    values = np.asarray(witness["values"], dtype=float)
    m = values.ndim
    alphabet = values.shape[0]
    k = int(witness.get("k", payload.get("k", 1)))
    q = _parse_reference_q(witness.get("reference_q"), m, alphabet)
    d = evaluate_float(values, q, k)
    return {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": "AUDIT_OF_EXISTING_DIRECTED_WITNESS",
        "mode": "audit-json",
        "source": str(path),
        "source_protocol_version": payload.get("protocol_version"),
        "m": int(m),
        "alphabet": int(alphabet),
        "k": int(k),
        "reference_q": q.tolist(),
        "diagnostics": _json_float(d),
        "H3_old_killed": bool(float(d["H3_old_max_violation"]) > 1e-10),
        "half_factor_candidate_killed": bool(
            float(d["H3_direct_max_violation"]) > 1e-10
        ),
    }


def main(argv=None):
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="mode", required=True)

    e = sub.add_parser("exact")
    e.add_argument("--m", type=int, default=2)
    e.add_argument("--k-values", type=int, nargs="+", default=[1])
    e.add_argument("--value-radius", type=int, default=2)
    e.add_argument("--no-anchor-zero", action="store_true")
    e.add_argument("--stop-on-counterexample", action="store_true")
    e.add_argument("--out", required=True)

    d = sub.add_parser("directed")
    d.add_argument("--restarts", type=int, default=2000)
    d.add_argument("--steps", type=int, default=300)
    d.add_argument("--m", type=int, default=3)
    d.add_argument("--alphabet", type=int, default=2)
    d.add_argument("--k", type=int, default=1)
    d.add_argument("--seed", type=int, default=701)
    d.add_argument("--value-clip", type=float, default=8.0)
    d.add_argument("--q-mode", choices=["uniform","random","skewed","boundary"],
                   default="random")
    d.add_argument("--no-optimize-q", action="store_true")
    d.add_argument("--target", choices=["old","direct","ratio"], default="direct")
    d.add_argument("--out", required=True)

    a = sub.add_parser("audit-json")
    a.add_argument("inputs", nargs="+")
    a.add_argument("--out", required=True)

    args = p.parse_args(argv)

    if args.mode == "exact":
        out = run_exact(
            m=args.m,
            k_values=tuple(args.k_values),
            value_radius=args.value_radius,
            anchor_zero=not args.no_anchor_zero,
            stop_on_counterexample=args.stop_on_counterexample,
        )
    elif args.mode == "directed":
        out = run_directed(
            restarts=args.restarts,
            steps=args.steps,
            m=args.m,
            alphabet=args.alphabet,
            k=args.k,
            seed=args.seed,
            value_clip=args.value_clip,
            q_mode=args.q_mode,
            optimize_q=not args.no_optimize_q,
            target=args.target,
        )
    else:
        rows = [audit_json(Path(x)) for x in args.inputs]
        out = {
            "protocol_version": PROTOCOL_VERSION,
            "evidence_class": "AUDIT_OF_EXISTING_DIRECTED_WITNESSES",
            "rows": rows,
            "any_H3_old_killed": any(x["H3_old_killed"] for x in rows),
            "any_half_factor_candidate_killed": any(
                x["half_factor_candidate_killed"] for x in rows
            ),
        }

    _atomic_json(Path(args.out), out)
    print(json.dumps(out, indent=2, sort_keys=True))
    if out.get("half_factor_candidate_killed") or out.get(
        "any_half_factor_candidate_killed"
    ):
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
