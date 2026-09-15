#!/usr/bin/env python3
"""Annotate recorded D6 counterexample worlds with WITNESS-FREE misalignment columns.

Motivation
----------
D6 was stated under `AllCoordinatesInteractionContrastRankOne`, i.e. rank one of
the *centred* interaction contrast.  Centring is a projection that discards the
additive layer, and every recorded counterexample appears to live exactly in the
discarded layer.  The invariant that does NOT discard it is rank one of the RAW
local contrast

    rho_{i,u}(z) = F(z[i<-u]) - F(z[i<-u0]).

`RawLocalContrastRankOne` holds at coordinate i iff the (action x context)
matrix of raw contrasts has rank <= 1.  That test needs no factorisation
witness, no anchor choice and no reference measure, which is why it is used here
instead of the determinant  mu_i(u,v) = alpha_i(u) lambda_i(v) - alpha_i(v) lambda_i(u).
mu is only equivalent to raw rank one when the context factor h_i is
non-constant; the rank test is unconditional.  mu is still reported, together
with an explicit degeneracy flag, so the two can be compared.

This script is append-only with respect to the ledger: it never edits an
existing artifact, it writes one new summary artifact.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import glob
import hashlib
import itertools
import json
import os
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

Action = Tuple[int, ...]
World = Dict[Action, Fraction]

PROTOCOL_VERSION = "d6_misalignment_annotation_v1"


# --------------------------------------------------------------------------- #
# exact linear algebra
# --------------------------------------------------------------------------- #
def exact_rank(rows: Sequence[Sequence[Fraction]]) -> int:
    """Rank over Q by Gaussian elimination.  Rows are short (K), so this is cheap."""
    work = [list(r) for r in rows]
    n_rows = len(work)
    n_cols = len(work[0]) if work else 0
    rank = 0
    col = 0
    while rank < n_rows and col < n_cols:
        pivot = None
        for r in range(rank, n_rows):
            if work[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            col += 1
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        pv = work[rank][col]
        for r in range(rank + 1, n_rows):
            if work[r][col] != 0:
                factor = work[r][col] / pv
                row_r = work[r]
                row_p = work[rank]
                for c in range(col, n_cols):
                    row_r[c] -= factor * row_p[c]
        rank += 1
        col += 1
    return rank


def max_abs_minor_relative(rows: Sequence[Sequence[Fraction]]) -> float:
    """Largest |2x2 minor|, normalised by the squared max entry.

    Float, and labelled as such: it is a magnitude diagnostic only.  The
    rank returned by `exact_rank` is the exact, load-bearing quantity.
    """
    if len(rows) < 2:
        return 0.0
    scale = max((abs(v) for row in rows for v in row), default=Fraction(0))
    if scale == 0:
        return 0.0
    fl = [[float(v / scale) for v in row] for row in rows]
    n_cols = len(fl[0])
    best = 0.0
    for a in range(len(fl)):
        for b in range(a + 1, len(fl)):
            ra, rb = fl[a], fl[b]
            for x in range(n_cols):
                rax, rbx = ra[x], rb[x]
                for y in range(x + 1, n_cols):
                    d = abs(rax * rb[y] - ra[y] * rbx)
                    if d > best:
                        best = d
    return best


# --------------------------------------------------------------------------- #
# world / reference semantics (definitions only, no repo evaluator)
# --------------------------------------------------------------------------- #
def load_world(payload: Sequence[dict]) -> World:
    return {tuple(e["action"]): Fraction(e["value"]) for e in payload}


def load_q(payload: Sequence[Sequence[str]]) -> List[List[Fraction]]:
    return [[Fraction(v) for v in row] for row in payload]


def joint_weight(q: List[List[Fraction]], c: Action) -> Fraction:
    w = Fraction(1)
    for j, cj in enumerate(c):
        w *= q[j][cj]
        if w == 0:
            return Fraction(0)
    return w


def product_response(world: World, q: List[List[Fraction]], i: int, u: int) -> Fraction:
    """Q_i(u) = E_{c~q} F(c[i<-u]).  Terms of zero weight are skipped."""
    total = Fraction(0)
    for c, _ in world.items():
        w = joint_weight(q, c)
        if w == 0:
            continue
        cc = list(c)
        cc[i] = u
        total += w * world[tuple(cc)]
    return total


def contexts_for(m: int, K: int, i: int):
    """Canonical context representatives: coordinate i pinned to 0 (it is overwritten)."""
    for rest in itertools.product(range(K), repeat=m - 1):
        z = list(rest[:i]) + [0] + list(rest[i:])
        yield tuple(z)


def raw_contrast_matrix(world: World, m: int, K: int, i: int, u0: int = 0
                        ) -> List[List[Fraction]]:
    """rows indexed by action u, columns by context; entry rho_{i,u}(z)."""
    ctxs = list(contexts_for(m, K, i))
    rows: List[List[Fraction]] = []
    for u in range(K):
        row = []
        for z in ctxs:
            zu = list(z); zu[i] = u
            z0 = list(z); z0[i] = u0
            row.append(world[tuple(zu)] - world[tuple(z0)])
        rows.append(row)
    return rows


def centred_profile_matrix(raw_rows: List[List[Fraction]],
                           alpha: List[Fraction]) -> List[List[Fraction]]:
    return [[v - alpha[u] for v in row] for u, row in enumerate(raw_rows)]



# --------------------------------------------------------------------------- #
# exact mirror of the search script's FloatModel.evaluate / .ratio
# --------------------------------------------------------------------------- #
def exact_evaluate(world: World, q: List[List[Fraction]], m: int, K: int) -> dict:
    """Exact rational recomputation of the decision layer.

    Mirrors FloatModel.evaluate/.ratio in
    scripts/run_d6_direct_rankone_linear_fiber_search.py, in Fraction
    arithmetic.  Recomputed PER WITNESS: the artifacts record one
    artifact-level best ratio, which must not be attributed to the other
    witness slots stored beside it.
    """
    k = m // 2
    ctxs = [list(contexts_for(m, K, i)) for i in range(m)]

    weight = []
    for i in range(m):
        wi = []
        for z in ctxs[i]:
            w = Fraction(1)
            for j in range(m):
                if j != i:
                    w *= q[j][z[j]]
                    if w == 0:
                        break
            wi.append(w)
        weight.append(wi)

    sl = []
    for i in range(m):
        rows = []
        for u in range(K):
            row = []
            for z in ctxs[i]:
                zz = list(z); zz[i] = u
                row.append(world[tuple(zz)])
            rows.append(row)
        sl.append(rows)

    R = [[sum((weight[i][c] * sl[i][u][c] for c in range(len(ctxs[i]))), Fraction(0))
          for u in range(K)] for i in range(m)]
    baseline = sum((R[0][u] * q[0][u] for u in range(K)), Fraction(0))
    comp = [[R[i][u] - baseline for u in range(K)] for i in range(m)]
    score = [max(R[i]) - min(R[i]) for i in range(m)]

    delta = Fraction(0)
    for i in range(m):
        ncol = len(ctxs[i])
        for u in range(K):
            for v in range(u + 1, K):
                diffs = [sl[i][u][c] - sl[i][v][c] for c in range(ncol)]
                osc = max(diffs) - min(diffs)
                if osc > delta:
                    delta = osc

    actions = sorted(world.keys())
    losses = {}
    for S in itertools.combinations(range(m), k):
        vals = [world[x] - sum((comp[i][x[i]] for i in S), Fraction(0)) for x in actions]
        losses[S] = (max(vals) - min(vals)) / 2

    order = sorted(range(m), key=lambda i: (-score[i], i))
    selected = tuple(sorted(order[:k]))
    sel = set(selected)
    optimum = min(losses.values())
    regret = losses[selected] - optimum
    margin = (min(score[i] for i in range(m) if i in sel)
              - max(score[i] for i in range(m) if i not in sel))

    ratio = None if delta == 0 else 2 * regret / ((m - 1) * delta)
    return {
        "source": "recomputed_exact_per_witness",
        "delta_square": str(delta),
        "response_spans": [str(s) for s in score],
        "selected": list(selected),
        "topc_margin": str(margin),
        "topc_margin_relative_float": (float(margin / delta) if delta != 0 else None),
        "strict_topc": bool(margin > 0),
        "loss_selected": str(losses[selected]),
        "loss_optimum": str(optimum),
        "doubled_decision_gap": str(2 * regret),
        "m_minus_one_delta": str((m - 1) * delta),
        "ratio": (str(ratio) if ratio is not None else None),
        "ratio_float": (float(ratio) if ratio is not None else None),
        "violates": (ratio is not None and ratio > 1),
        "excess_over_delta_float": (float((2 * regret - (m - 1) * delta) / delta)
                                    if delta != 0 else None),
    }


# --------------------------------------------------------------------------- #
# per-witness analysis
# --------------------------------------------------------------------------- #
def analyse_witness(world_payload, q_payload) -> dict:
    world = load_world(world_payload)
    q = load_q(q_payload)
    any_action = next(iter(world))
    m = len(any_action)
    K = max(max(a) for a in world) + 1
    if len(world) != K ** m:
        return {"error": f"world has {len(world)} entries, expected {K**m}"}

    per_coord = []
    for i in range(m):
        raw_rows = raw_contrast_matrix(world, m, K, i)
        raw_rank = exact_rank(raw_rows)

        alpha = [product_response(world, q, i, u) - product_response(world, q, i, 0)
                 for u in range(K)]
        cen_rows = centred_profile_matrix(raw_rows, alpha)
        cen_rank = exact_rank(cen_rows)

        # h_i is constant (as a function of context) exactly when the centred
        # matrix vanishes.  That is the degeneracy on which mu is uninformative.
        h_degenerate = (cen_rank == 0)

        # lambda from the centred factorisation, when one exists (cen_rank <= 1):
        # pick the context column with the largest entry as the scale.
        lam: Optional[List[str]] = None
        mu_max: Optional[str] = None
        if cen_rank <= 1 and not h_degenerate:
            best_col, best_val = 0, Fraction(0)
            for col in range(len(cen_rows[0])):
                v = max(abs(cen_rows[u][col]) for u in range(K))
                if v > best_val:
                    best_val, best_col = v, col
            lam_f = [cen_rows[u][best_col] for u in range(K)]
            mu = max((abs(alpha[u] * lam_f[v] - alpha[v] * lam_f[u])
                      for u in range(K) for v in range(u + 1, K)),
                     default=Fraction(0))
            lam = [str(x) for x in lam_f]
            mu_max = str(mu)

        per_coord.append({
            "coordinate": i,
            "raw_contrast_rank": raw_rank,
            "raw_rank_one": raw_rank <= 1,
            "centred_profile_rank": cen_rank,
            "centred_rank_one": cen_rank <= 1,
            "context_factor_degenerate": h_degenerate,
            "alpha": [str(a) for a in alpha],
            "lambda_at_scale_column": lam,
            "mu_max_abs": mu_max,
            "mu_informative": (lam is not None),
            "raw_max_minor_relative_float": max_abs_minor_relative(raw_rows),
        })

    n_mis = sum(1 for c in per_coord if not c["raw_rank_one"])
    n_cen_violating = sum(1 for c in per_coord if not c["centred_rank_one"])
    n_degen = sum(1 for c in per_coord if c["context_factor_degenerate"])
    sum_mu = sum(Fraction(c["mu_max_abs"]) for c in per_coord
                 if c["mu_max_abs"] is not None)

    return {
        "m": m,
        "alphabet": K,
        "decision": exact_evaluate(world, q, m, K),
        "n_misaligned": n_mis,
        "misaligned_coordinates": [c["coordinate"] for c in per_coord
                                   if not c["raw_rank_one"]],
        "n_centred_rank_violating": n_cen_violating,
        "n_context_factor_degenerate": n_degen,
        "sum_mu_max_abs": str(sum_mu),
        "sum_mu_max_abs_float": float(sum_mu),
        "per_coordinate": per_coord,
    }


# --------------------------------------------------------------------------- #
# artifact traversal
# --------------------------------------------------------------------------- #
WITNESS_KEYS = ("counterexample", "strict_top_c_witness", "tightness_witness")


def sha256_of(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def recorded_decision_quantities(doc: dict) -> dict:
    """Read delta_square / 2D / ratio if the artifact recorded them.

    These are NOT recomputed here; the field `source` says so.  Recomputing the
    decision layer needs the loss and Top-C machinery and is the job of the
    independent-recheck scripts, which already ran on the flagship witnesses.
    """
    out: dict = {"source": "artifact_recorded"}
    ev = doc.get("exact_values")
    if isinstance(ev, dict):
        for k in ("delta_square", "m_minus_one_delta", "doubled_decision_gap",
                  "selected_loss", "optimal_loss", "ratio", "topc_margin",
                  "strict_violation"):
            if k in ev:
                out[k] = ev[k]
    for k in ("best_exact_ratio", "best_strict_top_c_exact_ratio",
              "best_float_ratio", "best_exact_ratio_float"):
        if k in doc:
            out[k] = doc[k]
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="research/d6_contrast_rank_falsification")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    files = sorted(p for p in glob.glob(os.path.join(args.root, "*.json"))
                   if not p.endswith(".manifest.json"))

    records = []
    for path in files:
        try:
            doc = json.load(open(path))
        except Exception as exc:  # noqa: BLE001
            records.append({"artifact": os.path.basename(path),
                            "error": f"unreadable: {exc}"})
            continue
        if not isinstance(doc, dict):
            continue

        found = []
        if isinstance(doc.get("world"), list) and isinstance(doc.get("q"), list):
            found.append(("<root>", doc))
        for key in WITNESS_KEYS:
            sub = doc.get(key)
            if isinstance(sub, dict) and isinstance(sub.get("world"), list):
                found.append((key, sub))
        if not found:
            continue

        rec_dec = recorded_decision_quantities(doc)
        for slot, sub in found:
            analysis = analyse_witness(sub["world"], sub["q"])
            records.append({
                "artifact": os.path.basename(path),
                "artifact_sha256": sha256_of(path),
                "witness_slot": slot,
                "recorded_decision_quantities": rec_dec,
                **analysis,
            })

    out_path = args.out or os.path.join(
        args.root,
        f"MISALIGNMENT_ANNOTATION_{_dt.datetime.now().strftime('%Y%m%d')}.json")
    payload = {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": "EXACT_RATIONAL_DERIVED_ANNOTATION",
        "development_only": True,
        "generated_utc": _dt.datetime.now(_dt.timezone.utc).isoformat(),
        "what_this_is": (
            "Per-coordinate rank of the RAW local contrast matrix for every "
            "recorded D6 counterexample world.  n_misaligned counts the "
            "coordinates where raw rank one FAILS while centred rank one may "
            "still hold; those are exactly the coordinates that the centred "
            "invariant cannot see."),
        "what_this_is_not": (
            "Not a recomputation of the decision layer.  delta_square and the "
            "doubled decision gap are read from the annotated artifacts and are "
            "labelled source=artifact_recorded."),
        "mu_caveat": (
            "mu_i is reported only where the centred profile is nonzero.  Where "
            "the context factor is constant, lambda is not determined by F and "
            "mu carries no information; those coordinates are flagged "
            "context_factor_degenerate and excluded from sum_mu_max_abs."),
        "records": records,
    }
    with open(out_path, "w") as fh:
        json.dump(payload, fh, indent=2)
    print(json.dumps({"out": out_path, "records": len(records)}, indent=2))


if __name__ == "__main__":
    main()
