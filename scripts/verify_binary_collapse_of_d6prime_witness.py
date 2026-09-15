#!/usr/bin/env python3
"""The D6-prime witness is a BINARY world, so what it refutes is unconditional.

The seed-5 / denominator-64 counterexample was found in the raw-rank-one fibre at
lambda_i = (0,1,0), i.e. phi_i(a_i) = [a_i = 1].  Every basis column of that
fibre depends on the action only through the binary key a -> ([a_i = 1])_i, so
every world in the fibre does too.  The witness therefore takes 2^m distinct
values, not K^m, and symbol 2 is an exact duplicate of symbol 0.

Restricting it to {0,1}^m reproduces delta_square, the Top-C selection, 2D and
the ratio EXACTLY.  At K = 2 the hypothesis AllCoordinatesRawLocalContrastRankOne
is vacuous -- proved in Lean as ``binary_allCoordinatesRawLocalContrastRankOne``,
and independently confirmed from the dimension side (codim m(K-2) = 0, addendum B
Section 96).  So the rank-one hypothesis contributes nothing to this refutation:
what fails is the plain bound 2D <= (m-1) delta_square on the binary cube.
"""
from __future__ import annotations
import itertools, json, sys, time
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from research_chains.provenance import write_artifact_with_provenance  # noqa: E402

PROTOCOL_VERSION = "d6_binary_collapse_of_raw_witness_v1"
EVIDENCE_CLASS = "EXACT_RATIONAL_COUNTEREXAMPLE_INDEPENDENTLY_RECOMPUTED"
SRC = ROOT / "research/d6_contrast_rank_falsification/RAWsweep_m6_d64_s5.json"
PRIOR = ROOT / "research/d6_contrast_rank_falsification/B3binary_m6_K2.json"
OUT = ROOT / "research/d6_contrast_rank_falsification/D6_UNCONDITIONAL_BINARY_KILLED_20260906.json"


def evaluate(vals, m, K, q):
    acts = list(itertools.product(range(K), repeat=m)); k = m // 2
    def at(z, i, u): a = list(z); a[i] = u; return tuple(a)
    def others(i): return list(itertools.product(*[range(K) if j != i else [0] for j in range(m)]))
    def ctxw(i, z):
        p = F(1)
        for j in range(m):
            if j != i: p *= q[j][z[j]]
        return p
    R = [[sum(vals[at(z, i, u)] * ctxw(i, z) for z in acts if z[i] == 0) for u in range(K)]
         for i in range(m)]
    base = sum(R[0][u] * q[0][u] for u in range(K))
    comp = [[R[i][u] - base for u in range(K)] for i in range(m)]
    delta = F(0)
    for i in range(m):
        Z = others(i)
        for u in range(K):
            for v in range(K):
                dif = [vals[at(z, i, u)] - vals[at(z, i, v)] for z in Z]
                delta = max(delta, max(dif) - min(dif))
    losses = {S: F(1, 2) * (max(x) - min(x)) for S in itertools.combinations(range(m), k)
              for x in [[vals[a] - sum(comp[i][a[i]] for i in S) for a in acts]]}
    score = [max(R[i]) - min(R[i]) for i in range(m)]
    sel = tuple(sorted(sorted(range(m), key=lambda i: (-score[i], i))[:k]))
    opt = min(losses.values()); reg = losses[sel] - opt
    lo = min(score[i] for i in sel); hi = max(score[i] for i in range(m) if i not in sel)
    return {"delta_square": str(delta), "selected": list(sel),
            "argmin_subsets": [list(S) for S, v in losses.items() if v == opt],
            "selected_loss": str(losses[sel]), "optimal_loss": str(opt),
            "doubled_decision_gap": str(2 * reg), "m_minus_one_delta": str((m - 1) * delta),
            "exact_ratio": str(2 * reg / ((m - 1) * delta)),
            "exact_ratio_float": float(2 * reg / ((m - 1) * delta)),
            "strict_violation": bool(2 * reg > (m - 1) * delta),
            "top_c_score_margin": str(lo - hi), "strict_top_c": bool(lo > hi),
            "top_c_margin_relative_float": float((lo - hi) / delta)}


def main():
    t0 = time.time()
    src = json.load(open(SRC)); prior = json.load(open(PRIOR))
    w = src["counterexample"]; m, K = src["m"], src["alphabet"]
    Fv = {tuple(e["action"]): F(e["value"]) for e in w["world"]}
    phi = [(0,) + tuple(r) for r in w["lambda_int"]]

    def key(a): return tuple(1 if phi[i][a[i]] else 0 for i in range(m))
    groups = {}
    for a, v in Fv.items():
        groups.setdefault(key(a), set()).add(v)
    factors = all(len(s) == 1 for s in groups.values())
    if not factors:
        raise SystemExit("witness does not factor through the binary key")
    binary = {b: next(iter(groups[b])) for b in groups}

    at_K3 = evaluate(Fv, m, K, [[F(t) for t in r] for r in w["q"]])
    at_K2 = evaluate(binary, m, 2, [[F(1), F(0)] for _ in range(m)])
    identical = all(at_K3[kk] == at_K2[kk] for kk in
                    ("delta_square", "selected", "doubled_decision_gap",
                     "m_minus_one_delta", "exact_ratio", "top_c_score_margin"))

    result = {
        "protocol_version": PROTOCOL_VERSION, "development_only": True,
        "evidence_class": EVIDENCE_CLASS,
        "claim": "2D <= (m-1)*delta_square for ALL worlds on the binary cube, "
                 "corner reference (NO rank hypothesis: at K=2 "
                 "AllCoordinatesRawLocalContrastRankOne is vacuous)",
        "verdict": "FALSE", "status": "KILLED",
        "m": m, "reference": "corner (deterministic product), corner index 0",
        "source_witness": SRC.name, "source_lambda_int": w["lambda_int"],
        "phi_per_coordinate": [list(p) for p in phi],
        "collapse": {
            "witness_factors_through_binary_key": factors,
            "distinct_values": len(set(Fv.values())),
            "grid_points_K3": K ** m, "grid_points_K2": 2 ** m,
            "why": "Every basis column of the raw fibre at lambda_i=(0,1,0) is a product "
                   "of phi_i(a_i)=[a_i=1], so it is a function of the binary key alone. "
                   "Symbol 2 is an exact duplicate of symbol 0 in the witness.",
        },
        "evaluated_at_K3": at_K3, "evaluated_at_K2": at_K2,
        "K2_reproduces_K3_exactly": identical,
        "consequence":
            "The refutation does not need the raw rank-one hypothesis. At K=2 that "
            "hypothesis holds for every world (Lean: binary_allCoordinatesRawLocalContrast"
            "RankOne; dimension side: codim m(K-2)=0). The bound 2D <= (m-1) delta_square "
            "therefore fails UNCONDITIONALLY at m=6 on the binary cube with corner "
            "reference. D6-prime dies as a corollary, not as the primary finding.",
        "supersedes": {
            "artifact": PRIOR.name,
            "recorded_best_exact_ratio": prior["best_exact_ratio"],
            "recorded_best_exact_ratio_float": prior["best_exact_ratio_float"],
            "recorded_as": "no counterexample over the whole binary function space",
            "budget_recorded": {
                "corner_fibers": prior.get("corner_fibers"),
                "corner_starts": prior.get("corner_starts"),
                "corner_exact_leads": prior.get("corner_exact_leads"),
                "corners_swept": prior.get("corners_swept"),
                "wall_clock_seconds": prior.get("wall_clock_seconds"),
            },
            "budget_of_the_killing_run": {
                "corner_fibers": src["corner_fibers"], "corner_starts": src["corner_starts"],
                "corner_exact_leads": src["corner_exact_leads"],
                "corner_maxiter": src["corner_maxiter"], "corners_swept": src["corners_swept"],
                "wall_clock_seconds": src["wall_clock_seconds"],
            },
            "reason": "The prior binary run spent 66.147 s across 64 corners (about 1.4 s per "
                      "corner, 8 fibres, 1 start, 2 exact leads). Addendum B Section 96 read "
                      "its 0.3584 as a ceiling over 'every binary world' because one fibre "
                      "covers the whole 2^m space at K=2. Coverage of the SPACE was confused "
                      "with coverage by the SEARCH. The killing run spent 1658 s on a single "
                      "corner with 24 fibres, 3 starts and 10 exact leads.",
        },
        "binary_world": [{"action": list(b), "value": str(v)} for b, v in sorted(binary.items())],
        "max_denominator_digits": len(str(max(v.denominator for v in binary.values()))),
        "non_claims": [
            "Exact rational counterexample, not a Lean proof. Promotion to PROVED FALSE needs "
            "a Lean module, and the present witness carries 48-digit denominators.",
            "This refutes the bound at m=6, corner reference. It says nothing about other m "
            "or other references, and nothing about the sharp constant: the corner sweep stops "
            "at the FIRST certified violation, so 1.000440 is a first crossing, not a supremum.",
            "The proved raw-route Lean corpus is untouched. What this shows is that the "
            "invariant cannot rescue the bound, because the bound already fails where the "
            "invariant is vacuous.",
        ],
        "wall_clock_seconds": round(time.time() - t0, 3),
    }
    if OUT.exists():
        raise SystemExit(f"refusing to overwrite existing ledger artifact: {OUT}")
    write_artifact_with_provenance(
        OUT, result,
        protocol={"protocol_version": PROTOCOL_VERSION, "source": SRC.name,
                  "prior": PRIOR.name, "m": m},
        seed=int(src["seed"]), evidence_class=EVIDENCE_CLASS, chain="D6")
    print(json.dumps({"verdict": result["verdict"], "status": result["status"],
                      "K2_reproduces_K3_exactly": identical,
                      "K2_ratio": at_K2["exact_ratio"],
                      "K2_ratio_float": at_K2["exact_ratio_float"],
                      "K2_strict_violation": at_K2["strict_violation"],
                      "prior_recorded_ceiling": prior["best_exact_ratio_float"],
                      "out": str(OUT)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
