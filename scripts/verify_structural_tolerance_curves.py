"""Exact chi_epsilon curves for Structural, two models.

(A) staircase family and disjoint unions of staircase blocks
(B) scalar two-support-point model (the ScalarChi5 witness lives here)

Method: instead of enumerating permutations (m! is infeasible past m=8), test
directly whether a budget set K is coverable by ONE chain, via a layered
reachability DP, then solve the resulting set cover exactly. Everything over Q.

Development-only. These are exact computations on named families, not theorems.
"""
from fractions import Fraction as F
from itertools import combinations
import argparse, json, hashlib, pathlib, sys, random

PROTOCOL_VERSION = "structural_tolerance_curves_v1"

def _curve(m, radius, tot):
    layers = {k: {frozenset(c): radius(frozenset(c)) for c in combinations(range(m), k)}
              for k in range(m+1)}
    L = {k: min(layers[k].values()) for k in layers}
    thr = sorted({(v-L[k])/tot for k in layers for v in layers[k].values()})
    need = list(range(1, m)); full = (1 << len(need)) - 1
    def coverable(K, eps):
        R = {frozenset()}
        for k in sorted(K):
            A = [S for S, v in layers[k].items() if (v-L[k])/tot <= eps]
            R = {S for S in A if any(P <= S for P in R)}
            if not R: return False
        return True
    def chi(eps):
        if full == 0: return 1
        good = [mask for mask in range(1, full+1)
                if coverable([need[i] for i in range(len(need)) if mask >> i & 1], eps)]
        cur = {0}; s = 0
        while full not in cur:
            s += 1
            if s > len(need)+1: return None
            cur = {u | g for u in cur for g in good}
        return s
    rows, prev = [], None
    for e in thr:
        c = chi(e)
        if c != prev: rows.append({"eps_at_least": str(e), "chi": c}); prev = c
    return rows

def staircase_union(blocks):
    rels = [(b,i,neg) for b,r in enumerate(blocks) for i in range(r) for neg in (False,True)]
    acts = [None] + [(b,i) for b,r in enumerate(blocks) for i in range(r)]
    m = len(rels)
    def f(j,a):
        if a is None: return 0
        jb,ji,neg = j; ab,ai = a
        if jb != ab: return 0
        return (-1 if ai <= ji else 0) if neg else (1 if ji == ai else 0)
    def radius(S):
        T = [rels[t] for t in range(m) if t not in S]
        v = [sum(f(j,a) for j in T) for a in acts]
        return F(max(v)-min(v), 2)
    return _curve(m, radius, sum(blocks))

def scalar(w):
    m = len(w); tot = F(sum(abs(x) for x in w), 2)
    if tot == 0: return None
    def radius(S):
        return F(abs(sum(w[j] for j in range(m) if j not in S)), 2)
    return _curve(m, radius, tot)

def main():
    parser=argparse.ArgumentParser();parser.add_argument("--out",default="research/structural_tolerance_20260910/tolerance_curves.json")
    out = pathlib.Path(parser.parse_args().out)
    if out.exists(): sys.exit(f"refusing to overwrite existing ledger artifact: {out}")
    staircase = {str(b): staircase_union(b)
                 for b in ([2],[3],[4],[2,2],[3,2])}
    random.seed(20260911)
    prec = []
    for m in (5,6,7):
        for B in range(1,7):
            lv = []
            for _ in range(30):
                # NOTE: randint(-2**B, 2**B) spans 2**(B+1)+1 values, so the
                # "bits" label below is the exponent, not the signed bit width.
                w = [random.randint(-2**B, 2**B) for _ in range(m)]
                if sum(abs(x) for x in w) == 0: continue
                r = scalar(w)
                if r: lv.append(len(r))
            if not lv:
                continue
            prec.append({"m": m, "bits": B, "levels_max": max(lv),
                         "levels_mean": float(sum(lv)/len(lv)), "samples": len(lv)})
    payload = {
        "protocol_version": PROTOCOL_VERSION,
        "development_only": True,
        "evidence_class": "EXACT_RATIONAL_COMPUTATION_ON_NAMED_FAMILIES",
        "finding_staircase": ("every staircase family and every disjoint union tested has "
                              "EXACTLY TWO levels, collapsing at eps = 1/(2*sum r). "
                              "There is no K-vs-eps trade-off curve in this family."),
        "finding_lower_bound_slack": ("RETRACTED (Structural Section 80). The 1/4 constant is not the "
                                      "strength of the bound: normalized_tolerance_lower already carries "
                                      "the hypothesis 2*r*eps < 1, the full range. The 1/4 appears only in "
                                      "normalized_lower, which instantiates r = floor(1/(4*eps)) to state "
                                      "the bound in eps alone. No factor of two was ever missing. "
                                      "LeanStructuralStaircaseToleranceCurveV1.exact_curve now proves "
                                      "chi_eps = r for eps < 1/(2r) and 1 otherwise, for all r > 0."),
        "finding_precision": {
            "observed_B1_max_levels_by_m": {str(m): max(x["levels_max"] for x in prec if x["m"]==m and x["bits"]==1) for m in (5,6,7)},
            "interpretation": "Finite random search only; no universal precision bound or tail probability for the named witness is established."},
        "staircase_curves": staircase,
        "scalar_precision_sweep": prec,
        "scalarchi5_witness_curve": scalar([-32,7,29,-7,-8,-13,18]),
        "non_claim": ("Exact computations on specific finite families. No claim that chi_eps is "
                      "unbounded at a fixed normalized tolerance, and no claim about families "
                      "outside those enumerated here."),
    }
    payload["script_sha256"] = hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2))
    print(f"wrote {out}")
    print("  staircase: moi cau hinh so muc =",
          {k: len(v) for k, v in staircase.items()})
    print("  witness ScalarChi5 so muc =", len(payload["scalarchi5_witness_curve"]))

if __name__ == "__main__":
    main()
