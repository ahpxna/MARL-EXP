"""Exact budget-regime law for D6 A-free phase designs.

Compares the cyclic cover (block length n=2q+1, penalty (2+1/q)^2) against the
three-group design (block length 3, penalty 9) at INTEGER block counts, which is
the regime the asymptotic variance formulas do not see.

Everything is exact over Q. Development-only: this is an exact computation about
the two designs' Fisher information, NOT a lower bound over all algorithms.
"""
from fractions import Fraction as F
import json, sys, hashlib, pathlib

PROTOCOL_VERSION = "d6_block_budget_law_v1"

def info_cyclic_block(q): return F(q**4, 2*q+1)
def info_threegroup_block(q): return F(q*q, 3)

def best_split(q, N):
    n = 2*q+1; best = None
    for L in range(0, N//n + 1):
        rem = N - L*n; b = rem//3
        info = L*info_cyclic_block(q) + b*info_threegroup_block(q)
        if info > 0 and (best is None or info > best[0]):
            best = (info, L, b, N - L*n - 3*b)
    return best

def main():
    qs = [3,4,5,8,16,32,64]
    rows, violations = [], []
    for q in qs:
        n = 2*q+1
        for N in range(1, 40*n):
            best = best_split(q, N)
            if best is None:
                continue
            info, L, b, waste = best
            greedy_L, greedy_b = N//n, (N - (N//n)*n)//3
            if (L, b) != (greedy_L, greedy_b):
                violations.append({"q": q, "N": N, "opt": [L, b], "greedy": [greedy_L, greedy_b]})
            if N % n in (0, 3, n-1) and N <= 12*n:
                vc = (1/(L*info_cyclic_block(q))) if L > 0 else None
                rows.append({"q": q, "N": N, "remainder": N % n, "L": L, "b": b,
                             "wasted": waste,
                             "var_hybrid": str(1/info),
                             "var_cyclic_only": str(vc) if vc is not None else None})
    per_query_ratio = {str(q): str(F(9*q*q, (2*q+1)**2)) for q in qs}
    payload = {
        "protocol_version": PROTOCOL_VERSION,
        "development_only": True,
        "evidence_class": "EXACT_RATIONAL_COMPUTATION_ON_TWO_NAMED_DESIGNS",
        "law": ("optimal integer split is greedy: L*=floor(N/(2q+1)) cyclic blocks, "
                "then b*=floor((N mod (2q+1))/3) three-group blocks; remainder wasted"),
        "law_violations": violations,
        "law_holds": len(violations) == 0,
        "checked_q": qs,
        "checked_N_per_q": "1 .. 40*(2q+1)",
        "information_per_query_ratio_cyclic_over_threegroup": per_query_ratio,
        "ratio_limit": "9/4",
        "feasibility_threshold": "cyclic needs N >= 2q+1 for one block; below that only three-group runs",
        "non_claim": ("This compares two FIXED designs by Fisher information at integer block "
                      "counts. It is not a lower bound over all query families, and not a "
                      "statement about adaptive algorithms."),
        "rows": rows,
    }
    out = pathlib.Path("research/d6_phase_boundary_20260908/block_budget_law.json")
    if out.exists():
        sys.exit(f"refusing to overwrite existing ledger artifact: {out}")
    out.parent.mkdir(parents=True, exist_ok=True)
    payload["script_sha256"] = hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
    out.write_text(json.dumps(payload, indent=2))
    print(f"law_holds={payload['law_holds']}  violations={len(violations)}  rows={len(rows)}")
    print(f"wrote {out}")

if __name__ == "__main__":
    main()
