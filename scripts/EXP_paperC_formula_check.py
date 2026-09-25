#!/usr/bin/env python3
"""Paper C: floating-point cross-checks of the three closed-form values (NUMERICAL).

The values are theorems (Lean): the whole frontier `V_m(eta)` (`even_frontier_all`,
`odd_frontier`) and the banded ex-post value `V^post_m(eta)` (`expost_even`, `expost_odd`).
This script solves the corresponding linear programs at small sizes and checks that the
solver lands on the formulas.  It certifies nothing; a mismatch would mean either a
modelling error in the LP or a transcription error, and the script refuses to write.

LP model: variables are masses on the distinct weight sequences (rankings of g_m up to
relabelling within weight classes), with the per-class prefix-count band; after uniform
relabelling inside each class this is the per-item band (`actual_banded_witness_of_counts`,
`actual_banded_infima`).  Ex ante: minimise `max_k E r_k`.  Ex post: minimise
`E max_k r_k`, which is linear in the law.

Output (new file; refuses to overwrite): research/unified_20260919/paperC_formula_check.json
"""

import hashlib
import itertools
import json
import pathlib
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

OUT = pathlib.Path("research/unified_20260919/paperC_formula_check.json")
MS = [3, 4, 5, 6, 7, 8, 9]
ETAS = [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 0.95, 1.0, 1.25, 1.5, 2.0]
TOL = 1e-7
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""), flush=True)
    return ok


def family(m):
    p = (m - 1) // 2
    q = m - 2 - p
    return [-3] + [-1] * p + [1] * q + [3], {-3: 1, -1: p, 1: q, 3: 1}


def excess(s):
    S, out = 0, []
    for k in range(1, len(s)):
        S += s[k - 1]
        out.append(abs(S) - (k % 2))
    return out


def v_free(m):
    return Fr(2, (m + 4) * (m - 1))


def frontier(m, eta):
    """even_frontier_all / odd_frontier."""
    eta = Fr(eta).limit_denominator(10 ** 6)
    if m % 2 == 0:
        return max(v_free(m), 4 * (1 - eta) / (m * (m + 4)))
    return max((m + 3 - (m + 1) * eta) / (m * (m + 4)),
               v_free(m) + max(Fr(0), 1 - eta) / (m * (m + 4)))


def expost(m, eta):
    """expost_even / expost_odd."""
    eta = Fr(eta).limit_denominator(10 ** 6)
    if m % 2 == 0:
        return Fr(2, m + 4)
    return (2 + 2 * max(Fr(0), 1 - eta) / m) / (m + 4)


def solve(m, eta, post):
    g, N = family(m)
    seqs = sorted(set(itertools.permutations(g)))
    n = len(seqs)
    ex = np.array([excess(s) for s in seqs], float)
    A, b = [], []
    for w in N:
        if N[w] == 0:
            continue
        for k in range(1, m):
            r = [sum(1 for x in s[:k] if x == w) / N[w] for s in seqs]
            A.append(r + ([] if post else [0])); b.append(k / m + eta / m)
            A.append([-x for x in r] + ([] if post else [0])); b.append(-(k / m - eta / m))
    if post:
        c = ex.max(axis=1)
        res = linprog(c, A_ub=A, b_ub=b, A_eq=[[1] * n], b_eq=[1],
                      bounds=[(0, None)] * n, method="highs")
    else:
        for k in range(m - 1):
            A.append(list(ex[:, k]) + [-1]); b.append(0)
        c = np.zeros(n + 1); c[-1] = 1
        res = linprog(c, A_ub=A, b_ub=b, A_eq=[[1] * n + [0]], b_eq=[1],
                      bounds=[(0, None)] * n + [(None, None)], method="highs")
    return res.fun / (m + 4) if res.success else None


def main():
    if OUT.exists():
        print(f"refusing to overwrite existing {OUT}", file=sys.stderr)
        return 2
    rows, worst_a, worst_p = [], 0.0, 0.0
    for m in MS:
        for eta in ETAS:
            va, vp = solve(m, eta, False), solve(m, eta, True)
            fa, fp = float(frontier(m, eta)), float(expost(m, eta))
            worst_a = max(worst_a, abs(va - fa))
            worst_p = max(worst_p, abs(vp - fp))
            rows.append({"m": m, "eta": eta, "lp_exante": va, "formula_exante": fa,
                         "lp_expost": vp, "formula_expost": fp})
        print(f"  m={m} done", flush=True)
    check("every ex-ante LP value equals the frontier formula (even_frontier_all, odd_frontier)",
          worst_a < TOL, f"largest gap {worst_a:.2e}")
    check("every ex-post LP value equals the banded ex-post formula (expost_even, expost_odd)",
          worst_p < TOL, f"largest gap {worst_p:.2e}")
    out = {"producer": "scripts/EXP_paperC_formula_check.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "evidence_class": "NUMERICAL (float LP cross-check of Lean formulas)",
           "ms": MS, "etas": ETAS, "tolerance": TOL, "rows": rows,
           "checks": CHECKS, "all_passed": all(c["ok"] for c in CHECKS)}
    if not out["all_passed"]:
        print("REFUSING to write: a check failed.", file=sys.stderr)
        return 1
    OUT.write_text(json.dumps(out, indent=1))
    print(f"wrote {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
