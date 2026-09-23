#!/usr/bin/env python3
"""Paper C: the odd family's circular window sums, and the value they give.

WHAT THIS CHECKS.  `LeanPaperCWindowV1` proves, for `m` odd, `m >= 3` and `0 < k < m`,

    sum_{a<m} |W(a,k)|  =  m+4   (k odd),     =  k+4   (k even),

where `W(a,k)` is the length-`k` circular window of the signed-prefix family starting at
rotation `a`.  `LeanPaperCValueV1` then subtracts the per-budget baseline `b_k = k mod 2`
and reports the value `4/m` at odd budgets, `(k+4)/m` at even ones, maximum `(m+3)/m` at
`k = m-1`.  This script recomputes all of that by brute force and matches it against the
transcribed Lean statements.

WHY THE BASELINE MATTERS, AND WHY IT IS CHECKED SEPARATELY.  The odd budgets carry the
LARGER raw sum (`m+4` against `k+4 <= m+3`) and the SMALLER value, because `b_k = 1` there
removes exactly `m/m`.  Reading the raw sums as the value inverts which budget is worst --
it would put the maximum at the odd budgets, when it is at `k = m-1` and there only.  The
script therefore checks the raw sums, the baseline, and the value as three separate
assertions rather than one.

INDEPENDENT CROSS-CHECK.  At `k = m-1` the corpus already has a different proof
(`sum_rot_abs_prefix`, `LeanPaperCOmitV1`): a prefix of length `m-1` omits one position, so
under a cyclic rotation its sum is `total - (omitted item)`, giving
`sum_rotations |prefix| = sum_items |total - item| = m+3`.  That route shares no step with
the window recursion, so agreeing with it is evidence and not a restatement.

SELF-CHECKS.  Every assertion below is a transcription of a Lean statement.  A failure here
means the formalisation and the arithmetic disagree, and the script refuses to report.
"""

import hashlib
import json
import pathlib
import sys
from collections import Counter
from fractions import Fraction as F

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def base(j):
    """`oddBase`: (+3, -3, then -1 at even index, +1 at odd)."""
    if j == 0:
        return 3
    if j == 1:
        return -3
    return -1 if j % 2 == 0 else 1


def window(m, a, k):
    return sum(base((a + i) % m) for i in range(k))


def gfamily(m, j):
    """`g_m = (-3, -1 x p, +1 x q, +3)` with `p = ceil((m-2)/2) = (m-1)//2`."""
    p = (m - 1) // 2
    return -3 if j == 0 else (3 if j == m - 1 else (-1 if j <= p else 1))


def main():
    sizes = [m for m in range(5, 22, 2)]
    rows = []
    ok_raw = ok_val = ok_max = ok_cross = ok_pref = True

    for m in sizes:
        D = m + 4
        total = sum(base(j) for j in range(m))
        # `oddBase_total`: the period sums to -1
        ok_pref &= (total == -1)

        # `preN_pattern`: prefixes take only {0, 3, -1}
        pref = [sum(base(i) for i in range(j)) for j in range(m + 1)]
        ok_pref &= (pref[0] == 0 and pref[1] == 3)
        ok_pref &= all(pref[j] == (0 if j % 2 == 0 else -1) for j in range(2, m + 1))

        vals = {}
        for k in range(1, m):
            S = sum(abs(window(m, a, k)) for a in range(m))
            # `win_abs_sum_odd` / `win_abs_sum_even`
            ok_raw &= (S == (m + 4 if k % 2 == 1 else k + 4))
            # `winValue_odd` / `winValue_even`: subtract the parity baseline b_k = k mod 2
            v = F(S, m) - F(k % 2)
            ok_val &= (v == (F(4, m) if k % 2 == 1 else F(k + 4, m)))
            vals[k] = v

        mx = max(vals.values())
        argmax = sorted(k for k in vals if vals[k] == mx)
        # `winValue_le` + `winValue_at_last`
        ok_max &= (mx == F(m + 3, m) and argmax == [m - 1])

        # independent route at k = m-1 (`sum_rot_abs_prefix`)
        omit = sum(abs(total - base(j)) for j in range(m))
        ok_cross &= (omit == m + 3 and omit == sum(abs(window(m, a, m - 1)) for a in range(m)))

        rows.append({"m": m, "D": D, "total": total,
                     "raw_odd": m + 4, "raw_even_at_last": m + 3,
                     "value_odd": str(F(4, m)), "value_max": str(mx),
                     "argmax": argmax, "V_m0": str(mx / D),
                     "V_m0_claimed": str(F(m + 3, m * D))})

    check("raw window sums match win_abs_sum_odd (m+4 at odd k) and win_abs_sum_even"
          " (k+4 at even k), at every budget 0<k<m", ok_raw,
          f"sizes {sizes[0]}..{sizes[-1]} odd")
    check("the prefix sequence takes only {0, 3, -1} and the period sums to -1"
          " (preN_pattern, oddBase_total)", ok_pref)
    check("the value after subtracting the parity baseline b_k = k mod 2 is 4/m at odd"
          " budgets and (k+4)/m at even ones (winValue_odd, winValue_even)", ok_val)
    check("the maximum over budgets is (m+3)/m and it is attained at k = m-1 AND NOWHERE"
          " ELSE -- the odd budgets carry the larger raw sum and the smaller value"
          " (winValue_le, winValue_at_last)", ok_max)
    check("the budget k = m-1 agrees with the independent omit-one-item route"
          " (sum_rot_abs_prefix), which shares no step with the window recursion", ok_cross)
    ok_rearr = all(Counter(base(j) for j in range(m))
                   == Counter(gfamily(m, j) for j in range(m)) for m in sizes)
    check("the window construction's base sequence is a REARRANGEMENT of g_m -- same weight"
          " multiset -- so the rotations are a law over rankings of the family and not over"
          " some other sequence (countVal_agree)", ok_rearr,
          "counts (+3,-3,-1,+1) = (1, 1, (m-1)/2, (m-3)/2) on both sides")

    check("V_m(0) from this family equals the value the manuscript records for odd m,"
          " (m+3)/m(m+4)",
          all(r["V_m0"] == r["V_m0_claimed"] for r in rows),
          f"checked at m = {', '.join(str(r['m']) for r in rows)}")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {"source_sha256": hashlib.sha256(
               pathlib.Path("scripts/EXP_paperC_window.py").read_bytes()).hexdigest(),
           "sizes": sizes, "rows": rows,
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperC_window.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
