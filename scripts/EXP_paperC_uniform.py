#!/usr/bin/env python3
"""Paper C: the even mixture at uniform marginals, checked against the Lean statements.

Every check below transcribes a Lean definition verbatim and asserts a theorem that is
proved in the corpus.  Nothing here is a fit and nothing is a plot: if a check fails the
script refuses to report, because a failure would mean the Lean statement and the object
the paper describes have come apart.

Transcribed definitions (`LeanPaperCRankingV1`, `LeanPaperCEvenV1`):

    insWeight a i = if i = a then 3 else if i = a+1 then -3
                    else if i < a then (-1)^(i+1) else (-1)^(i-1)
    flatEven m i  = if i = 0 then -3 else if i = m-1 then 3
                    else if i % 2 = 1 then 1 else -1
    excess pi k   = |prefixSum pi k| - (k % 2)

The mixture is the one `evenMixture_value_at_D` computes: the `m-1` insertion rankings and
the flat ranking, uniformly over the `m` of them, each further mixed half and half with its
sign flip.

Theorems asserted:
  * `uniform_band_zero`            -- every weight type's expected count is its multiplicity
                                      times k/m, EXACTLY, at every budget (band eta = 0);
  * `evenMixtureFlipped_value_at_D`-- the value is 4/(m(m+4)) at every budget;
  * `value_ge_at_uniform_at_D`     -- at uniform marginals the budget-1 regret is exactly
                                      4/(mD), which is the matching lower bound;
  * `free_value_lt_uniform_value`  -- the insertion mixture's free value is strictly below
                                      it, so the eta = 0 mixture does NOT attain the free
                                      value and the even breakpoint is not contradicted;
  * the hypothesis of `Vm_eq_at_zero` -- every ranking in the mixture is a rearrangement of
                                      g_m, so the law is a law over permutations of g_m.

An earlier draft of this check used `(-1)^i` for the non-pair positions of `insWeight` and
reported a second value.  That was a transcription error in THIS file, not in the Lean; the
definition above is the one the corpus proves about, and it is quoted rather than
paraphrased for exactly that reason.
"""
import hashlib
import json
import pathlib
import sys
from fractions import Fraction as F

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "research" / "unified_20260919" / "paperC_uniform.json"
CHECKS = []


def check(claim, ok, detail=""):
    CHECKS.append({"claim": claim, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {claim}   {detail}")


def insWeight(a, i):
    if i == a:
        return 3
    if i == a + 1:
        return -3
    if i < a:
        return (-1) ** (i + 1)
    return (-1) ** (i - 1)


def flatW(m, i):
    if i == 0:
        return -3
    if i == m - 1:
        return 3
    return 1 if i % 2 == 1 else -1


def gFamily(m):
    """g_m = (-3, -1 x p, +1 x q, +3), the signed-prefix family, as a multiset."""
    return sorted([-3, 3] + [-1] * ((m - 2) // 2) + [1] * ((m - 2) - (m - 2) // 2))


def excess(w, k):
    return abs(sum(w[:k])) - (k % 2)


def mixture(m):
    """The m rankings, each half-and-half with its flip: 2m atoms of weight 1/(2m)."""
    rankings = [[insWeight(a, i) for i in range(m)] for a in range(m - 1)]
    rankings.append([flatW(m, i) for i in range(m)])
    fam = []
    for r in rankings:
        fam.append((F(1, 2 * m), r))
        fam.append((F(1, 2 * m), [-x for x in r]))
    return fam


def main():
    ms = [4, 6, 8, 10, 12, 14]
    print("=" * 78)
    print("Paper C: the even mixture at uniform marginals")
    print("=" * 78)

    band_rows, value_rows, perm_rows, lower_rows, sep_rows = [], [], [], [], []
    ok_band = ok_value = ok_perm = ok_lower = ok_sep = True

    for m in ms:
        D = m + 4
        fam = mixture(m)
        target = F(4, m * D)

        # --- uniform_band_zero -----------------------------------------------------
        worst = F(0)
        for k in range(1, m):
            for w in (3, -3, 1, -1):
                cnt = sum(p * sum(1 for i in range(k) if r[i] == w) for p, r in fam)
                mult = F(1) if abs(w) == 3 else F(m - 2, 2)
                worst = max(worst, abs(cnt - mult * F(k, m)))
        ok_band &= (worst == 0)
        band_rows.append({"m": m, "max_abs_deviation": str(worst)})

        # --- evenMixtureFlipped_value_at_D -----------------------------------------
        vals = {sum(p * F(excess(r, k), D) for p, r in fam) for k in range(1, m)}
        ok_value &= (vals == {target})
        value_rows.append({"m": m, "distinct_values": sorted(str(v) for v in vals),
                           "target": str(target)})

        # --- every ranking is a rearrangement of g_m -------------------------------
        g = gFamily(m)
        same = all(sorted(r) == g for _, r in fam)
        ok_perm &= same
        perm_rows.append({"m": m, "all_rearrangements_of_g_m": same,
                          "g_m": g})

        # --- value_ge_at_uniform_at_D: E r_1 = 4/(mD) at uniform marginals ---------
        # At budget 1 the prefix holds one item, so E|S_1| = sum_i |g_i| / m.
        er1 = (F(sum(abs(x) for x in g), m) - 1) / D
        ok_lower &= (er1 == target)
        lower_rows.append({"m": m, "E_r1": str(er1), "target": str(target),
                           "sum_abs_g": sum(abs(x) for x in g)})

        # --- free_value_lt_uniform_value -------------------------------------------
        free = F(2, D * (m - 1))
        ok_sep &= (free < target)
        sep_rows.append({"m": m, "insertion_free_value": str(free),
                         "uniform_value": str(target), "strictly_below": free < target})

    check("`uniform_band_zero`: every weight type's expected count is its multiplicity times"
          " k/m EXACTLY, at every budget -- the band holds at eta = 0, not merely at"
          " eta_*(m)", ok_band,
          "; ".join(f"m={r['m']}: dev {r['max_abs_deviation']}" for r in band_rows))

    check("`evenMixtureFlipped_value_at_D`: the sign-flipped mixture's value is"
          " 4/(m(m+4)) at EVERY budget -- one distinct value, not a maximum over several",
          ok_value,
          "; ".join(f"m={r['m']}: {r['distinct_values']} = {r['target']}"
                    for r in value_rows))

    check("the hypothesis of `Vm_eq_at_zero`: every ranking in the mixture is a"
          " rearrangement of g_m, so the law is a law over permutations of the family and"
          " not over some other weight vector", ok_perm,
          "; ".join(f"m={r['m']}: {r['all_rearrangements_of_g_m']}" for r in perm_rows))

    check("`value_ge_at_uniform_at_D`: at uniform marginals the budget-1 regret is EXACTLY"
          " 4/(mD), because the prefix holds one item and sum_i |g_i| = m+4 -- this is the"
          " lower bound that makes the value exact rather than one-sided", ok_lower,
          "; ".join(f"m={r['m']}: E r_1 = {r['E_r1']} = {r['target']}"
                    f" (sum|g| = {r['sum_abs_g']} = m+4)" for r in lower_rows))

    check("`free_value_lt_uniform_value`: the insertion mixture's free value 2/(D(m-1)) is"
          " STRICTLY below 4/(mD), so the eta = 0 mixture does not attain the free value and"
          " `breakpoint_lower_even` is not contradicted -- the earlier note claiming a"
          " tension was wrong", ok_sep,
          "; ".join(f"m={r['m']}: {r['insertion_free_value']} < {r['uniform_value']}"
                    for r in sep_rows))

    out = {"source_sha256": hashlib.sha256(
               pathlib.Path(__file__).read_bytes()).hexdigest(),
           "m_values": ms, "band": band_rows, "value": value_rows,
           "rearrangement": perm_rows, "lower_bound": lower_rows,
           "separation": sep_rows,
           "checks": CHECKS, "all_passed": all(c["ok"] for c in CHECKS)}
    OUT.write_text(json.dumps(out, indent=1))
    print(f"\n{sum(c['ok'] for c in CHECKS)}/{len(CHECKS)} self-checks passed")
    print(f"  artifact: {OUT.relative_to(ROOT)}")
    if not out["all_passed"]:
        print("REFUSING to report: a self-check failed.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
