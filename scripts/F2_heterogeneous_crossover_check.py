#!/usr/bin/env python3
"""F-H_n: the heterogeneous crossover bracket, in exact rational arithmetic.

Outsider: two endpoints at +-rho/2 with variance 1, and n middle cells with
ARBITRARY means z_i and variances sig_i. Incumbent: two cells at -+1/2,
variance 1. rho = 1 - c/sqrt(n), so d = c/sqrt(n); g_i = 1/2 - |z_i|;

    H_n  = (1/n) sum_i sig_i/g_i^2          (the lower-bound scalar)
    H_n+ = (1/n) sum_i sig_i/(g_i+d/2)^2    (the upper-bound scalar)

Claim under test, at the explicit allocation
    u = c^2 H_n/(16 + c^2 H_n),  w_i = (u/(n H_n)) sig_i/g_i^2,  endpoints (1-u)/4:

    n*Gamma_n  =  c^2/(32 + 2 c^2 H_n)      EXACTLY,

i.e. the supervisor's proposed slack factor (1 + 3c^2/(4 n g_0^2)) is not needed.
The value is computed as the minimum over ORDERED pairs of outsider cells of the
exact two-quadratic pinch value A*B*(1-D)^2/(A+B), with
A = 1/(2(1/w_I0 + 1/w_I1)) and B = 1/(2(sig_a/w_a + sig_b/w_b)) — the
variance-weighted form of the pinch already proved in
work/p13_conjectures/LeanFunctionalCrossoverLowerV1.lean.

DOMAIN. The claim needs every middle cell strictly inside the endpoints, i.e.
    g_0 >= d/2 = c/(2 sqrt n).
The probe checks the boundary: outside it the value drops BELOW the formula and
the active pair stops being the endpoint/endpoint one.

Raises on any mismatch.   python3 scripts/F2_heterogeneous_crossover_check.py
"""
from fractions import Fraction as F
import itertools, json, math
from pathlib import Path


def value_at_allocation(n, c, types):
    """types: list of (count, z, sig). Returns a dict of exact quantities."""
    r = int(math.isqrt(n))
    assert r * r == n, (
        f"cells_of: n={n} is not a perfect square; the square grid used here "
        f"needs r*r == n (audit F4).  Pass a perfect square or supply d directly.")
    if r * r != n:
        raise ValueError("n must be a perfect square so that d = c/sqrt(n) is rational")
    if sum(k for k, _, _ in types) != n:
        raise ValueError("type counts must sum to n")
    d = c / r
    rho = 1 - d
    gs = [(k, z, sig, F(1, 2) - abs(z)) for k, z, sig in types]
    if any(g <= 0 for _, _, _, g in gs):
        raise ValueError("middle cell outside the incumbent's span")
    Hn = sum(k * sig / g ** 2 for k, _, sig, g in gs) / n
    Hnp = sum(k * sig / (g + d / 2) ** 2 for k, _, sig, g in gs) / n
    u = c * c * Hn / (16 + c * c * Hn)
    wend = (1 - u) / 4
    per = [(k, z, sig, u / (n * Hn) * sig / g ** 2) for k, z, sig, g in gs]
    total = 4 * wend + sum(k * w for k, _, _, w in per)
    if total != 1:
        raise AssertionError(f"allocation is not a probability vector: {total}")
    A = F(1, 2) / (F(1) / wend + F(1) / wend)
    cells = [(rho / 2, F(1), wend, 1), (-rho / 2, F(1), wend, 1)] + \
            [(z, sig, w, k) for k, z, sig, w in per]
    best, arg = None, None
    for (ma, sa, wa, _), (mb, sb, wb, _) in itertools.permutations(cells, 2):
        B = F(1, 2) / (sa / wa + sb / wb)
        v = A * B * (1 - (ma - mb)) ** 2 / (A + B)
        if best is None or v < best:
            best, arg = v, (ma, mb)
    for (m, sig, w, k) in cells:                      # two distinct cells of one type
        if k >= 2:
            B = F(1, 2) / (2 * sig / w)
            v = A * B / (A + B)                       # D = 0
            if v < best:
                best, arg = v, (m, m)
    g0 = min(g for _, _, _, g in gs)
    return {"d": d, "Hn": Hn, "Hnp": Hnp, "nGamma": n * best, "active": arg,
            "g0": g0, "inside_domain": g0 >= d / 2,
            "formula": c * c / (32 + 2 * c * c * Hn),
            "upper": c * c / (32 + 2 * c * c * Hnp)}


FAMILIES = {
    "flat z=0 sig=1":      lambda n: [(n, F(0), F(1))],
    "z in {0,1/4}":        lambda n: [(n // 2, F(1, 4), F(1)), (n // 2, F(0), F(1))],
    "sig in {1/2,3/2}":    lambda n: [(n // 2, F(0), F(1, 2)), (n // 2, F(0), F(3, 2))],
    "sig in {1/4,5/4}":    lambda n: [(n // 4, F(0), F(1, 4)), (3 * n // 4, F(0), F(5, 4))],
    "z=+-3/8":             lambda n: [(n // 2, F(3, 8), F(1)), (n // 2, F(-3, 8), F(1))],
    "z=7/16 mixed sig":    lambda n: [(n // 2, F(7, 16), F(1)), (n // 2, F(0), F(2))],
}


def main():
    inside = outside = 0
    rows = []
    for n in (64, 256, 1024, 4096, 16384):
        for c in (F(1, 2), F(1), F(2), F(4), F(8)):
            for name, f in FAMILIES.items():
                r = value_at_allocation(n, c, f(n))
                if r["inside_domain"]:
                    if r["nGamma"] != r["formula"]:
                        raise AssertionError(
                            f"inside the domain the value is not exact: n={n} c={c} "
                            f"{name}: {r['nGamma']} vs {r['formula']}")
                    if not (r["formula"] <= r["upper"]):
                        raise AssertionError(f"lower exceeds upper: n={n} c={c} {name}")
                    inside += 1
                else:
                    outside += 1
                    rows.append({"n": n, "c": str(c), "family": name,
                                 "g0": str(r["g0"]), "d_over_2": str(r["d"] / 2),
                                 "nGamma": str(r["nGamma"]),
                                 "formula": str(r["formula"]),
                                 "value_below_formula": r["nGamma"] < r["formula"],
                                 "active_pair": [str(x) for x in r["active"]]})
    print(f"inside the domain g0 >= d/2 : {inside} configurations, "
          f"n*Gamma = c^2/(32 + 2 c^2 H_n) EXACTLY in every one")
    print(f"outside the domain          : {outside} configurations, listed in the artifact")
    below = [r for r in rows if r["value_below_formula"]]
    print(f"  of those, {len(below)} have the value strictly BELOW the formula "
          f"(the formula is NOT a lower bound there)")

    print("\nsame H_n, different middle distribution -> same value?")
    for n in (256, 4096):
        for c in (F(1), F(2)):
            vs = [value_at_allocation(n, c, FAMILIES[k](n))
                  for k in ("flat z=0 sig=1", "sig in {1/2,3/2}", "sig in {1/4,5/4}")]
            hs = {v["Hn"] for v in vs}
            gs = {v["nGamma"] for v in vs}
            print(f"  n={n} c={c}: H_n = {hs}, n*Gamma = {gs}, identical = {len(gs)==1}")
            if len(hs) != 1 or len(gs) != 1:
                raise AssertionError("same H_n did not give the same value")

    out = Path("research/worker_F_Hn_20260914/F2_heterogeneous_crossover_check.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "claim": "at the explicit allocation, n*Gamma_n = c^2/(32 + 2 c^2 H_n) exactly, "
                 "inside the domain g_0 >= c/(2 sqrt n)",
        "arithmetic": "exact Fraction throughout; no floating point decides anything",
        "configurations_inside_domain": inside,
        "configurations_outside_domain": outside,
        "outside_domain_rows": rows,
        "lean_upper_half": "work/p13_conjectures/LeanFunctionalHeterogeneousCrossoverV1.lean",
        "scope": "n a perfect square (so d is rational), at most three distinct "
                 "middle types, c in {1/2,1,2,4,8}. The lower half is NOT proved in "
                 "Lean; only the upper half is.",
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
