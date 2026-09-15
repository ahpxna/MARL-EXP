#!/usr/bin/env python3
"""Functional: the heterogeneous lower bound INSTANTIATED, every pair type covered,
and the complexity sandwiched.

WHAT WAS MISSING.  `LeanFunctionalHeterogeneousLowerV1` proves the BRIDGE -- every
flipping alternative hands over two distinct outsider cells whose pinch value lies
below the energy -- and then says, in its own words, that instantiating it at the
explicit allocation is NOT done there and is only verified numerically by
`F2_heterogeneous_crossover_check.py`.  `LeanFunctionalHeterogeneousInstanceV1` now
supplies that instantiation.  This file is the bridge between the two: it checks, in
exact rational arithmetic on the SAME configurations the probe uses, the two
identities the Lean proof rests on and each of the three case reductions, and then
closes the complexity sandwich.

THE TWO IDENTITIES (Lean: `mixed_pair_ok`, `middle_pair_ok` take them as `hAR`).
With `r = sig/w` and `A = 1/(2(1/w_I0 + 1/w_I1))`, at the stated allocation
    A * r_endpoint = 1/4,        A * r_middle(i) = g_i^2 / d^2.
Both are checked here as exact rational equalities, per cell, per configuration.

THE THREE CASE REDUCTIONS.  `pairVal >= A d^2/2` is equivalent to
`(1-D)^2 >= d^2 (A R + 1/2)` with `R = r_a + r_b`, and that criterion is checked for
EVERY ordered pair of cells -- endpoint/endpoint, endpoint/middle, middle/middle --
so no pair type is left to a generic argument.  The active pair is reported, and it
is the endpoint pair, which attains the bound with equality.

THE SANDWICH.  The probe already has both scalars,
    H_n  = (1/n) sum sig_i/g_i^2,     H_n+ = (1/n) sum sig_i/(g_i + d/2)^2,
with `n Gamma = c^2/(32 + 2 c^2 H_n)` exactly (lower) and `c^2/(32 + 2 c^2 H_n+)`
(upper).  Since a fixed-confidence sample complexity is `~ log(1/delta)/Gamma`, the
two give a sandwich whose RATIO is `(32 + 2 c^2 H_n)/(32 + 2 c^2 H_n+)`, and that
ratio is computed here and shown to tend to 1 as `n` grows at fixed `c` -- so the
complexity is pinned to a factor that goes to 1, not merely bracketed.

WHAT THIS DOES NOT ESTABLISH
  * The bridge itself is not re-proved; this file checks the arithmetic the Lean
    instantiation uses against the probe's exact numbers.
  * `1 - D >= g + d/2` and `1 - D >= g_a + g_b` are geometric facts about a middle
    cell sitting inside the incumbent's span; they are CHECKED here per pair, and
    assumed as hypotheses in Lean.
  * The sample-complexity statement is the standard `log(1/delta)/Gamma` reading of
    an information rate; no algorithm or stopping rule is analysed here.

    .venv/bin/python scripts/P10_functional_instantiation.py
"""
from __future__ import annotations

import importlib.util, itertools, json, math
from fractions import Fraction as F
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "f2", REPO / "scripts/F2_heterogeneous_crossover_check.py")
f2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(f2)


def cells_of(n, c, types):
    """the same allocation the probe uses, with the resistances exposed."""
    r = int(math.isqrt(n))
    assert r * r == n, (
        f"cells_of: n={n} is not a perfect square; the square grid used here "
        f"needs r*r == n (audit F4).  Pass a perfect square or supply d directly.")
    d = c / r
    rho = 1 - d
    gs = [(k, z, sig, F(1, 2) - abs(z)) for k, z, sig in types]
    Hn = sum(k * sig / g ** 2 for k, _, sig, g in gs) / n
    Hnp = sum(k * sig / (g + d / 2) ** 2 for k, _, sig, g in gs) / n
    u = c * c * Hn / (16 + c * c * Hn)
    wend = (1 - u) / 4
    per = [(k, z, sig, g, u / (n * Hn) * sig / g ** 2) for k, z, sig, g in gs]
    A = F(1, 2) / (F(1) / wend + F(1) / wend)
    cells = [("endpoint", rho / 2, F(1), wend, None),
             ("endpoint", -rho / 2, F(1), wend, None)]
    for k, z, sig, g, w in per:
        cells.append(("middle", z, sig, w, g))
        if k >= 2:
            cells.append(("middle", z, sig, w, g))     # a second copy of the type
    return d, rho, A, Hn, Hnp, cells, u


def main():
    print("Functional: instantiating the heterogeneous lower bound\n")
    res = {"identities": 0, "pairs_checked": 0, "configurations": 0}
    print("PART 1 -- the two identities the Lean proof rests on, exactly")
    nid = 0
    for n in (64, 256, 1024, 4096):
        for c in (F(1, 2), F(1), F(2), F(4)):
            for name, fam in f2.FAMILIES.items():
                types = fam(n)
                d, rho, A, Hn, Hnp, cells, u = cells_of(n, c, types)
                if min(g for t, _z, _s, _w, g in cells if t == "middle") < d / 2:
                    continue
                for t, _z, sig, w, g in cells:
                    r = sig / w
                    want = F(1, 4) if t == "endpoint" else g ** 2 / d ** 2
                    if A * r != want:
                        raise AssertionError(
                            f"identity fails n={n} c={c} {name} {t}: "
                            f"{A*r} vs {want}")
                    nid += 1
    print(f"   A*r = 1/4 (endpoint) and A*r = g^2/d^2 (middle): {nid} exact "
          f"equalities, over every cell of every in-domain configuration")
    res["identities"] = nid

    print("\nPART 2 -- the criterion d^2(A R + 1/2) <= (1-D)^2 on EVERY ordered pair")
    npair = {"endpoint/endpoint": 0, "endpoint/middle": 0, "middle/middle": 0}
    nfail = 0
    active_types = {}
    nconf = 0
    for n in (64, 256, 1024, 4096):
        for c in (F(1, 2), F(1), F(2), F(4)):
            for name, fam in f2.FAMILIES.items():
                types = fam(n)
                d, rho, A, Hn, Hnp, cells, u = cells_of(n, c, types)
                if min(g for t, _z, _s, _w, g in cells if t == "middle") < d / 2:
                    continue
                nconf += 1
                target = A * d * d / 2
                best, barg = None, None
                for (ta, za, sa, wa, ga), (tb, zb, sb, wb, gb) in \
                        itertools.permutations(cells, 2):
                    R = sa / wa + sb / wb
                    D = za - zb
                    lhs = d * d * (A * R + F(1, 2))
                    rhs = (1 - D) ** 2
                    kind = ("endpoint/endpoint" if ta == tb == "endpoint" else
                            ("middle/middle" if ta == tb == "middle"
                             else "endpoint/middle"))
                    npair[kind] += 1
                    if lhs > rhs:
                        nfail += 1
                    B = F(1, 2) / R
                    v = A * B * (1 - D) ** 2 / (A + B)
                    if best is None or v < best:
                        best, barg = v, kind
                    # the criterion and the pinch comparison must agree
                    if (v >= target) != (lhs <= rhs):
                        raise AssertionError("pairVal_ge_iff fails numerically")
                if best != target:
                    raise AssertionError(
                        f"the minimum is not the endpoint value: n={n} c={c} {name}")
                active_types[barg] = active_types.get(barg, 0) + 1
    print(f"   {sum(npair.values())} ordered pairs over {nconf} in-domain "
          f"configurations: " + ", ".join(f"{k} {v}" for k, v in npair.items()))
    print(f"   criterion failures: {nfail}  (the Lean cases cover all three types)")
    print(f"   the MINIMUM equals A d^2/2 in every configuration, attained at: "
          f"{active_types}")
    if nfail:
        raise AssertionError("a pair violated the criterion inside the domain")
    res["pairs_checked"] = sum(npair.values())
    res["pairs_by_type"] = npair
    res["configurations"] = nconf
    res["active_pair_types"] = active_types

    print("\nPART 3 -- the complexity sandwich, and its ratio")
    rows = []
    for c in (F(1), F(2), F(4)):
        for name in ("flat z=0 sig=1", "z=+-3/8", "z=7/16 mixed sig"):
            seq = []
            for n in (64, 256, 1024, 4096, 16384):
                types = f2.FAMILIES[name](n)
                r = f2.value_at_allocation(n, c, types)
                if not r["inside_domain"]:
                    continue
                lo, hi = r["formula"], r["upper"]
                seq.append((n, float(lo), float(hi), float(hi / lo)))
            if not seq:
                continue
            print(f"   c={c} {name}: n*Gamma in [lower, upper], ratio -> "
                  + ", ".join(f"n={n}:{rt:.6f}" for n, _l, _h, rt in seq))
            if not (seq[-1][3] <= seq[0][3] + 1e-12):
                raise AssertionError("the sandwich ratio is not tightening")
            rows.append({"c": str(c), "family": name,
                         "rows": [{"n": n, "lower": l, "upper": h, "ratio": rt}
                                  for n, l, h, rt in seq]})
    print("   the ratio is (32 + 2c^2 H_n)/(32 + 2c^2 H_n+) and tends to 1 as n")
    print("   grows at fixed c, because d = c/sqrt(n) -> 0 makes H_n+ -> H_n.")
    print("   A fixed-confidence complexity ~ log(1/delta)/Gamma therefore inherits")
    print("   the SAME ratio: the complexity is pinned to a factor tending to 1.")
    res["sandwich"] = rows

    print("\nPART 4 -- the domain is sharp: below g = d/2 the formula stops being a "
          "lower bound")
    out_rows = []
    for n in (64, 256):
        for c in (F(4), F(8)):
            for name, fam in f2.FAMILIES.items():
                r = f2.value_at_allocation(n, c, fam(n))
                if r["inside_domain"]:
                    continue
                below = r["nGamma"] < r["formula"]
                out_rows.append({"n": n, "c": str(c), "family": name,
                                 "g0": str(r["g0"]), "d_over_2": str(r["d"] / 2),
                                 "value_below_formula": bool(below),
                                 "active_pair": [str(x) for x in r["active"]]})
    nb = sum(1 for r in out_rows if r["value_below_formula"])
    print(f"   {len(out_rows)} out-of-domain configurations, {nb} of them have the "
          f"value strictly BELOW the formula")
    print("   which is exactly what `domain_is_sharp` states in Lean: at g < d/2 the")
    print("   endpoint/middle criterion fails, so the endpoint pair stops being the")
    print("   minimiser and the formula is no longer a lower bound.")
    res["out_of_domain"] = out_rows

    res["not_established"] = [
        "the bridge itself is not re-proved here; this file checks the arithmetic "
        "the Lean instantiation uses against the probe's exact numbers",
        "the geometric facts 1-D >= g+d/2 and 1-D >= g_a+g_b are checked per pair "
        "here and assumed as hypotheses in Lean",
        "the sample-complexity reading is the standard log(1/delta)/Gamma; no "
        "algorithm or stopping rule is analysed in this file",
    ]
    outp = REPO / "research/worker_P10_functional_20260914/P10_functional_instantiation.json"
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {outp}")


if __name__ == "__main__":
    main()
