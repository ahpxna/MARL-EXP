#!/usr/bin/env python3
"""Paper B: the leading constant of the parity channel's per-query information (NUMERICAL).

Question (and nothing more): with the Lean parity cancellation (LeanPaperBVisibleV1,
`parity_moment_lt`, `parity_moment_eq`), the two mask values of query j differ first at order
h^j, with coefficient
    a_j(y) = (-1)^j j^{-j} (phi^{(j)}(y-1) - phi^{(j)}(y+1)),
so KL(p_+ || p_-) ~ c_j h^{2j} with c_j = (1/2) int a_j^2 / p_0, p_0 = (phi(.-1)+phi(.+1))/2,
and H^2 = 1 - BC ~ c_j h^{2j} / 4. The Taylor remainder is not formalized. This run computes
c_j by quadrature and checks it against the exact divergences at small h.

Model: the density of `pdens` (LeanPaperBParityChiSqV1),
    p_v(y) = 2^{-j} sum_z phi_sigma(y - v prod(z) - (h/j) sum(z)),  z in {+-1}^j, v = +-1,
grouped by the number r of negative signs (prod = (-1)^r, sum = j - 2r, multiplicity C(j,r)).

SELF-CHECKS (refuse to write on failure):
* the moment identity of the Lean theorems, E[prod(Z) (sum Z)^k] = 0 (k < j), j! (k = j),
  by exact enumeration of the cube, j = 1..6;
* the leading coefficient: (p_+ - p_-)/h^j -> a_j pointwise (max error at the smallest h
  below 2% of max|a_j|);
* KL(p_+||p_-)/(c_j h^{2j}), KL(p_-||p_+)/(c_j h^{2j}) and 4 H^2/(c_j h^{2j}) all within 2% of 1
  at the smallest h, and their distance to 1 decreasing over the last three h.

Usage:
    python -u scripts/EXP_paperB_parity_constants.py --smoke
    python -u scripts/EXP_paperB_parity_constants.py
Output (new file; refuses to overwrite): research/unified_20260919/paperB_parity_constants.json
(smoke: paperB_parity_constants_smoke.json)
"""

import hashlib
import itertools
import json
import math
import pathlib
import sys
import time

import numpy as np
from numpy.polynomial.hermite_e import hermeval

OUTDIR = pathlib.Path("research/unified_20260919")


def phi(x, s):
    return np.exp(-x * x / (2 * s * s)) / math.sqrt(2 * math.pi * s * s)


def dphi(n, x, s):
    """n-th derivative of the N(0, s^2) density: (-1)^n s^{-n} He_n(x/s) phi(x)."""
    c = np.zeros(n + 1); c[n] = 1.0
    return (-1) ** n * s ** (-n) * hermeval(x / s, c) * phi(x, s)


def dens(j, v, h, s, y):
    tot = np.zeros_like(y)
    for r in range(j + 1):
        pr = (-1) ** r
        sm = j - 2 * r
        tot += math.comb(j, r) * phi(y - v * pr - (h / j) * sm, s)
    return tot / 2 ** j


def diff(j, h, s, y):
    tot = np.zeros_like(y)
    for r in range(j + 1):
        pr = (-1) ** r
        sm = j - 2 * r
        tot += math.comb(j, r) * (phi(y - pr - (h / j) * sm, s) - phi(y + pr - (h / j) * sm, s))
    return tot / 2 ** j


def a_coef(j, s, y):
    return (-1) ** j * j ** (-j) * (dphi(j, y - 1, s) - dphi(j, y + 1, s))


def trap(f, y):
    return float(np.trapezoid(f, y))


def kl_stable(q, d, y):
    """KL(q + d || q) = int q [(1+x) log1p(x) - x], x = d/q; the integrand is nonnegative and
    of size q x^2 / 2, so no cancellation against int d = 0 is left."""
    x = d / q
    small = np.abs(x) < 1e-3
    g = np.where(small, x * x / 2 - x ** 3 / 6 + x ** 4 / 12 - x ** 5 / 20,
                 (1 + x) * np.log1p(np.where(small, 0.0, x)) - x)
    return trap(q * g, y)


def main():
    smoke = "--smoke" in sys.argv
    out = OUTDIR / ("paperB_parity_constants_smoke.json" if smoke else "paperB_parity_constants.json")
    if out.exists():
        print(f"refusing to overwrite {out}", file=sys.stderr)
        return 2
    checks = []

    def check(name, ok, detail=""):
        checks.append({"name": name, "ok": bool(ok), "detail": detail})
        print(f"  [{'OK  ' if ok else 'FAIL'}] {name}   {detail}", flush=True)
        return ok

    t0 = time.time()
    # 1. the moment identity (the Lean theorems), exact integers
    bad = []
    for j in range(1, 7):
        for k in range(0, j + 1):
            tot = 0
            for z in itertools.product((1, -1), repeat=j):
                tot += math.prod(z) * sum(z) ** k
            want = 0 if k < j else math.factorial(j) * 2 ** j
            if tot != want:
                bad.append((j, k, tot, want))
    check("parity cancellation: sum_z prod(z)(sum z)^k = 0 (k<j), 2^j j! (k=j), j<=6",
          not bad, f"mismatches {bad}")

    sigmas = [1.0] if smoke else [0.5, 1.0]
    js = [1, 2, 3] if smoke else [1, 2, 3, 4, 5]
    hs = [0.2, 0.1, 0.05] if smoke else [0.2, 0.1, 0.05, 0.025]
    rows = []
    coef_worst, kl_worst, mono_ok = 0.0, 0.0, True
    for s in sigmas:
        y = np.linspace(-1 - 14 * s, 1 + 14 * s, 60001)
        p0 = 0.5 * (phi(y - 1, s) + phi(y + 1, s))
        for j in js:
            aj = a_coef(j, s, y)
            cj = 0.5 * trap(aj * aj / p0, y)
            rec = {"sigma": s, "j": j, "c_j": cj, "h": []}
            errs = {"klpm": [], "klmp": [], "hel": []}
            for h in hs:
                pp = dens(j, 1.0, h, s, y)
                pm = dens(j, -1.0, h, s, y)
                d = diff(j, h, s, y)
                klpm = kl_stable(pm, d, y)
                klmp = kl_stable(pp, -d, y)
                hel = 0.5 * trap(d * d / (np.sqrt(pp) + np.sqrt(pm)) ** 2, y)
                scale = cj * h ** (2 * j)
                cerr = float(np.max(np.abs(d / h ** j - aj)) / np.max(np.abs(aj)))
                r = {"h": h, "KL_pm": klpm, "KL_mp": klmp, "H2": hel,
                     "KL_pm_ratio": klpm / scale, "KL_mp_ratio": klmp / scale,
                     "H2_ratio": 4 * hel / scale, "coef_rel_err": cerr}
                rec["h"].append(r)
                errs["klpm"].append(abs(r["KL_pm_ratio"] - 1))
                errs["klmp"].append(abs(r["KL_mp_ratio"] - 1))
                errs["hel"].append(abs(r["H2_ratio"] - 1))
            coef_worst = max(coef_worst, rec["h"][-1]["coef_rel_err"])
            for key in errs:
                kl_worst = max(kl_worst, errs[key][-1])
                e = errs[key][-3:]
                if not (e[0] >= e[1] >= e[2]):
                    mono_ok = False
            rows.append(rec)
            print(f"  sigma={s} j={j}: c_j={cj:.6e}  ratios at h={hs[-1]}: "
                  f"KL+-={rec['h'][-1]['KL_pm_ratio']:.4f} KL-+={rec['h'][-1]['KL_mp_ratio']:.4f} "
                  f"4H2={rec['h'][-1]['H2_ratio']:.4f} ({time.time()-t0:.0f}s)", flush=True)
    check("leading coefficient: (p+ - p-)/h^j -> a_j", coef_worst < 0.02,
          f"worst relative error {coef_worst:.2e}")
    check("KL and Hellinger ratios within 2% at the smallest h", kl_worst < 0.02,
          f"worst |ratio-1| {kl_worst:.2e}")
    check("ratios approach 1 monotonically over the last three h", mono_ok)

    if not all(c["ok"] for c in checks):
        print("SELF-CHECK FAILED; refusing to write", file=sys.stderr)
        return 1
    rec = {"producer": "scripts/EXP_paperB_parity_constants.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "status": "NUMERICAL (trapezoid quadrature); the Taylor remainder is not formalized",
           "checks": checks, "rows": rows, "seconds": time.time() - t0}
    out.write_text(json.dumps(rec, indent=1))
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
