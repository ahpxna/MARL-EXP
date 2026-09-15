#!/usr/bin/env python3
"""D07 probe 3: what exactly degrades as the limiting margin r_inf -> 0.

r_inf(tau,rho) = 2(1+tau)exp(-2tau) - rho.  Fix tau, set
    rho = rho_bd(tau) - mu,   rho_bd(tau) = 2(1+tau)exp(-2tau),
so the limiting margin is exactly mu (to 40 digits), and sweep mu over decades.

For each (tau, mu) we record, over a geometric ladder of k:
  * sup_k  k*|phaseValueFull/k - Gamma|   (is the O(1/k) CONSTANT bounded?)
  * k_cross(mu): the largest k at which the FINITE-k activity test
        k*r <= e   (equivalently  r <= e/k)
    still fails while the LIMIT is active -- i.e. V = 0 but Gamma > 0.
  * k_settle(mu): smallest k on the ladder with |k*err - C1| <= 0.05*|C1|.

rho is emitted as an exact 40-digit rational so that phaseValueFull stays exact
Fraction arithmetic; only exp() is Decimal (prec 60).
"""
import json
import sys
from decimal import Decimal, getcontext
from fractions import Fraction as F

getcontext().prec = 60
OUT = "/Users/phanan/cig-amf-main/research/high_risk_20260910/D07_boundary_margin_20260912.json"
SCALE = 10 ** 40


def D(x):
    if isinstance(x, F):
        return Decimal(x.numerator) / Decimal(x.denominator)
    return Decimal(x)


def dec_to_frac(d, scale=SCALE):
    return F(int((d * scale).to_integral_value(rounding="ROUND_HALF_EVEN")), scale)


def coeffs_exact(k, tau):
    q = k - 1
    t = F(tau, k)
    c = (1 - t) ** (2 * q)
    b = F(q - 1) * t * c
    a = (1 - t) ** (2 * q + 1) + F(q) * t * c
    return a, b, c


def pvf(k, p, c, e, r):
    kk = F(k)
    return (max(F(0), kk * r - e) * (p * (kk - 1) + max(F(0), e - r))) / (4 * (c * (kk - 1)))


def limit_pack(tauD, rhoD):
    E = (-2 * tauD).exp()
    a8 = (1 + tauD) * E
    b8 = tauD * E
    r8 = 2 * a8 - rhoD
    p8 = rhoD - 2 * b8
    e8 = min(a8, 2 * b8)
    m8 = max(Decimal(0), e8 - r8)
    c1 = E * (2 * tauD - tauD * tauD)
    a1 = E * tauD * tauD * (1 - tauD)
    b1 = tauD * E * (2 * tauD - tauD * tauD - 2)
    r1, p1 = 2 * a1, -2 * b1
    Gamma = r8 * p8 / (4 * E)
    C1 = (r8 * (p1 + m8) + p8 * (r1 - e8) - r8 * p8 * c1 / E) / (4 * E)
    return E, r8, p8, e8, r1, Gamma, C1


def main():
    taus = [F(1, 10), F(17, 50), F(1, 2)]
    mus = [F(1, 10), F(1, 30), F(1, 100), F(1, 300), F(1, 1000), F(1, 3000),
           F(1, 10000), F(1, 100000)]
    ks = [10, 14, 20, 28, 40, 56, 80, 113, 160, 226, 320, 452, 640, 905, 1280,
          1810, 2560, 3620, 5000]

    rows = []
    for tau in taus:
        tauD = D(tau)
        E = (-2 * tauD).exp()
        rho_bd = 2 * (1 + tauD) * E
        for mu in mus:
            rhoD_target = rho_bd - D(mu)
            rho = dec_to_frac(rhoD_target)
            if not (F(1) <= rho <= F(2)):
                rows.append({"tau": str(tau), "mu": str(mu), "skipped":
                             "rho=%s outside [1,2]" % (float(rho),)})
                continue
            Ef, r8, p8, e8, r1, Gamma, C1 = limit_pack(tauD, D(rho))
            seq, kcross, ksettle = [], None, None
            for k in ks:
                a, b, c = coeffs_exact(k, tau)
                p, r, e = rho - 2 * b, 2 * a - rho, min(a, 2 * b)
                active_finite = (F(k) * r > e)
                V = pvf(k, p, c, e, r)
                err = D(k) * (D(V) / D(k) - Gamma)
                seq.append((k, err, active_finite))
                if not active_finite:
                    kcross = k
                if ksettle is None and abs(err - C1) <= Decimal("0.05") * abs(C1):
                    ksettle = k
            sup_abs = max(abs(v) for _, v, _ in seq)
            rows.append({
                "tau": str(tau), "mu": str(mu), "rho_40digit": str(float(rho)),
                "r_inf_check": str(+r8),
                "Gamma": str(+Gamma), "C1_limit": str(+C1),
                "sup_k_abs_k_times_err": str(+sup_abs),
                "k_last_finite_INACTIVE": kcross,
                "k_settle_5pct": ksettle,
                "predicted_kcross_(e_inf-r1)/mu": float((e8 - r1) / D(mu)),
                "C1_at_zero_margin_pred": str(+(p8 * (r1 - e8) / (4 * Ef))),
                "k_times_err": {str(k): str(+v) for k, v, _ in seq},
            })
    res = {
        "probe": "D07_boundary_margin",
        "precision": "exact Fractions for phaseValueFull; decimal prec=60 for exp; "
                     "rho rounded to a 40-digit rational so the margin is exact to 1e-40",
        "grid": {"tau": [str(x) for x in taus], "mu": [str(x) for x in mus], "k": ks},
        "rows": rows,
    }
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=2)
    for r in rows:
        if "skipped" in r:
            print("tau=%-5s mu=%-8s SKIP %s" % (r["tau"], r["mu"], r["skipped"]))
            continue
        print("tau=%-5s mu=%-8s sup k|err|=%-12.6g C1=%-12.6g kcross_obs=%-6s "
              "kcross_pred=%-9.1f ksettle=%-6s C1(mu->0)=%.6g"
              % (r["tau"], r["mu"], float(r["sup_k_abs_k_times_err"]),
                 float(r["C1_limit"]), r["k_last_finite_INACTIVE"],
                 r["predicted_kcross_(e_inf-r1)/mu"], r["k_settle_5pct"],
                 float(r["C1_at_zero_margin_pred"])))
    print("-> %s" % OUT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
