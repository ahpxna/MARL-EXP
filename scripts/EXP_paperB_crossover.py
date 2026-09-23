#!/usr/bin/env python3
"""Paper B: how little nonlinearity is needed to destroy the decision/identification gap.

The linear class gives `H^2 = Theta(h^{2r})` for identification.  A degree-2 probe gives
`Theta(h^4)` at `r = 3` --- `EXP_paperB_uniform_hellinger` exhibits one.  The question this
script answers quantitatively is the one in between: if the class is widened by only
`eta`, where is the crossover?

THE PROBE.  With three tail coordinates and `chi = z_4 z_5 z_6`,

    g_eta(z) = (z_4 + z_5 + z_6 + eta z_4 z_5) / (3 + eta),      ||g_eta||_inf = 1,

interpolates between the linear probe (`eta = 0`) and a probe with a degree-2 component.
Its moments against the tail character are exactly

    E[chi g_eta] = 0,    E[chi g_eta^2] = 2 eta/(3+eta)^2,    E[chi g_eta^3] = 6/(3+eta)^3,

so the `eta = 0` signal first appears at the CUBE and the `eta > 0` signal already at the
SQUARE.  That predicts two additive channels, `h^6` from the cube and `eta^2 h^4` from the
square, and a crossover at `eta ~ h`.

WHY THE TWO CHANNELS DO NOT INTERFERE.  The density difference expands as

    p_+ - p_-  =  (eta h^2/(3+eta)^2) A  -  (h^3/(3+eta)^3) B  +  R,
    A(y) = f''(y-1) - f''(y+1),      B(y) = f'''(y-1) - f'''(y+1),

with `f` the head density, which is EVEN in this construction.  Then `A` is odd, `B` is
even and the base density `p_0` is even, so

    int A B / p_0 = 0

and the `eta h^5` cross term drops out of the quadratic leading behaviour.  The script
checks each parity claim and the vanishing integral directly rather than assuming them.

WHAT IS MEASURED.  `H^2` on a grid of `(h, eta)`, fitted to `c_6 h^6 + c_4 eta^2 h^4`, with
the fit validated out of sample and the crossover located.

SCOPE.  This is a law for the ONE probe `g_eta`, not for a widened query class: a single
probe bounds the supremum from below only.  Claiming a class-level crossover would need a
uniform upper bound over that class, which is not attempted here and is not claimed.
"""

import hashlib
import json
import pathlib
import sys
from itertools import product

import numpy as np

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def cube(n):
    return np.array(list(product((-1.0, 1.0), repeat=n)))


def base_means(u, v, r):
    Z = cube(r + 3)
    tail = Z[:, 3:3 + r].prod(axis=1)
    return 3 * u * Z[:, 0] - 2 * Z[:, 1] - 2 * Z[:, 2] + v * tail


def g_eta(r, eta):
    Z = cube(r + 3)
    return (Z[:, 3] + Z[:, 4] + Z[:, 5] + eta * Z[:, 3] * Z[:, 4]) / (3.0 + eta)


def tail_character(r):
    return cube(r + 3)[:, 3:3 + r].prod(axis=1)


def grid_pts(sigma, npts):
    span = 3 + 2 + 2 + 1 + 1 + 8 * sigma
    y = np.linspace(-span, span, npts)
    w = np.full(npts, y[1] - y[0])
    w[0] *= 0.5
    w[-1] *= 0.5
    return y, w


def mixture_density(mu, sigma, y):
    d = np.exp(-0.5 * ((y[:, None] - mu[None, :]) / sigma) ** 2)
    return d.sum(axis=1) / (len(mu) * sigma * np.sqrt(2 * np.pi))


def hellinger_sq(mu1, mu2, sigma, y, w):
    p = mixture_density(mu1, sigma, y)
    q = mixture_density(mu2, sigma, y)
    aff = float(np.sum(w * np.sqrt(np.maximum(p * q, 0.0))))
    return 1.0 - aff, float(np.sum(w * p)), float(np.sum(w * q))


def main():
    smoke = "--smoke" in sys.argv
    sigma, r = 1.0, 3
    npts = 4001 if smoke else 40001
    y, w = grid_pts(sigma, npts)
    chi = tail_character(r)
    m1, m2 = base_means(1, +1, r), base_means(1, -1, r)

    print("=" * 78)
    print("Paper B: the query-class crossover of the decision/identification gap")
    print("=" * 78)

    # ---- the exact moment algebra ------------------------------------------------
    etas = [0.0, 0.25, 1.0] if smoke else [0.0, 0.05, 0.1, 0.2, 0.4, 0.8, 1.6]
    mom = []
    for eta in etas:
        g = g_eta(r, eta)
        mom.append({"eta": eta, "sup_norm": float(np.abs(g).max()),
                    "E_chi_g": float(np.mean(chi * g)),
                    "E_chi_g2": float(np.mean(chi * g ** 2)),
                    "E_chi_g3": float(np.mean(chi * g ** 3)),
                    "pred_g2": 2 * eta / (3 + eta) ** 2,
                    "pred_g3": 6 / (3 + eta) ** 3})
    check("`g_eta` is a legal probe at every eta: sup-norm exactly one",
          all(abs(x["sup_norm"] - 1.0) < 1e-12 for x in mom),
          f"worst |{'||g||'}-1| = {max(abs(x['sup_norm'] - 1) for x in mom):.2e}")
    check("the moment algebra is exact: E[chi g]=0, E[chi g^2]=2eta/(3+eta)^2,"
          " E[chi g^3]=6/(3+eta)^3 -- so eta opens a SQUARE channel while the cube"
          " channel stays open",
          all(abs(x["E_chi_g"]) < 1e-12
              and abs(x["E_chi_g2"] - x["pred_g2"]) < 1e-12
              and abs(x["E_chi_g3"] - x["pred_g3"]) < 1e-12 for x in mom),
          f"worst deviation "
          f"{max(max(abs(x['E_chi_g']), abs(x['E_chi_g2'] - x['pred_g2']),abs(x['E_chi_g3'] - x['pred_g3'])) for x in mom):.2e}")

    # ---- the parity cancellation --------------------------------------------------
    dy = y[1] - y[0]

    def phi(t):
        return np.exp(-t ** 2 / (2 * sigma ** 2)) / (sigma * np.sqrt(2 * np.pi))

    # The FULL head of the observation model is `3 u z1 - 2 z2 - 2 z3` over the cube,
    # with u = 1 as used by `base_means` above -- eight atoms, not four.  An earlier
    # version built only the `-2 z2 - 2 z3` part, i.e. the density of a DIFFERENT model,
    # so the expansion coefficients it verified were not this model's.
    u_head = 1.0
    head = np.array([3.0 * u_head * z1 - 2.0 * z2 - 2.0 * z3
                     for z1 in (-1.0, 1.0) for z2 in (-1.0, 1.0) for z3 in (-1.0, 1.0)])
    f = sum(phi(y - hh) for hh in head) / len(head)

    def dd(a, k):
        o = a.copy()
        for _ in range(k):
            n = np.zeros_like(o)
            n[1:-1] = (o[2:] - o[:-2]) / (2 * dy)
            o = n
        return o

    f2, f3 = dd(f, 2), dd(f, 3)
    A = np.interp(y - 1, y, f2) - np.interp(y + 1, y, f2)
    B = np.interp(y - 1, y, f3) - np.interp(y + 1, y, f3)
    # The baseline is the density of the FULL head 3u z1 - 2 z2 - 2 z3, not of the
    # -2 z2 - 2 z3 part alone.  `A` and `B` are already differences across the z1 channel's
    # +-1 shift, so the law they perturb is the mixture over that same shift.  An earlier
    # version used `p0 = f`, which is a different density; the parity argument is unaffected
    # (the mixture of an even density over +-1 is even) but the numbers were not the model's.
    p0 = 0.5 * (np.interp(y - 1, y, f) + np.interp(y + 1, y, f))
    msk = (np.abs(y) < 10) & (p0 > 1e-28)
    cross = float(np.sum((A * B / p0)[msk]) * dy)
    nA = float(np.sum((A * A / p0)[msk]) * dy)
    nB = float(np.sum((B * B / p0)[msk]) * dy)
    parity = {"A_odd_defect": float(np.max(np.abs(A + A[::-1]))),
              "B_even_defect": float(np.max(np.abs(B - B[::-1]))),
              "p0_even_defect": float(np.max(np.abs(p0 - p0[::-1]))),
              "cross": cross, "normalised_cross": abs(cross) / np.sqrt(nA * nB)}
    check("A is odd, B is even and p_0 is even, so the cross term int A B / p_0 vanishes"
          " -- the eta h^5 term does not interfere with the two channels",
          parity["normalised_cross"] < 1e-6,
          f"normalised cross term {parity['normalised_cross']:.2e};"
          f" A-odd defect {parity['A_odd_defect']:.1e},"
          f" B-even defect {parity['B_even_defect']:.1e}")

    # ---- the measured surface -----------------------------------------------------
    hs = [0.4, 0.2] if smoke else [0.45, 0.35, 0.28, 0.22, 0.17, 0.13]
    print("\n  H^2 on the (h, eta) grid")
    print("  " + "-" * 72)
    rows = []
    for eta in etas:
        g = g_eta(r, eta)
        line = []
        for h in hs:
            H2, _, _ = hellinger_sq(m1 + h * g, m2 + h * g, sigma, y, w)
            rows.append({"eta": eta, "h": h, "H2": H2})
            line.append(H2)
        print(f"      eta={eta:5.3f}  " + "  ".join(f"{v:.3e}" for v in line))

    # fit H^2 ~ c6 h^6 + c4 eta^2 h^4 on the coarse half, validate on the fine half
    # The two-channel form is the leading behaviour of a SMALL-eta expansion, so it is
    # fitted and validated only where that expansion is claimed.  Its failure at large
    # eta is not a defect: there the higher-order terms are not small, and the measured
    # ORDER (below) is the quantity that stays meaningful.
    ETA_FIT = 0.4
    half = max(1, len(hs) // 2)
    coarse = [x for x in rows if x["h"] in hs[:half] and x["eta"] <= ETA_FIT]
    fine = [x for x in rows if x["h"] in hs[half:] and x["eta"] <= ETA_FIT]
    Mc = np.array([[x["h"] ** 6, x["eta"] ** 2 * x["h"] ** 4] for x in coarse])
    yc = np.array([x["H2"] for x in coarse])
    coef, *_ = np.linalg.lstsq(Mc, yc, rcond=None)
    c6, c4 = float(coef[0]), float(coef[1])
    Mf = np.array([[x["h"] ** 6, x["eta"] ** 2 * x["h"] ** 4] for x in fine])
    yf = np.array([x["H2"] for x in fine])
    pred = Mf @ coef
    rel = np.abs(pred - yf) / np.maximum(yf, 1e-300)
    print(f"\n      fitted on the coarse half:  H^2 ~ {c6:.4e} h^6 + {c4:.4e} eta^2 h^4")
    print(f"      out-of-sample relative error on the fine half:"
          f" median {np.median(rel):.3f}, worst {rel.max():.3f}")
    check("both coefficients of c6 h^6 + c4 eta^2 h^4 are positive, so the two channels"
          " are present and additive rather than one masking the other",
          c6 > 0 and c4 > 0, f"c6 = {c6:.4e}, c4 = {c4:.4e}")
    check("the two-channel form fitted on the COARSE half predicts the FINE half"
          f" within the small-eta regime eta <= {ETA_FIT} where the expansion is claimed"
          " -- not a fit re-checked at its own points",
          float(np.median(rel)) < 0.25,
          f"median relative error {np.median(rel):.4f}, worst {rel.max():.4f}"
          f" over {len(fine)} held-out points")

    # the crossover: where does the eta channel overtake the h channel?
    cross_rows = []
    for h in hs:
        eta_star = np.sqrt(c6 * h ** 6 / (c4 * h ** 4)) if c4 > 0 else float("nan")
        cross_rows.append({"h": h, "eta_star": float(eta_star),
                           "eta_star_over_h": float(eta_star / h)})
    print("\n      crossover eta*(h) where the two channels are equal:")
    for x in cross_rows:
        print(f"        h={x['h']:5.3f}   eta* = {x['eta_star']:.4f}"
              f"   eta*/h = {x['eta_star_over_h']:.4f}")
    print("      (eta*/h is sqrt(c6/c4) and is h-free BY CONSTRUCTION of the fitted form,"
          " so it is reported, not tested)")

    # The two falsifiable consequences of the two-channel form, measured directly from
    # H^2 and not from the fit: order six along eta = 0, order four at fixed eta > 0.
    def order_at(eta):
        v = [x["H2"] for x in rows if x["eta"] == eta]
        return float(np.polyfit(np.log(hs), np.log(v), 1)[0])

    ord0 = order_at(0.0)
    eta_big = max(etas)
    ordb = order_at(eta_big)
    ord_rows = [{"eta": e, "order": order_at(e)} for e in etas]
    print("\n      measured order in h at each eta (from H^2 directly, not from the fit):")
    for x in ord_rows:
        print(f"        eta={x['eta']:5.3f}   order = {x['order']:.3f}")
    check("at eta = 0 the measured order in h is six -- the linear probe reaches the"
          " worlds only through the CUBE channel",
          abs(ord0 - 6.0) < 0.6, f"order at eta=0 is {ord0:.3f}")
    check("at the largest eta the measured order drops toward four -- the SQUARE channel"
          " has taken over, which is the collapse the crossover predicts",
          ordb < ord0 - 1.0 and ordb < 5.0,
          f"order at eta={eta_big} is {ordb:.3f} against {ord0:.3f} at eta=0")
    check("the measured order decreases monotonically in eta, so the transition is a"
          " crossover and not a switch",
          all(ord_rows[i]["order"] >= ord_rows[i + 1]["order"] - 0.15
              for i in range(len(ord_rows) - 1)),
          "; ".join(f"eta={x['eta']}: {x['order']:.2f}" for x in ord_rows))

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    print("\n  SCOPE.  This is the law for the single probe g_eta, and a probe bounds the")
    print("  supremum from below only.  It does NOT establish a crossover for a widened")
    print("  query CLASS: that needs a uniform upper bound over the class, which is not")
    print("  attempted here.  The moment algebra and the parity cancellation are exact;")
    print("  the two-channel fit is a measurement.")

    out = {"sigma": sigma, "r": r, "smoke": bool(smoke),
           "moments": mom, "parity": parity, "rows": rows,
           "fit": {"c6": c6, "c4": c4, "eta_fit_max": ETA_FIT,
                   "oos_median_rel": float(np.median(rel)),
                   "oos_worst_rel": float(rel.max())},
           "crossover": cross_rows, "order_by_eta": ord_rows,
           "scope": "one probe g_eta; a lower bound on the supremum, not a class-level"
                    " crossover law",
           "source_sha256": hashlib.sha256(
               pathlib.Path("scripts/EXP_paperB_crossover.py").read_bytes()).hexdigest(),
           "checks": CHECKS, "all_passed": nfail == 0}
    dest = ("research/unified_20260919/paperB_crossover"
            + ("_smoke" if smoke else "") + ".json")
    with open(dest, "w") as f:
        json.dump(out, f, indent=2)
    print(f"\n  artifact: {dest}")
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
