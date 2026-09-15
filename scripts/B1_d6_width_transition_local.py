#!/usr/bin/env python3
"""Package B probe: the local width transition at the scalar boundary.

Everything that is rational is computed with exact `Fraction` arithmetic from
the ACTUAL D6 construction means (the same affine means the Lean modules use),
never from a fitted curve.  Every check RAISES on mismatch.

Model (identical to research/worker_distinct_research_acceptance_20260913/
approximate_game.py):  coords = {0..2q}, special coordinate j = 2q+1,
true label A = {0..q}, B = coords \\ A (|B| = q).  For a label C (a (q+1)-subset
of coords) and nuisance nu the ACTUAL means are

    scalar i :  1                      if i in C
                nu - 1                 if i = j
                1 - nu                 otherwise
    query (G,h), j not in G :  (1-h) + (1-nu)*(|G \\ C| - h)

Information of a cost allocation w (cost mass, sum 1) with charges c_e
(= cost*variance) is  sum_e (w_e/c_e) * (m_theta(e) - m_alpha(e))^2 / 2.

Design w_eta : cost mass (1-eta)/q on each B-scalar (charge 1), cost mass
eta/C(q,2) on each unordered B-pair (G, h=false) (charge cz).
"""
from fractions import Fraction as F
from itertools import combinations
import json, math, sys, time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from certified_pow import enclose_zstar, enclose_charge

OUT = Path("/Users/phanan/cig-amf-main/research/worker_gopB_20260913")
FAIL = []

def check(cond, msg):
    if not cond:
        raise AssertionError("PROBE FAILED: " + msg)

# ---------------------------------------------------------------- model ------
def mean_scalar(C, j, nu, i):
    if i in C: return F(1)
    if i == j: return nu - 1
    return 1 - nu

def mean_query(C, j, nu, G, h):
    assert j not in G
    k = len(set(G) - set(C))
    return (0 if h else 1) + (1 - nu) * (k - (1 if h else 0))

def universe(q):
    coords = list(range(2 * q + 1)); j = 2 * q + 1
    A = frozenset(range(q + 1)); B = frozenset(coords) - A
    return coords, j, A, B

# ------------------------------------------------- 1. hypergeometric count ---
def hypergeometric_check():
    """The number of changed B coordinates that land in a uniform 2-subset G of B
    is Hypergeometric(q, d, 2).  Exact counts, 20 configurations."""
    rows = []
    configs = [(q, d) for q in (3, 4, 5, 6, 7) for d in range(1, q + 1)][:20]
    check(len(configs) == 20, "expected exactly 20 configurations")
    for q, d in configs:
        _, _, _, B = universe(q)
        Bs = sorted(B); S = set(Bs[:d])
        pairs = list(combinations(Bs, 2))
        counts = {}
        for G in pairs:
            k = len(set(G) & S)
            counts[k] = counts.get(k, 0) + 1
        emp = {k: F(v, len(pairs)) for k, v in counts.items()}
        hyp = {}
        for k in range(0, 3):
            if k <= d and 2 - k <= q - d:
                hyp[k] = F(math.comb(d, k) * math.comb(q - d, 2 - k), math.comb(q, 2))
        check(emp == hyp, f"hypergeometric pmf mismatch at q={q} d={d}: {emp} vs {hyp}")
        m1 = sum(k * p for k, p in emp.items())
        check(m1 == F(2 * d, q), f"hypergeometric mean mismatch q={q} d={d}")
        m2 = sum(k * k * p for k, p in emp.items())
        var = m2 - m1 * m1
        want = F(2, 1) * F(d, q) * (1 - F(d, q)) * F(q - 2, q - 1)
        check(var == want, f"hypergeometric variance mismatch q={q} d={d}")
        rows.append({"q": q, "d": d, "pmf": {str(k): str(v) for k, v in sorted(emp.items())},
                     "mean": str(m1), "variance": str(var)})
    return rows

# --------------------------------------------- 2. design value, real means ---
def design_value_exact(q, mu, nu, eta, cz, C):
    """EXACT information of w_eta against label C at nuisance nu, from the means."""
    coords, j, A, B = universe(q)
    tot = F(0)
    ws = F(1 - eta, 1) if isinstance(eta, int) else (1 - eta)
    for i in sorted(B):
        d = mean_scalar(A, j, mu, i) - mean_scalar(C, j, nu, i)
        tot += (1 - eta) / q * d * d / 2
    npair = math.comb(q, 2)
    for G in combinations(sorted(B), 2):
        d = mean_query(A, j, mu, G, False) - mean_query(C, j, nu, G, False)
        tot += eta / (npair * cz) * d * d / 2
    return tot

def coeffs(q, mu, eta, cz):
    """C_eta, B_eta, A_eta of the handoff."""
    g = 1 - mu
    Cc = (1 - eta) * mu * mu / (2 * q) + eta * g * g / (q * cz)
    Bb = eta * g / (q * cz)
    Aa = (1 - eta) * F(q - 1, 2 * q) + eta * F(2 * q - 3, q) / cz
    return Cc, Bb, Aa

def general_poly(q, mu, eta, cz, d, x):
    """Claimed polynomial for a label changing d B coordinates (verified below)."""
    g = 1 - mu
    sc = (1 - eta) * (d * mu * mu + (q - d) * x * x) / (2 * q)
    npair = math.comb(q, 2)
    jo = F(0)
    for k in range(0, 3):
        if k <= d and 2 - k <= q - d:
            cnt = math.comb(d, k) * math.comb(q - d, 2 - k)
            delta = 2 * x + (g - x) * k
            jo += F(cnt) * delta * delta / 2
    return sc + eta / (npair * cz) * jo

def polynomial_identity_check():
    rows = []
    for q in (3, 4, 5, 6):
        coords, j, A, B = universe(q)
        for mu in (F(1, 4), F(1, 3), F(2, 5)):
            for cz in (F(3), F(7, 2)):
                for eta in (F(1, 5), F(1, 3)):
                    Cc, Bb, Aa = coeffs(q, mu, eta, cz)
                    seen = {}
                    for lab in combinations(coords, q + 1):
                        Cl = frozenset(lab)
                        if Cl == A: continue
                        d = len(Cl & B)
                        for x in (F(0), F(1, 7), F(-1, 5), F(3, 11)):
                            nu = mu + x
                            v = design_value_exact(q, mu, nu, eta, cz, Cl)
                            gp = general_poly(q, mu, eta, cz, d, x)
                            check(v == gp, f"general-d polynomial mismatch q={q} d={d} x={x}")
                            if d == 1:
                                quad = Cc + 2 * Bb * x + Aa * x * x
                                check(v == quad,
                                      f"d=1 quadratic mismatch q={q} mu={mu} cz={cz} eta={eta} x={x}: {v} vs {quad}")
                            seen.setdefault((d, x), set()).add(v)
                    for kk, vs in seen.items():
                        check(len(vs) == 1, f"design value not a function of d alone at {kk}")
                    rows.append({"q": q, "mu": str(mu), "cz": str(cz), "eta": str(eta),
                                 "C_eta": str(Cc), "B_eta": str(Bb), "A_eta": str(Aa),
                                 "labels_checked": math.comb(2 * q + 1, q + 1) - 1})
    return rows

# ------------------------------------------------ 3/4. profile and branches --
def profile_exact(q, mu, eta, cz, d, clip=True):
    """Exact min over nu in [0,1] (clip=True) or over all real nu, of the
    d-changed-coordinate information.  Returns (value, argmin x)."""
    x0, x1, x2 = F(0), F(1, 2), F(-1, 2)
    v0 = general_poly(q, mu, eta, cz, d, x0)
    v1 = general_poly(q, mu, eta, cz, d, x1)
    v2 = general_poly(q, mu, eta, cz, d, x2)
    c = v0
    b = (v1 - v2)
    a = 2 * (v1 + v2 - 2 * v0)
    # v(x) = a x^2 + b x + c with these three points (x=+-1/2)
    check(a * x1 * x1 + b * x1 + c == v1, "quadratic reconstruction failed")
    check(a * x2 * x2 + b * x2 + c == v2, "quadratic reconstruction failed")
    lo, hi = -mu, 1 - mu
    cand = [lo, hi] if clip else []
    vert = None
    if a > 0:
        vert = -b / (2 * a)
        if (not clip) or (lo <= vert <= hi):
            cand.append(vert)
    if not clip:
        check(a > 0, "unbounded below")
        return a * vert * vert + b * vert + c, vert
    best = min((a * x * x + b * x + c, x) for x in cand)
    return best[0], best[1]

def branch_check():
    rows = []
    for q in (3, 4, 5, 6, 8):
        for mu in (F(1, 4), F(1, 3), F(2, 5)):
            g = 1 - mu; V0 = mu * mu / (2 * q); cstar = 2 * g * g / (mu * mu)
            for cz in (cstar / 2, cstar * F(3, 4), cstar):
                for eta in (F(1, 100), F(1, 20), F(1, 8), F(1, 4), F(1, 2)):
                    vals = {}
                    for d in range(1, q + 1):
                        v, xstar = profile_exact(q, mu, eta, cz, d)
                        vals[d] = (v, xstar)
                        if d >= 2:
                            check(v >= (1 - eta) * d * mu * mu / (2 * q),
                                  f"d>=2 scalar floor violated q={q} d={d} eta={eta}")
                    gamma = min(v for v, _ in vals.values())
                    arg = min(vals, key=lambda d: vals[d][0])
                    suff = eta <= cz / (cz + cstar)
                    if suff:
                        check(arg == 1, f"d=1 not the bottleneck though eta<=cz/(cz+cstar): q={q} eta={eta}")
                    vun, xun = profile_exact(q, mu, eta, cz, 1, clip=False)
                    interior = (-mu <= xun <= 1 - mu)
                    rows.append({"q": q, "mu": str(mu), "cz": str(cz), "cstar": str(cstar),
                                 "eta": str(eta), "gamma": str(gamma), "argmin_d": arg,
                                 "V0": str(V0), "beats_V0": bool(gamma > V0),
                                 "d1_unconstrained_equals_clipped": bool(vun == vals[1][0]),
                                 "d1_minimiser_interior": bool(interior),
                                 "sufficient_eta_condition": bool(suff)})
    return rows

# ------------------------------------------------------ 5/6. asymptotics -----
def gain_float(q, mu, cz, eta):
    g = 1 - mu; V0 = mu * mu / (2 * q)
    Cc = (1 - eta) * mu * mu / (2 * q) + eta * g * g / (q * cz)
    Bb = eta * g / (q * cz)
    Aa = (1 - eta) * (q - 1) / (2 * q) + eta * (2 * q - 3) / (q * cz)
    return Cc - Bb * Bb / Aa - V0

def best_eta(q, mu, cz, tol=1e-14):
    lo, hi = 0.0, 1.0 - 1e-12
    for _ in range(300):
        a = lo + (hi - lo) / 3; b = hi - (hi - lo) / 3
        if gain_float(q, mu, cz, a) < gain_float(q, mu, cz, b): lo = a
        else: hi = b
    eta = (lo + hi) / 2
    if not (hi - lo < 1e-9):
        raise RuntimeError("ternary search did not converge")
    if not (0 < eta < 1):
        raise RuntimeError(f"optimal eta out of range: {eta}")
    return eta, gain_float(q, mu, cz, eta)

def expansion_rows():
    rows = []
    for q in (3, 4, 8):
        for mu in (0.25, 0.4):
            g = 1 - mu; V0 = mu * mu / (2 * q)
            zstar = 1 + 2 * math.log(g / mu, 2)
            prev = None
            for h in (0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002, 0.001):
                cz = 2 ** (zstar - h)
                eta, gain = best_eta(q, mu, cz)
                eta_pred = (q - 1) * g * g * math.log(2) / (2 * mu * mu) * h
                gain_pred = (q - 1) * g * g * math.log(2) ** 2 / (8 * q) * h * h
                r_eta = eta / eta_pred; r_gain = gain / gain_pred
                if prev is not None:
                    check(abs(r_gain - 1) <= abs(prev - 1) + 1e-12,
                          f"gain ratio not converging at q={q} mu={mu} h={h}")
                prev = r_gain
                rows.append({"q": q, "mu": mu, "h": h, "z_star": zstar, "eta_opt": eta,
                             "eta_first_order": eta_pred, "eta_ratio": r_eta,
                             "gain": gain, "gain_h2_law": gain_pred, "gain_ratio": r_gain,
                             "q_times_h": q * float(h)})
            check(abs(prev - 1) < 0.02, f"h->0 limit not reached at q={q} mu={mu}: {prev}")
    return rows

def scaling_rows():
    """q*h = t fixed: the fixed-q h^2 law is NOT uniform in q."""
    rows = []
    for mu in (0.25, 0.4):
        g = 1 - mu; cstar = 2 * g * g / (mu * mu)
        zstar = 1 + 2 * math.log(g / mu, 2)
        for t in (0.25, 0.5, 1.0, 2.0, 4.0):
            seq = []
            for q in (8, 16, 32, 64, 128, 256, 512, 1024):
                h = t / q; cz = 2 ** (zstar - h)
                eta, gain = best_eta(q, mu, cz)
                law = (q - 1) * g * g * math.log(2) ** 2 / (8 * q) * h * h
                seq.append((q, eta, gain * q * q, gain / law))
            # limiting profile: maximise F(eta) = eta mu^2 t log2/2 - eta^2 g^2/(cstar^2 A)
            def Flim(eta):
                A = (1 - eta) / 2 + 2 * eta / cstar
                return eta * mu * mu * t * math.log(2) / 2 - eta * eta * g * g / (cstar * cstar * A)
            lo, hi = 0.0, 1 - 1e-12
            for _ in range(300):
                a = lo + (hi - lo) / 3; b = hi - (hi - lo) / 3
                if Flim(a) < Flim(b): lo = a
                else: hi = b
            etalim = (lo + hi) / 2; Flimv = Flim(etalim)
            ratio_last = seq[-1][2] / Flimv
            check(abs(ratio_last - 1) < 2e-2,
                  f"q^2*gain does not converge to the scaling profile at mu={mu} t={t}: {ratio_last}")
            rows.append({"mu": mu, "t_equals_q_h": t, "limit_eta": etalim,
                         "limit_q2_gain": Flimv,
                         "limit_over_fixed_q_law": Flimv / (g * g * math.log(2) ** 2 * t * t / 8),
                         "finite_q": [{"q": q, "eta": e, "q2_gain": v, "gain_over_h2_law": r}
                                       for q, e, v, r in seq]})
    return rows

# ----------------------------------------------------- 7. dual sandwich ------
def dual_upper(q, mu, zlo, zhi, delta):
    """An UPPER bound, so each charge must be a CERTIFIED LOWER bound on r**z:
    dividing by a smaller charge can only raise the value. `zlo <= z <= zhi` are
    rationals that bracket the real exponent; `certified_pow.enclose_charge`
    returns `c_lo <= r**z` proved by the integer comparison `c_lo**den <= r**num`.
    The previous version used `Fraction(float(r**z)).limit_denominator(...)` times
    `(1 - 1e-9)`, which is a rounded float and a nudge and certifies nothing."""
    """Upper bound on the FULL game value from the uniform single-swap mixture
    (a uniform in A, b uniform in B) at nuisance nu = mu - delta.  Rational
    arithmetic; the charge r^z is replaced by a rational LOWER bound (which only
    makes the bound larger, hence still valid)."""
    g = 1 - mu; nu = mu - delta
    if nu < 0: raise ValueError("illegal nuisance")
    vals = [(nu * nu / (2 * (q + 1)), ("scalar", "A")),
            ((mu * mu + (q - 1) * delta * delta) / (2 * q), ("scalar", "B")),
            (delta * delta / 2, ("scalar", "j"))]
    for s in range(q + 2):
        for t in range(q + 1):
            if not (1 <= s + t <= q): continue
            for h in (0, 1):
                if h == 0 and s + t < 2: continue
                r = s + t + h; m = t - h
                EY = F(t, q) - F(s, q + 1)
                EY2 = F(t, q) + F(s, q + 1) - 2 * F(s * t, q * (q + 1))
                E = delta * delta * m * m - 2 * delta * m * (g + delta) * EY + (g + delta) ** 2 * EY2
                cr, _ = enclose_charge(r, zlo, zhi)   # certified c_lo <= r**z
                vals.append((E / (2 * cr), ("query", s, t, h)))
    return max(vals)

def sandwich_rows():
    rows = []
    for q in (3, 4, 8):
        for mu in (F(1, 4), F(2, 5)):
            g = 1 - mu; V0 = mu * mu / (2 * q); cstar = 2 * g * g / (mu * mu)
            # 2**(z*) = 2 (g/mu)**2 is EXACT, but r**(z*) for r != 2 is not, so the
            # exponent itself must be bracketed: enclose_zstar certifies
            # z_lo <= 1 + 2 log2(g/mu) <= z_hi by comparing 2**a with (g/mu)**(2 den).
            zs_lo, zs_hi = enclose_zstar(g, mu)
            for h in (F(1, 10), F(1, 20), F(1, 50), F(1, 100)):
                zlo, zhi = zs_lo - h, zs_hi - h
                # primal wants an UPPER bound on the charge (it lowers L);
                # the eta cap wants a LOWER bound (it keeps eta inside the domain)
                cz_lo, cz_hi = enclose_charge(2, zlo, zhi)
                czup = cz_hi
                cap = cz_lo / (cz_lo + cstar)
                eta_pred = (F(q - 1) * g * g
                            * F(int(10 ** 9 * math.log(2) * float(h)), 10 ** 9)
                            / (2 * mu * mu))
                grid = [F(i, 400) * cap for i in range(1, 401)]
                grid += [F(i, 200) * 2 * eta_pred for i in range(1, 201)]
                best = (F(-1), None)
                for eta in grid:
                    if eta <= 0 or eta > cap: continue
                    vals = [profile_exact(q, mu, eta, czup, d)[0] for d in range(1, q + 1)]
                    v = min(vals)
                    if v > best[0]: best = (v, eta)
                L, etastar = best
                # dual: best delta on a grid (any delta gives a valid upper bound)
                bu = (F(10 ** 9), None, None)
                for i in range(1, 801):
                    delta = F(i, 400) * g * h
                    if delta <= 0 or delta >= mu: continue
                    u, arg = dual_upper(q, mu, zlo, zhi, delta)
                    if u < bu[0]: bu = (u, delta, arg)
                U, deltastar, arg = bu
                check(U >= L, f"dual below primal (bug) q={q} mu={mu} h={float(h)}: {float(U)} < {float(L)}")
                rows.append({"q": q, "mu": str(mu), "h": str(h),
                             "z_lo": str(zlo), "z_hi": str(zhi),
                             "charge_lo": str(cz_lo), "charge_hi": str(cz_hi),
                             "V0": float(V0),
                             # EXACT rationals, so an independent checker can
                             # re-verify every comparison without this script.
                             "V0_exact": str(V0),
                             "primal_lower_L_exact": str(L),
                             "dual_upper_U_exact": str(U),
                             "eta_star_exact": str(etastar),
                             "delta_star_exact": str(deltastar),
                             "gain_L_exact": str(L - V0), "gain_U_exact": str(U - V0),
                             "primal_lower_L": float(L), "eta_star": float(etastar),
                             "dual_upper_U": float(U), "delta_star": float(deltastar),
                             "dual_argmax": list(map(str, arg)),
                             "U_over_L": float(U) / float(L),
                             "gain_L": float(L - V0), "gain_U": float(U - V0),
                             "sandwich_relative_width": float((U - L) / (L - V0)) if L > V0 else None,
                             "q_times_h": q * float(h)})
    return rows


def sandwich_summary(rows):
    """What the sandwich does and does NOT pin down.

    U/L close to 1 is a statement about the VALUE, whose leading term V0 is the
    same on both sides; it says nothing about how well the GAIN L - V0 is pinned.
    The honest figure is (U - L) / (L - V0), and it is reported per cell and at
    its worst.

    The h^2 law is also checked the only way it can be, by SUCCESSIVE RATIOS. The
    grid is h = 1/10, 1/20, 1/50, 1/100, so the ratios h_prev/h are 2, 2.5, 2 and
    an h^2 law predicts gain ratios 4, 6.25, 4 -- not 4 and 2.5."""
    widths = [r["sandwich_relative_width"] for r in rows
              if r["sandwich_relative_width"] is not None]
    groups = {}
    for r in rows:
        groups.setdefault((r["q"], r["mu"]), []).append(r)
    ratio_rows = []
    for (q, mu), rs in sorted(groups.items(), key=str):
        rs = sorted(rs, key=lambda r: -float(F(r["h"])))
        for a, b in zip(rs, rs[1:]):
            hp, hc = F(a["h"]), F(b["h"])
            pred = float((hp / hc) ** 2)
            gL, gU = F(b["gain_L_exact"]), F(b["gain_U_exact"])
            aL, aU = F(a["gain_L_exact"]), F(a["gain_U_exact"])
            # the gain ratio is only known to lie in [gap of the two brackets]
            ratio_rows.append({
                "q": q, "mu": mu, "h_from": a["h"], "h_to": b["h"],
                "h_ratio": float(hp / hc), "h2_law_predicts": pred,
                "gain_ratio_lower": float(aL / gU) if gU > 0 else None,
                "gain_ratio_upper": float(aU / gL) if gL > 0 else None})
    return {"max_relative_gain_width": max(widths) if widths else None,
            "min_relative_gain_width": min(widths) if widths else None,
            "note": "U/L near 1 compares VALUES, which share the leading term V0; "
                    "it does not mean the GAIN is pinned. The gain bracket is as "
                    "wide as max_relative_gain_width in relative terms.",
            "h2_law_note": "h = 1/10, 1/20, 1/50, 1/100 -> successive h ratios "
                           "2, 2.5, 2, so an h^2 law predicts gain ratios "
                           "4, 6.25, 4. A previous report said '4 and 2.5', "
                           "which confused the h ratio with its square.",
            "successive_ratios": ratio_rows}

def main():
    t0 = time.time()
    out = {"status": "running", "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    out["hypergeometric_exact"] = hypergeometric_check()
    print("1. hypergeometric: 20/20 configurations exact", flush=True)
    out["polynomial_identity_exact"] = polynomial_identity_check()
    print("2. real-mean polynomial identity: exact on every label", flush=True)
    out["branches"] = branch_check()
    print("3/4. d>=2 floor and d=1 profile: checked", flush=True)
    out["expansion"] = expansion_rows()
    print("5. eta_h and h^2 expansion at q=3,4,8: checked", flush=True)
    out["scaling_qh"] = scaling_rows()
    print("6. q*h scaling profile: checked", flush=True)
    out["dual_sandwich"] = sandwich_rows()
    out["dual_sandwich_summary"] = sandwich_summary(out["dual_sandwich"])
    sm = out["dual_sandwich_summary"]
    print(f"7. primal/dual sandwich: checked; relative width of the GAIN bracket "
          f"{sm['min_relative_gain_width']:.4f} .. {sm['max_relative_gain_width']:.4f}",
          flush=True)
    for rr in sm["successive_ratios"]:
        print(f"   q={rr['q']} mu={rr['mu']}: h {rr['h_from']} -> {rr['h_to']} "
              f"(ratio {rr['h_ratio']}), h^2 law predicts {rr['h2_law_predicts']}, "
              f"certified gain ratio in "
              f"[{rr['gain_ratio_lower']:.3f}, {rr['gain_ratio_upper']:.3f}]",
              flush=True)
    out["status"] = "complete"; out["seconds"] = round(time.time() - t0, 1)
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "B1_width_transition_local.json").write_text(json.dumps(out, indent=2) + "\n")
    print("wrote", OUT / "B1_width_transition_local.json", flush=True)

if __name__ == "__main__":
    main()
