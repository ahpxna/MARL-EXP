#!/usr/bin/env python3
"""MASTER (tag MASTER): audit the 'price of evidence B', then replace it with a
FIXED-WORLD acquisition model in which the query is executable and the cost is a
sample count.

Independent re-implementation.  Nothing is imported from the repo; the gate is
transcribed directly from work/p13_conjectures/LeanD6ThresholdConstructionV1.lean
(`gate A j x = if x j then 0 else if (exists i in A, x i) or 2 <= count (others A j) x
then 1 else 0`) and every response is recomputed from that transcription by full
enumeration of the cube in exact rational arithmetic.

PART A  AUDIT.  research/master_reference_20260912/master_reference_phase_certificates_v1.json
        publishes price_of_evidence_B[k,rho].cheapest_t_that_kills_floor :=
        min { t in COARSE GRID : (k-2)b(t) >= 1  AND  V_k(t,rho) = 0 }.
        We recompute, per (k,rho), (i) the in-regime window on the coarse grid,
        (ii) the exact zero-crossing of the algebraic V on a fine dyadic scan
        plus a certified bisection bracket, and (iii) whether the published
        number was set by the grid's resolution or by the regime filter rather
        than by the floor dying.  The regime filter is the thing that could have
        removed the true cause, so it is tested, not assumed innocent.

PART B  RESPONSE LAW, from the Lean gate, exactly.  For |A|=alpha, |B|=beta and
        one distinguished coordinate z (n = alpha+beta+1 coordinates), under the
        product reference Bernoulli(t):
            s_i(t) = a(t) for i in A,  b(t) for i in B,  a(t)-1 for i=z,
            a(t) = (1-t)^(alpha+beta-1) (1+(beta-1)t),
            b(t) = (beta-1) t (1-t)^(alpha+beta-1),
            c(t) = a(t)-b(t) = (1-t)^(alpha+beta-1).
        Verified by enumeration; the construction's own case is beta = alpha-1 = k-1,
        where alpha+beta-1 = 2k-2.

PART C  FIXED WORLD.  Build F_{A,t0} ONCE at t0 and never recompensate:
            F_{A,t0}(x) = g_A(x) - E_{t0}[g_A] + sum_i (rho*1_T(i) - s_i(t0))(x_i - t0).
        A query = one i.i.d. draw X ~ Bernoulli(t1)^n with Y = F_{A,t0}(X) + N(0,sigma^2).
        Readout = the first-order response Delta_i(t1) = E[Y|X_i=1] - E[Y|X_i=0].
        Claim verified exactly:  Delta_i(t1) - rho*1_T(i) = s_i(t1) - s_i(t0),
        hence the A-vs-B contrast is  Gamma(t0,t1) = c(t1) - c(t0), and
        Gamma(t0,t0) = 0 EXACTLY.  That zero is the floor.

PART D  COST.  Two-point test between the fixed world F_{A,t0} and the fixed
        world F_{A',t0} (A' = A with coordinate i swapped for i'), both built at
        t0.  n(t1) = (z_a+z_b)^2 * max(W_A, W_A') / Gamma^2 samples, W the
        per-sample variance of the difference-in-means slope estimator.
        n -> infinity as t1 -> t0; the minimum over t1 is the acquisition price.

PART E  ADVERSE CHECKS.  A check that can never return False is not a check.
        E1 the floor must be breakable: Gamma != 0 off the incumbent reference.
        E2 the floor must not be an information floor: per-sample Gaussian KL
           between the two fixed worlds at t1 = t0 is strictly positive, so a
           full-likelihood analyst identifies A at t1 = t0 at finite cost.
        E3 the floor must not be an artifact of first-order readout alone: the
           SECOND-order response at t1 = t0 is computed and priced in the same
           sample unit.  If it is finite, the reference move is not the only way
           (and maybe not the cheapest way) to break the floor, and the headline
           must be restricted to the first-order readout class.

Exact Fraction arithmetic everywhere except the final sample counts and KLs,
where the float residual of the underlying exact quantity is reported.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, math, os, sys
from fractions import Fraction as Fr

PROTOCOL_VERSION = "master_reference_contrast_v2"
Z = 1.959963984540054          # two-sided 5% normal quantile
ZSUM2 = (2 * Z) ** 2           # (z_alpha + z_beta)^2 with alpha = beta = 2.5% one-sided


# =====================================================================  D6 algebra
def slopes_ab(alpha, beta, t):
    """(a, b, c) for |A|=alpha, |B|=beta, one z coordinate."""
    c = (1 - t) ** (alpha + beta - 1)
    return c * (1 + (beta - 1) * t), (beta - 1) * t * c, c


def pieces(k, t, rho):
    a, b, c = slopes_ab(k, k - 1, t)
    return a, b, a - b, rho - 2 * b, 2 * a - rho, min(a, 2 * b)


def pos(x):
    return x if x > 0 else Fr(0)


def V_formula(k, t, rho):
    """The published algebraic minimax value.  Asserted by the source ONLY where
    (k-2)b >= 1; evaluating it elsewhere is an extrapolation and is labelled."""
    a, b, cg, p, r, e = pieces(k, t, rho)
    return pos(k * r - e) * (p * (k - 1) + pos(e - r)) / (4 * cg * (k - 1))


def in_regime(k, t, rho):
    return (k - 2) * pieces(k, t, rho)[1] >= 1


# =====================================================  PART A: audit the "price"
def audit(artifact_path, scan_points=512, bisect_steps=48):
    with open(artifact_path) as f:
        art = json.load(f)
    ks = art["grid"]["ks"]
    rhos = [Fr(x) for x in art["grid"]["rhos"]]
    coarse = sorted(Fr(x) for x in art["grid"]["ts"])
    # fine dyadic scan of (0, 1/2]
    scan = [Fr(i, 2 * scan_points) for i in range(1, scan_points + 1)]

    rows = []
    for k in ks:
        for rho in rhos:
            pub = None
            for r in art["price_of_evidence_B"]:
                if r["k"] == k and Fr(r["rho"]) == rho:
                    pub = r["cheapest_t_that_kills_floor"]
            in_reg = [t for t in coarse if in_regime(k, t, rho)]
            dead = [V_formula(k, t, rho) == 0 for t in scan]
            flips = [(scan[i], scan[i + 1]) for i in range(len(scan) - 1)
                     if dead[i] != dead[i + 1]]
            # certified bracket for the FIRST alive -> dead transition
            bracket = None
            if flips and not dead[0]:
                lo, hi = flips[0]
                for _ in range(bisect_steps):
                    m = (lo + hi) / 2
                    if V_formula(k, m, rho) == 0:
                        hi = m
                    else:
                        lo = m
                assert V_formula(k, lo, rho) != 0 and V_formula(k, hi, rho) == 0
                bracket = (lo, hi)
            t_cross = bracket[1] if bracket else None
            row = {
                "k": k, "rho": str(rho),
                "published_cheapest_t_that_kills_floor": pub,
                "coarse_grid_in_regime": [str(t) for t in in_reg],
                "smallest_in_regime_coarse_t": str(min(in_reg)) if in_reg else None,
                "algebraic_V_dead_at_smallest_scan_t": bool(dead[0]),
                "n_sign_changes_on_fine_scan": len(flips),
                "algebraic_V_dead_at_EVERY_scanned_t": bool(all(dead)),
                "algebraic_V_alive_at_EVERY_scanned_t": bool(not any(dead)),
                "crossing_bracket": [str(bracket[0]), str(bracket[1])] if bracket else None,
                "crossing_float": float(t_cross) if t_cross is not None else None,
            }
            if pub is not None:
                pf = Fr(pub)
                row["published_equals_smallest_in_regime_coarse_t"] = bool(
                    in_reg and pf == min(in_reg))
                row["published_is_grid_left_endpoint"] = bool(pf == min(coarse))
                if t_cross is not None:
                    row["published_over_crossing_factor"] = float(pf / t_cross)
                    row["crossing_is_below_the_regime_window"] = bool(
                        in_reg and t_cross < min(in_reg))
                    row["published_strictly_above_crossing"] = bool(pf > t_cross)
            rows.append(row)

    pubrows = [r for r in rows if r["published_cheapest_t_that_kills_floor"] is not None]
    summary = {
        "cells": len(rows),
        "cells_with_a_published_price": len(pubrows),
        "published_price_equals_smallest_in_regime_coarse_t":
            sum(bool(r.get("published_equals_smallest_in_regime_coarse_t")) for r in pubrows),
        "published_price_strictly_above_the_algebraic_crossing":
            sum(bool(r.get("published_strictly_above_crossing")) for r in pubrows),
        "cells_where_the_crossing_lies_BELOW_the_certified_regime_window":
            sum(bool(r.get("crossing_is_below_the_regime_window")) for r in pubrows),
        "max_published_over_crossing_factor":
            max([r["published_over_crossing_factor"] for r in pubrows
                 if r.get("published_over_crossing_factor") is not None] or [None]),
        "cells_with_more_than_one_sign_change": sum(
            1 for r in rows if r["n_sign_changes_on_fine_scan"] > 1),
        "fine_scan": f"t = i/{2 * scan_points}, i = 1..{scan_points} (deliberate truncation to (0,1/2])",
        "bisection_steps": bisect_steps,
        "extrapolation_warning": "V_formula is asserted by the source only where (k-2)b>=1; "
                                 "the fine scan evaluates it everywhere and every cell where "
                                 "that matters is flagged by crossing_is_below_the_regime_window",
    }
    return {"summary": summary, "rows": rows}


# =====================================================  PART B/C: the fixed world
class World:
    """F_{A,t0} built ONCE at t0.  Exact rationals."""

    def __init__(self, alpha, beta, t0, rho, A, T):
        self.alpha, self.beta = alpha, beta
        self.n = alpha + beta + 1
        self.z = self.n - 1
        self.A = frozenset(A)
        self.B = frozenset(range(self.n - 1)) - self.A
        self.T = frozenset(T)
        self.t0, self.rho = t0, rho
        assert len(self.A) == alpha and len(self.B) == beta and self.z not in self.T
        self.cube = list(itertools.product((0, 1), repeat=self.n))
        self.g = [self._gate(x) for x in self.cube]
        self.Eg0 = self._expect(self.g, t0)
        self.s0 = [self._slope(self.g, t0, i) for i in range(self.n)]
        self.coef = [rho * (1 if i in self.T else 0) - self.s0[i] for i in range(self.n)]
        self.F = [self.g[m] - self.Eg0
                  + sum(self.coef[i] * (Fr(x[i]) - t0) for i in range(self.n))
                  for m, x in enumerate(self.cube)]

    # gate, transcribed from LeanD6ThresholdConstructionV1.lean
    def _gate(self, x):
        if x[self.z] == 1:
            return Fr(0)
        if any(x[i] for i in self.A):
            return Fr(1)
        return Fr(1) if sum(x[j] for j in self.B) >= 2 else Fr(0)

    def _w(self, x, t, skip=()):
        w = Fr(1)
        for i, xi in enumerate(x):
            if i in skip:
                continue
            w *= t if xi == 1 else (1 - t)
        return w

    def _expect(self, vals, t):
        return sum(self._w(x, t) * vals[m] for m, x in enumerate(self.cube))

    def _slope(self, vals, t, i):
        """E[val | X_i=1] - E[val | X_i=0] under the product reference."""
        hi = sum(self._w(x, t, skip=(i,)) * vals[m]
                 for m, x in enumerate(self.cube) if x[i] == 1)
        lo = sum(self._w(x, t, skip=(i,)) * vals[m]
                 for m, x in enumerate(self.cube) if x[i] == 0)
        return hi - lo

    # ---- readouts of the FIXED world at an arbitrary query reference t1
    def response(self, t1, i):
        return self._slope(self.F, t1, i)

    def cond_moments(self, t1, i):
        out = {}
        for u in (0, 1):
            m1 = m2 = Fr(0)
            for m, x in enumerate(self.cube):
                if x[i] != u:
                    continue
                w = self._w(x, t1, skip=(i,))
                y = self.F[m]
                m1 += w * y
                m2 += w * y * y
            out[u] = (m1, m2 - m1 * m1)
        return out

    def cond_moments2(self, t1, i, j):
        out = {}
        for u in (0, 1):
            for v in (0, 1):
                m1 = m2 = Fr(0)
                for m, x in enumerate(self.cube):
                    if x[i] != u or x[j] != v:
                        continue
                    w = self._w(x, t1, skip=(i, j))
                    y = self.F[m]
                    m1 += w * y
                    m2 += w * y * y
                out[(u, v)] = (m1, m2 - m1 * m1)
        return out


def make_pair(k, t0, rho, alpha=None, beta=None):
    """Two fixed worlds built at the SAME t0, differing by one swapped coordinate."""
    al = k if alpha is None else alpha
    be = (k - 1) if beta is None else beta
    n = al + be + 1
    nonz = list(range(n - 1))
    T = frozenset(range(min(k, n - 1)))
    A = frozenset(nonz[:al])
    i = max(A)                                   # swapped-out, will be in A then in B
    ip = min(set(nonz) - A)                      # swapped-in
    A2 = (A - {i}) | {ip}
    return World(al, be, t0, rho, A, T), World(al, be, t0, rho, A2, T), i, ip


def verify_law(k, t0, rho, t1s, alpha=None, beta=None):
    W, _, _, _ = make_pair(k, t0, rho, alpha, beta)
    al, be = W.alpha, W.beta
    a0, b0, c0 = slopes_ab(al, be, t0)
    checks = []
    # B0: the raw gate slopes at the incumbent reference
    gate_ok = (all(W.s0[i] == a0 for i in W.A)
               and all(W.s0[j] == b0 for j in W.B)
               and W.s0[W.z] == a0 - 1)
    for t1 in t1s:
        a1, b1, c1 = slopes_ab(al, be, t1)
        d = {i: W.response(t1, i) - rho * (1 if i in W.T else 0) for i in range(W.n)}
        gam = d[min(W.A)] - d[min(W.B)]
        checks.append({
            "t1": str(t1),
            "A_coords_ok": all(d[i] == a1 - a0 for i in W.A),
            "B_coords_ok": all(d[j] == b1 - b0 for j in W.B),
            "z_coord_ok": d[W.z] == a1 - a0,
            "Gamma": str(gam),
            "Gamma_eq_c(t1)-c(t0)": bool(gam == c1 - c0),
            "Gamma_is_zero": bool(gam == 0),
            "t1_eq_t0": bool(t1 == t0),
        })
    return {"k": k, "alpha": al, "beta": be, "n_coords": W.n, "t0": str(t0),
            "rho": str(rho), "gate_slopes_at_t0_match_closed_form": bool(gate_ok),
            "checks": checks,
            "all_pass": bool(gate_ok and all(
                c["A_coords_ok"] and c["B_coords_ok"] and c["z_coord_ok"]
                and c["Gamma_eq_c(t1)-c(t0)"]
                and (c["Gamma_is_zero"] == c["t1_eq_t0"]) for c in checks))}


# ==========================================================  PART D: the cost curve
def first_order_cost(WA, WB, i, t1, sigma):
    """Samples for the two-point test 'i in A' vs 'i in B' from Delta_i at reference t1."""
    a1, b1, _ = slopes_ab(WA.alpha, WA.beta, t1)
    a0, b0, _ = slopes_ab(WA.alpha, WA.beta, WA.t0)
    gap = (a1 - a0) - (b1 - b0)
    if gap == 0:
        return {"t1": str(t1), "Gamma": 0.0, "n_samples": None,
                "note": "floor: contrast exactly zero"}
    Ws = []
    for W in (WA, WB):
        cm = W.cond_moments(t1, i)
        Ws.append((cm[1][1] + sigma ** 2) / t1 + (cm[0][1] + sigma ** 2) / (1 - t1))
    Wv = max(Ws)
    n = ZSUM2 * float(Wv) / float(gap) ** 2
    return {"t1": str(t1), "t1_f": float(t1), "Gamma": float(gap),
            "Gamma_exact": str(gap), "per_sample_var_max": float(Wv),
            "n_samples": n}


def second_order_cost(WA, WB, i, j, t1, sigma):
    """Samples for the same two-point test from the SECOND-order response at t1."""
    cmA, cmB = WA.cond_moments2(t1, i, j), WB.cond_moments2(t1, i, j)

    def d2(cm):
        return cm[(1, 1)][0] - cm[(1, 0)][0] - cm[(0, 1)][0] + cm[(0, 0)][0]

    gap = d2(cmA) - d2(cmB)
    if gap == 0:
        return {"pair": [i, j], "gap": 0.0, "n_samples": None}
    Ws = []
    for cm in (cmA, cmB):
        tot = Fr(0)
        for (u, v), (_m, var) in cm.items():
            p = (t1 if u else 1 - t1) * (t1 if v else 1 - t1)
            tot += (var + sigma ** 2) / p
        Ws.append(tot)
    n = ZSUM2 * float(max(Ws)) / float(gap) ** 2
    return {"pair": [i, j], "gap": float(gap), "gap_exact": str(gap),
            "per_sample_var_max": float(max(Ws)), "n_samples": n}


def full_likelihood_cost(WA, WB, t1, sigma):
    """Two-point test on the log-likelihood ratio, in the SAME units as the
    first- and second-order tests.

    With Y = F(X) + N(0,sigma^2) and D(x) = F_A(x) - F_A'(x),
        logLR = (D^2 + 2 D N) / (2 sigma^2),
        E[logLR | H_A] = +E[D^2]/(2 sigma^2) = +KL,  E[.. | H_A'] = -KL,
        Var[logLR] = Var(D^2)/(4 sigma^4) + E[D^2]/sigma^2   (both hypotheses).
    Separation of the means is 2*KL, so n = (z_a+z_b)^2 * Var / (2 KL)^2.
    """
    d1 = d2m = Fr(0)
    for m, x in enumerate(WA.cube):
        w = WA._w(x, t1)
        d = (WA.F[m] - WB.F[m]) ** 2
        d1 += w * d
        d2m += w * d * d
    var_d2 = d2m - d1 * d1
    kl = d1 / (2 * sigma ** 2)
    if kl == 0:
        return {"E[D^2]": 0.0, "per_sample_KL": 0.0, "n_samples": None}
    var_llr = var_d2 / (4 * sigma ** 4) + d1 / sigma ** 2
    n = ZSUM2 * float(var_llr) / (2 * float(kl)) ** 2
    return {"E[D^2]": float(d1), "E[D^2]_exact": str(d1),
            "per_sample_KL": float(kl), "per_sample_var_logLR": float(var_llr),
            "n_samples": n}


def first_moment_only_check(WA, WB, i, t1, sigma):
    """Is the floor a fact about the first-order RESPONSE, or about the whole
    first-order statistic?  At t1 = t0 the two worlds give the same conditional
    MEANS at coordinate i; if their conditional VARIANCES differ, a second-moment
    test on the very same readout still separates them and the floor is a
    first-MOMENT floor only."""
    cmA, cmB = WA.cond_moments(t1, i), WB.cond_moments(t1, i)
    means_equal = (cmA[1][0] - cmA[0][0]) == (cmB[1][0] - cmB[0][0])
    out = {"conditional_means_agree": bool(means_equal),
           "var_gap_u1": str(cmA[1][1] - cmB[1][1]),
           "var_gap_u0": str(cmA[0][1] - cmB[0][1]),
           "conditional_variances_agree": bool(cmA[1][1] == cmB[1][1]
                                               and cmA[0][1] == cmB[0][1])}
    # price the variance-contrast statistic  Vhat(u=1) - Vhat(u=0)  crudely:
    # a sample variance has variance (mu4 - var^2)/n_u; we use the Gaussian-noise
    # surrogate 2*(var+sigma^2)^2 as an upper bound on mu4 - var^2 only when the
    # conditional law is Gaussian, which it is NOT here, so this is reported as an
    # ORDER-OF-MAGNITUDE figure and labelled as such.
    gap = (cmA[1][1] - cmA[0][1]) - (cmB[1][1] - cmB[0][1])
    out["variance_contrast_gap"] = str(gap)
    out["variance_contrast_gap_f"] = float(gap)
    if gap != 0:
        wv = max(2 * (cm[u][1] + sigma ** 2) ** 2 / (t1 if u else 1 - t1)
                 for cm in (cmA, cmB) for u in (0, 1))
        out["n_samples_order_of_magnitude"] = ZSUM2 * float(wv) / float(gap) ** 2
        out["n_samples_caveat"] = ("Gaussian-kurtosis surrogate for a NON-Gaussian "
                                   "conditional law; order of magnitude only, not a bound")
    return out


def cost_case(k, t0, rho, sigma, t1_grid):
    WA, WB, i, ip = make_pair(k, t0, rho)
    curve = [first_order_cost(WA, WB, i, t1, sigma) for t1 in t1_grid]
    live = [r for r in curve if r["n_samples"] is not None]
    best = min(live, key=lambda r: r["n_samples"])
    on_grid = any(r["n_samples"] is None for r in curve)

    # E2: full-likelihood channel at the INCUMBENT reference, same test units
    full = full_likelihood_cost(WA, WB, t0, sigma)

    # E3: second-order readout at the INCUMBENT reference
    so_named = second_order_cost(WA, WB, i, ip, t0, sigma)
    so_z = second_order_cost(WA, WB, i, WA.z, t0, sigma)
    so_all = [second_order_cost(WA, WB, i, j, t0, sigma)
              for j in range(WA.n) if j != i]
    so_live = [r for r in so_all if r["n_samples"] is not None]
    so_best = min(so_live, key=lambda r: r["n_samples"]) if so_live else None

    # E4: is the floor first-MOMENT only?
    fm = first_moment_only_check(WA, WB, i, t0, sigma)

    return {
        "k": k, "n_coords": WA.n, "t0": str(t0), "rho": str(rho), "sigma": str(sigma),
        "swap": [i, ip], "i_in_T": bool(i in WA.T),
        "c_t0": float((1 - t0) ** (2 * k - 2)),
        "t0_is_on_the_query_grid": bool(on_grid),
        "floor_at_t1_eq_t0": "Gamma = 0 exactly -> no finite sample size",
        "argmin_t1": best["t1"], "argmin_t1_f": best["t1_f"],
        "Gamma_at_argmin": best["Gamma"],
        "min_samples_first_order": best["n_samples"],
        "argmin_is_interior": bool(min(t1_grid) < Fr(best["t1"]) < max(t1_grid)),
        "E2_full_likelihood_at_t0": dict(
            full, floor_is_informational=bool(full["n_samples"] is None)),
        "E3_second_order_at_t0": {
            "pair_(i,i')_no_oracle": so_named,
            "pair_(i,z)_no_oracle": so_z,
            "best_pair_oracle_choice": so_best,
            "floor_survives_second_order_readout": bool(so_best is None)},
        "E4_first_moment_only": fm,
        "ratio_second_order_over_reference_move": (
            so_z["n_samples"] / best["n_samples"]
            if so_z["n_samples"] is not None else None),
        "curve": curve,
    }


# ==================================================================== driver
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--overwrite", action="store_true")
    ap.add_argument("--artifact",
                    default="research/master_reference_20260912/"
                            "master_reference_phase_certificates_v1.json")
    ap.add_argument("--scan-points", type=int, default=512)
    a = ap.parse_args()
    if os.path.exists(a.out) and not a.overwrite:
        sys.exit(f"refusing to overwrite {a.out}; pass --overwrite")

    out = {"protocol_version": PROTOCOL_VERSION,
           "arithmetic": "exact Fraction for every response, contrast, variance and KL; "
                         "float only for sample counts, KL printouts and ratios",
           "scope_truncation": "full-cube enumeration is 2^(alpha+beta+1), so PART B/C/D/E "
                               "run at k in {3,4,5} (64/256/1024 cube points) only. "
                               "No claim is made for large k. PART A runs on the "
                               "published grid k in {6,...,64}."}

    out["partA_price_audit"] = audit(a.artifact, a.scan_points)

    t1s = [Fr(0), Fr(1, 16), Fr(1, 8), Fr(1, 4), Fr(1, 3), Fr(1, 2), Fr(3, 4)]
    law = []
    for k in (3, 4, 5):
        for t0 in (Fr(1, 8), Fr(1, 4)):
            for rho in (Fr(1), Fr(3, 2)):
                law.append(verify_law(k, t0, rho, sorted(set(t1s) | {t0})))
    out["partB_response_law_construction_blocks"] = {
        "cases": len(law), "all_pass": all(c["all_pass"] for c in law), "detail": law}

    law2 = [verify_law(3, Fr(1, 8), Fr(1), sorted(set(t1s) | {Fr(1, 8)}),
                       alpha=al, beta=be)
            for (al, be) in ((3, 2), (4, 2), (2, 4), (4, 3), (2, 2))]
    out["partB_response_law_decoupled_blocks"] = {
        "closed_form_tested": "a=(1-t)^(alpha+beta-1)(1+(beta-1)t), "
                              "b=(beta-1)t(1-t)^(alpha+beta-1), c=a-b=(1-t)^(alpha+beta-1)",
        "cases": len(law2), "all_pass": all(c["all_pass"] for c in law2), "detail": law2}

    grid = [Fr(i, 32) for i in range(1, 32)]
    costs = []
    for k in (3, 4, 5):
        for t0 in (Fr(1, 8), Fr(1, 4)):
            for sigma in (Fr(1, 10),):
                costs.append(cost_case(k, t0, Fr(1), sigma, grid))
    out["partD_cost"] = {
        "world": "F_{A,t0} built once at t0 and never recompensated",
        "query": "one i.i.d. draw X ~ Bernoulli(t1)^n; observe Y = F_{A,t0}(X) + N(0,sigma^2)",
        "coordinate_observed": "the full bit vector X and the scalar Y; the readout used is "
                               "the first-order response Delta_i = E[Y|X_i=1]-E[Y|X_i=0]",
        "cost_unit": "number of draws n (a sample count, not t)",
        "test": "two-point test between the fixed worlds F_{A,t0} and F_{A',t0}, "
                "A' = A with coordinate i swapped for i'; type-I = type-II = 2.5% one-sided; "
                f"n = {ZSUM2:.6f} * max(W_A, W_A') / Gamma^2",
        "query_grid": "t1 = i/32, i = 1..31 (deliberately coarse; t0 lies on it)",
        "cases": costs}

    # --------- console
    s = out["partA_price_audit"]["summary"]
    print("=== PART A: audit of price_of_evidence_B ===")
    for kk, vv in s.items():
        print(f"  {kk}: {vv}")
    print("\n  k  rho   published  smallest-in-regime  algebraic crossing   pub/cross")
    for r in out["partA_price_audit"]["rows"]:
        if r["published_cheapest_t_that_kills_floor"] is None:
            continue
        print(f"  {r['k']:>2} {r['rho']:>5} {r['published_cheapest_t_that_kills_floor']:>10}"
              f" {str(r['smallest_in_regime_coarse_t']):>18}"
              f" {r['crossing_float']:>18.8f}"
              f" {r.get('published_over_crossing_factor', float('nan')):>10.3f}")

    print("\n=== PART B: response law from the Lean gate (exact) ===")
    print(f"  construction blocks: {out['partB_response_law_construction_blocks']['cases']} cases,"
          f" all_pass={out['partB_response_law_construction_blocks']['all_pass']}")
    print(f"  decoupled blocks   : {out['partB_response_law_decoupled_blocks']['cases']} cases,"
          f" all_pass={out['partB_response_law_decoupled_blocks']['all_pass']}")

    print("\n=== PART D/E: fixed-world acquisition cost, in samples ===")
    print(f"{'k':>2} {'t0':>5} {'t1*':>6} {'Gamma*':>11} {'n1st*':>12} {'n2nd(i,z)@t0':>13}"
          f" {'nLLR@t0':>10} {'interior':>9} {'varsAgree':>10}")
    for c in costs:
        so = c["E3_second_order_at_t0"]["pair_(i,z)_no_oracle"]["n_samples"]
        print(f"{c['k']:>2} {c['t0']:>5} {c['argmin_t1']:>6} {c['Gamma_at_argmin']:>11.6f}"
              f" {c['min_samples_first_order']:>12.1f}"
              f" {(so if so is not None else float('nan')):>13.1f}"
              f" {c['E2_full_likelihood_at_t0']['n_samples']:>10.2f}"
              f" {str(c['argmin_is_interior']):>9}"
              f" {str(c['E4_first_moment_only']['conditional_variances_agree']):>10}")

    with open(a.out, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True)
    h = hashlib.sha256(open(a.out, "rb").read()).hexdigest()
    with open(a.out + ".manifest.json", "w") as f:
        json.dump({"protocol_version": PROTOCOL_VERSION,
                   "artifact": os.path.basename(a.out), "sha256": h,
                   "bytes": os.path.getsize(a.out)}, f, indent=1)
    print(f"\nwrote {a.out}\nsha256 {h}")


if __name__ == "__main__":
    main()
