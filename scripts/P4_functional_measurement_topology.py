#!/usr/bin/env python3
"""Functional batch-2 package: when does the SETUP cost of opening a measurement
type change the TOPOLOGY of the optimal design -- not just the sampling ratios?

THE COST MODEL, and the reason it is not invented for novelty.  Opening a
measurement type costs kappa once (calibrating an instrument, standing up a probe),
then each sample costs one unit of budget.  With a total budget T,
    I_T = max over S with kappa|S| < T of  (T - kappa|S|) Gamma(S),
    Gamma(S) = sup_{w in Delta(S)} inf_{lambda: TopC(lambda) != TopC(theta)}
               sum_{e in S} w_e KL_e(theta, lambda).
For Gaussian contrasts this inner problem is EXACTLY an effective-resistance
problem: with v = e_{i*} - e_j,
    inf over the hyperplane theta_{i*} = theta_j  of  sum_e w_e (c_e^T u)^2/(2 sig_e^2)
      = Delta_j^2 / (2 v^T M(w)^+ v),
and v^T M^+ v is the effective resistance between i* and j.  Resistance is CONVEX in
the conductances, so max_w min_j is a concave programme with an analytic gradient
(dR_j/dw_e = -(v_j^T M^+ c_e)^2/sig_e^2).  `F8_contrast_graph_phases.py` already has
that solver and it is IMPORTED here rather than rewritten.

WHAT IS NEW, and two corrections to the brief.
  * CORRECTION 1.  D^2/(2(K-1)) and D^2/(4(K-1)) are the values at the UNIFORM
    allocation, not Gamma, which is a SUPREMUM over w.  Both uniform numbers are
    reproduced exactly here, and both are strictly below the true Gamma of their
    support: on the complete graph the optimum is not uniform.  At K = 3 the
    optimum puts (1 - 1/sqrt 3)/... more weight on the two top edges and gives
    Gamma = 2 - sqrt 3 = 0.2679... against the uniform 0.25; at K = 4 it gives
    3/16 = 0.1875 against the uniform 1/6.  So the quoted crossover
    T = kappa (K-1)^2 is computed from two understated values and is not the
    crossover of the actual designs.
  * CORRECTION 2.  The star in D^2/(4(K-1)) is centred at a NON-top node.  The
    star centred AT the top arm has R_eff(i*,j) = 1/w = K-1 for every j, so
        Gamma_{star at top} = D^2/(2(K-1))  --  with K-1 edges, not K(K-1)/2,
    and it is the uniform allocation that is optimal there.  It therefore buys the
    brief's whole "complete graph" value at a fraction of the setup cost.  The
    complete graph is still not dominated, because its true Gamma is larger; the
    real frontier is computed in PART 2.
  * Every support on K = 3, 4 is enumerated (contrasts and cell observations), the
    allocation inside each support is solved, and the frontier over T/kappa is
    tabulated with the exact crossovers between consecutive winners.
  * The SYMMETRIC baseline is optimised in full under the SAME setup cost -- the
    best design invariant under permuting the non-top arms -- so "asymmetric wins"
    is a comparison against the best symmetric design, not against a symmetric
    allocation borrowed from the cost-free problem.
  * A second cost model in which a contrast is REALISED as two independent scalar
    reads (2 samples, variance 2) is run separately, since in that model a contrast
    is not a primitive and the topology can differ.
  * Integer rounding of sample counts is applied at the end and the loss reported.
  * A non-flat instance is run with the FULL extrema oracle: the answer is the pair
    (argmax, argmin) and every alternative that changes EITHER extremum is used --
    not pair-flips at the original extrema only.

WHAT THIS DOES NOT ESTABLISH.
  * Floating point throughout; supports are read at a tolerance and the frontier is
    a grid of T/kappa, not solved-for boundaries except where a closed form is given.
  * Known variances, static design, information rate per unit budget -- not a
    sample-complexity theorem.
  * The setup-cost model is an assumption.  If no real instrument cost justifies it,
    this branch should be dropped; nothing here argues that it must exist.

    .venv/bin/python scripts/P4_functional_measurement_topology.py
"""
from __future__ import annotations

import importlib.util, itertools, json, math
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "f8", REPO / "scripts/F8_contrast_graph_phases.py")
f8 = importlib.util.module_from_spec(spec); spec.loader.exec_module(f8)


def all_measurements(K, contrast_sigma2=1.0, contrast_samples=1):
    out = []
    for a, b in itertools.combinations(range(K), 2):
        c = np.zeros(K); c[a] = 1.0; c[b] = -1.0
        out.append((("contrast", a, b), c, contrast_sigma2, contrast_samples))
    for a in range(K):
        c = np.zeros(K); c[a] = 1.0
        out.append((("cell", a), c, 1.0, 1))
    return out


_GCACHE = {}


def gamma_of(sub, theta, istar, alt_pairs, starts=5):
    key = (tuple(sorted(str(m[0]) + str(m[2]) for m in sub)),
           tuple(np.round(theta, 12)), istar, tuple(alt_pairs), starts)
    if key in _GCACHE:
        return _GCACHE[key]
    out = _gamma_of(sub, theta, istar, alt_pairs, starts)
    _GCACHE[key] = out
    return out


def _gamma_of(sub, theta, istar, alt_pairs, starts=5):
    """Gamma(S) by the concave resistance programme on the restricted support."""
    meas = [(lab, c, 0) for lab, c, _s, _n in sub]
    sig2 = {lab: s for lab, _c, s, _n in sub}
    kappa = {lab: 1.0 for lab, _c, _s, _n in sub}
    v, x = _solve(meas, sig2, theta, istar, kappa, alt_pairs, starts)
    return v, x


def _solve(meas, sig2, theta, istar, kappa, alt_pairs, starts):
    """F8's solver, with the alternative set passed in so a FULL extrema oracle can
    be used instead of Top-1 flips."""
    from scipy.optimize import minimize
    n, K = len(meas), len(theta)
    if n == 0:
        return 0.0, None
    kap = np.array([kappa[lab] for lab, _c, _d in meas])
    C = np.array([c for _lab, c, _d in meas])
    inv = np.array([1.0 / sig2[lab] for lab, _c, _d in meas])
    V, D2 = [], []
    for (i, j) in alt_pairs:
        v = np.zeros(K); v[i] = 1.0; v[j] = -1.0
        V.append(v); D2.append((theta[i] - theta[j]) ** 2)
    V = np.array(V); D2 = np.array(D2)

    def resist_and_grad(x):
        M = (C * (x * inv)[:, None]).T @ C
        Mp = np.linalg.pinv(M, rcond=1e-12)
        if np.linalg.norm(M @ (Mp @ V.T) - V.T) > 1e-6:
            return None, None
        R = np.einsum('ij,jk,ik->i', V, Mp, V)
        W = V @ Mp @ C.T
        return R, -(W ** 2) * inv[None, :]

    def val(x):
        R, _ = resist_and_grad(np.maximum(x, 1e-15))
        if R is None or np.any(R <= 0):
            return 0.0
        return float(np.min(D2 / (2.0 * R)))

    def cons_f(z):
        R, _ = resist_and_grad(np.maximum(z[:n], 1e-12))
        if R is None:
            return -np.ones(len(V))
        return z[n] - 2.0 * R / D2

    def cons_j(z):
        _, G = resist_and_grad(np.maximum(z[:n], 1e-12))
        J = np.zeros((len(V), n + 1))
        if G is not None:
            J[:, :n] = -2.0 * G / D2[:, None]
        J[:, n] = 1.0
        return J

    cons = [{"type": "ineq", "fun": cons_f, "jac": cons_j},
            {"type": "ineq", "fun": lambda z: 1.0 - float(kap @ z[:n]),
             "jac": lambda z: np.concatenate([-kap, [0.0]])}]
    bnds = [(1e-9, None)] * n + [(1e-12, None)]
    rng = np.random.default_rng(20260914)
    best = (0.0, None)
    for s_i in range(starts):
        x0 = np.ones(n) if s_i == 0 else np.abs(rng.standard_normal(n)) + 0.05
        x0 = x0 / float(kap @ x0)
        R0, _ = resist_and_grad(x0)
        if R0 is None:
            continue
        z0 = np.concatenate([x0, [float(np.max(2.0 * R0 / D2)) + 1e-6]])
        try:
            r = minimize(lambda z: z[n], z0, jac=lambda z: np.eye(n + 1)[n],
                         constraints=cons, bounds=bnds, method="SLSQP",
                         options={"maxiter": 400, "ftol": 1e-14})
        except Exception:
            continue
        x = np.maximum(r.x[:n], 0.0)
        s = float(kap @ x)
        if s <= 0:
            continue
        x = x / s
        v = val(x)
        if v > best[0]:
            best = (v, x)
    return best


def top1_alts(K, istar):
    return [(istar, j) for j in range(K) if j != istar]


def extrema_alts(theta):
    """FULL extrema oracle: the answer is (argmax, argmin); every alternative that
    changes EITHER extremum is a boundary, so every ordered pair (i,j) with
    theta_i > theta_j and (i is the max or j is the min) has to be separated."""
    K = len(theta)
    imax = int(np.argmax(theta)); imin = int(np.argmin(theta))
    out = []
    for j in range(K):
        if j != imax:
            out.append((imax, j))
    for j in range(K):
        if j != imin:
            out.append((j, imin))
    return sorted(set(out))


def main():
    print("Functional: setup cost, and the TOPOLOGY of the optimal design\n")
    res = {}

    print("PART 1 -- the brief's two formulas are UNIFORM values, not Gamma")
    p1 = []
    for K in (3, 4, 5, 6):
        theta = np.zeros(K); theta[0] = 1.0
        D2 = 1.0
        alts = top1_alts(K, 0)
        full = all_measurements(K)
        contrasts = [m for m in full if m[0][0] == "contrast"]
        star_top = [m for m in contrasts if 0 in m[0][1:]]
        star_off = [m for m in contrasts if 1 in m[0][1:]]

        def uniform_value(sub):
            meas = [(lab, c, 0) for lab, c, _s, _n in sub]
            sig2 = {lab: sg for lab, _c, sg, _n in sub}
            w = np.ones(len(sub)) / len(sub)
            return f8.value(w, meas, sig2, theta, 0)

        uc, ust, uso = (uniform_value(contrasts), uniform_value(star_top),
                        uniform_value(star_off))
        gc, _ = gamma_of(contrasts, theta, 0, alts, starts=8)
        gst, _ = gamma_of(star_top, theta, 0, alts, starts=8)
        gso, _ = gamma_of(star_off, theta, 0, alts, starts=8)
        pred_c = D2 / (2 * (K - 1)); pred_off = D2 / (4 * (K - 1))
        # the brief's two formulas ARE the uniform values -- checked
        for nm, got, pred in (("complete, uniform w", uc, pred_c),
                              ("star off-top, uniform w", uso, pred_off)):
            if abs(got - pred) > 1e-9 * max(1.0, pred):
                raise AssertionError(f"K={K} {nm}: {got} vs brief {pred}")
        # the star AT the top is the case where uniform IS optimal
        if abs(gst - pred_c) > 2e-6 * pred_c or abs(ust - pred_c) > 1e-9:
            raise AssertionError(f"K={K} star at top: {gst}/{ust} vs {pred_c}")
        if gc < pred_c - 1e-9:
            raise AssertionError("optimal allocation below uniform -- solver bug")
        print(f"   K={K}: complete graph ({len(contrasts)} edges)  uniform "
              f"{uc:.9f} = D^2/(2(K-1)),  OPTIMAL {gc:.9f}"
              f"   ({100*(gc/uc-1):+.2f}%)")
        print(f"        star at TOP  ({len(star_top)} edges)  uniform {ust:.9f}"
              f" = OPTIMAL {gst:.9f}  -- same value as the brief's Gamma_complete")
        print(f"        star off-top ({len(star_off)} edges)  uniform {uso:.9f}"
              f" = D^2/(4(K-1)),  OPTIMAL {gso:.9f}")
        p1.append({"K": K,
                   "complete_uniform": uc, "complete_optimal": gc,
                   "edges_complete": len(contrasts),
                   "star_top_uniform": ust, "star_top_optimal": gst,
                   "edges_star": len(star_top),
                   "star_offtop_uniform": uso, "star_offtop_optimal": gso,
                   "brief_formula_complete": pred_c,
                   "brief_formula_star": pred_off,
                   "brief_matches_uniform_not_Gamma": True})
    res["closed_forms"] = p1
    k3 = [r for r in p1 if r["K"] == 3][0]
    if abs(k3["complete_optimal"] - (2 - math.sqrt(3))) > 1e-8:
        raise AssertionError("K=3 complete optimum is not 2 - sqrt 3")
    k4 = [r for r in p1 if r["K"] == 4][0]
    if abs(k4["complete_optimal"] - 3 / 16) > 1e-8:
        raise AssertionError("K=4 complete optimum is not 3/16")
    print("   K=3 complete optimum = 2 - sqrt(3) (to 1e-8); K=4 = 3/16 (to 1e-8)")
    print("   => the brief's Gamma_complete and Gamma_star are UNIFORM-allocation")
    print("      values; T = kappa (K-1)^2 is not the crossover of the designs.")

    print("\nPART 2 -- every support, and the frontier over T/kappa")
    p2 = {}
    for K in (3, 4):
        theta = np.zeros(K); theta[0] = 1.0
        alts = top1_alts(K, 0)
        full = all_measurements(K)
        rows = []
        for mask in range(1, 1 << len(full)):
            sub = [full[i] for i in range(len(full)) if mask >> i & 1]
            g, x = gamma_of(sub, theta, 0, alts, starts=3)
            if g <= 1e-9:
                continue
            rows.append({"support": [list(map(str, m[0])) for m in sub],
                         "size": len(sub), "Gamma": g})
        # frontier: for each T/kappa the maximiser of (T/kappa - |S|) Gamma(S)
        front = []
        prev = None
        for tk in [x / 4 for x in range(4, 400)]:
            feas = [r for r in rows if r["size"] < tk]
            if not feas:
                continue
            b = max(feas, key=lambda r: (tk - r["size"]) * r["Gamma"])
            key = tuple(tuple(s) for s in b["support"])
            if key != prev:
                front.append({"T_over_kappa_from": tk, "size": b["size"],
                              "Gamma": b["Gamma"],
                              "support": b["support"]})
                prev = key
        print(f"   K={K}: {len(rows)} separating supports out of {(1<<len(full))-1}; "
              f"{len(front)} regimes on the frontier")
        for fr in front:
            print(f"      T/kappa >= {fr['T_over_kappa_from']:.2f}: |S|={fr['size']} "
                  f"Gamma={fr['Gamma']:.6f}  {[tuple(s) for s in fr['support']]}")
        p2[str(K)] = {"n_separating_supports": len(rows), "frontier": front}
    res["frontier"] = p2

    print("\nPART 3 -- the best SYMMETRIC design under the same setup cost")
    p3 = []
    for K in (3, 4):
        theta = np.zeros(K); theta[0] = 1.0
        alts = top1_alts(K, 0)
        full = all_measurements(K)

        def orbit(lab):
            if lab[0] == "cell":
                return ("cell", "top" if lab[1] == 0 else "arm")
            a, b = lab[1], lab[2]
            return ("contrast", "top-arm" if 0 in (a, b) else "arm-arm")
        orbits = sorted({orbit(m[0]) for m in full})
        best_sym = None
        for r in range(1, len(orbits) + 1):
            for combo in itertools.combinations(orbits, r):
                sub = [m for m in full if orbit(m[0]) in combo]
                g, x = gamma_of(sub, theta, 0, alts, starts=3)
                if g <= 1e-9:
                    continue
                if best_sym is None or g > best_sym[0]:
                    best_sym = (g, combo, len(sub))
        # best OVERALL of any size, and best of the same size as the symmetric one
        allrows = []
        for mask in range(1, 1 << len(full)):
            sub = [full[i] for i in range(len(full)) if mask >> i & 1]
            g, _ = gamma_of(sub, theta, 0, alts, starts=3)
            if g > 1e-9:
                allrows.append((g, len(sub), [m[0] for m in sub]))
        for tk in (2.0, 4.0, 8.0, 20.0, 100.0):
            sym = max(((tk - s) * g, g, s, c)
                      for g, c, s in [(bs[0], bs[1], bs[2]) for bs in [best_sym]]
                      if s < tk) if best_sym[2] < tk else None
            symbest = None
            for r in range(1, len(orbits) + 1):
                for combo in itertools.combinations(orbits, r):
                    sub = [m for m in full if orbit(m[0]) in combo]
                    if len(sub) >= tk:
                        continue
                    g, _ = gamma_of(sub, theta, 0, alts, starts=3)
                    if g <= 1e-9:
                        continue
                    v = (tk - len(sub)) * g
                    if symbest is None or v > symbest[0]:
                        symbest = (v, g, len(sub), combo)
            anybest = None
            for g, s, lab in allrows:
                if s >= tk:
                    continue
                v = (tk - s) * g
                if anybest is None or v > anybest[0]:
                    anybest = (v, g, s, lab)
            if symbest is None or anybest is None:
                continue
            gain = anybest[0] / symbest[0] - 1
            print(f"   K={K} T/kappa={tk:g}: best symmetric I = {symbest[0]:.6f} "
                  f"(|S|={symbest[2]}, orbits {symbest[3]}); best overall "
                  f"{anybest[0]:.6f} (|S|={anybest[2]})  -> asymmetric gain "
                  f"{gain*100:+.3f}%")
            p3.append({"K": K, "T_over_kappa": tk,
                       "best_symmetric_I": symbest[0], "sym_size": symbest[2],
                       "sym_orbits": [list(o) for o in symbest[3]],
                       "best_overall_I": anybest[0], "overall_size": anybest[2],
                       "overall_support": [list(map(str, l)) for l in anybest[3]],
                       "asymmetric_relative_gain": gain})
    res["symmetric_baseline"] = p3

    print("\nPART 4 -- contrasts realised as TWO independent scalar reads")
    p4 = []
    for K in (3, 4):
        theta = np.zeros(K); theta[0] = 1.0
        alts = top1_alts(K, 0)
        # a contrast costs 2 samples and has variance 2: per unit of BUDGET it
        # delivers half the weight at twice the variance, i.e. conductance /4
        full = all_measurements(K, contrast_sigma2=4.0, contrast_samples=2)
        rows = []
        for mask in range(1, 1 << len(full)):
            sub = [full[i] for i in range(len(full)) if mask >> i & 1]
            g, _ = gamma_of(sub, theta, 0, alts, starts=3)
            if g > 1e-9:
                rows.append((g, len(sub), [m[0] for m in sub]))
        for tk in (4.0, 10.0, 40.0):
            b = max((r for r in rows if r[1] < tk), key=lambda r: (tk - r[1]) * r[0])
            print(f"   K={K} T/kappa={tk:g}: winner |S|={b[1]} Gamma={b[0]:.6f} "
                  f"{b[2]}")
            p4.append({"K": K, "T_over_kappa": tk, "size": b[1], "Gamma": b[0],
                       "support": [list(map(str, l)) for l in b[2]]})
    res["contrast_from_two_scalars"] = p4

    print("\nPART 5 -- a NON-FLAT instance with the FULL extrema oracle")
    p5 = []
    for K, th in ((3, [1.0, 0.4, 0.0]), (4, [1.0, 0.7, 0.3, 0.0]),
                  (4, [1.0, 0.95, 0.2, 0.0])):
        theta = np.array(th)
        alts = extrema_alts(theta)
        full = all_measurements(K)
        rows = []
        for mask in range(1, 1 << len(full)):
            sub = [full[i] for i in range(len(full)) if mask >> i & 1]
            g, _ = gamma_of(sub, theta, 0, alts, starts=3)
            if g > 1e-9:
                rows.append((g, len(sub), [m[0] for m in sub]))
        out = []
        for tk in (3.0, 5.0, 10.0, 30.0, 100.0):
            cand = [r for r in rows if r[1] < tk]
            if not cand:
                continue
            b = max(cand, key=lambda r: (tk - r[1]) * r[0])
            out.append({"T_over_kappa": tk, "size": b[1], "Gamma": b[0],
                        "support": [list(map(str, l)) for l in b[2]]})
        print(f"   theta={th}: alternatives {alts}")
        for o in out:
            print(f"      T/kappa={o['T_over_kappa']:g}: |S|={o['size']} "
                  f"Gamma={o['Gamma']:.6f}  {[tuple(s) for s in o['support']]}")
        p5.append({"K": K, "theta": th, "alternatives": [list(a) for a in alts],
                   "frontier": out})
    res["non_flat_full_extrema"] = p5

    print("\nPART 6 -- integer rounding of the sample counts")
    p6 = []
    K = 4
    theta = np.zeros(K); theta[0] = 1.0
    alts = top1_alts(K, 0)
    full = all_measurements(K)
    star = [m for m in full if m[0][0] == "contrast" and 0 in m[0][1:]]
    g, x = gamma_of(star, theta, 0, alts, starts=6)
    for T in (10, 20, 50, 100, 1000):
        n_cont = T - len(star)
        if n_cont <= 0:
            continue
        raw = x * n_cont
        n = np.floor(raw).astype(int)
        while n.sum() < n_cont:
            i = int(np.argmax(raw - n))
            n[i] += 1
        w = n / max(1, n.sum())
        meas = [(lab, c, 0) for lab, c, _s, _n in star]
        sig2 = {lab: s for lab, _c, s, _n in star}
        vi = f8.value(w, meas, sig2, theta, 0) * n.sum()
        vc = g * n_cont
        print(f"   T={T}: continuous {vc:.6f} vs integer {vi:.6f}  "
              f"(loss {100*(1-vi/vc):+.4f}%), counts {list(n)}")
        p6.append({"T": T, "continuous_I": vc, "integer_I": vi,
                   "relative_loss": 1 - vi / vc, "counts": [int(v) for v in n]})
    res["integer_rounding"] = p6

    res["not_established"] = [
        "floating point throughout; supports read at a tolerance, frontier on a "
        "grid of T/kappa except where a closed form is given",
        "known variances, static design, information rate per unit budget -- not a "
        "sample-complexity theorem",
        "the setup-cost model is an assumption; nothing here argues it must exist",
        "PART 3 optimises over the ORBIT-symmetric designs (invariant under "
        "permuting the non-top arms), which is the right baseline for this theta "
        "but is not the only notion of symmetry",
    ]
    out = REPO / "research/worker_P4_functional_20260914/P4_functional_topology.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
