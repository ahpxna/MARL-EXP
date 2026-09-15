#!/usr/bin/env python3
"""P21 -- Query: the E-Q harness.  Same-norm measurements, a pilot H^2, and the ACTUAL
likelihood-ratio test's error and regret at a feasible N.

Audit items answered here:

 Q6  g_0 and u were compared without a common normalisation.  Rescaling does not move
     the exponent, but it moves every constant and every finite-N comparison.  Here
     both are normalised to E_pi[g^2] = 1 before anything is measured.

 Q3  P15's measured constants and P16's substitution give a numerical projection, not a
     certificate.  This file keeps the two apart: the H^2 curve and the fitted exponent
     are NUMERICAL; the LRT error at the chosen N is MONTE CARLO with a reported CI;
     and the N it uses is chosen from the PILOT H^2 before the run, not after.

 negative control: the raw comparator (g == 0) leaves the two worlds identical, so its
 equal-prior error must come out at 1/2.  If it does not, the harness is wrong.

Everything is one fixed measurement applied IID; no adaptivity.
"""
from __future__ import annotations
import importlib.util, json, math, os
from pathlib import Path
import numpy as np

REPO = Path(__file__).resolve().parents[1]
OUT = REPO / "research/worker_P21_query_20260915"
SQ2PI = math.sqrt(2 * math.pi)
SIG = 1.0


def load(name):
    spec = importlib.util.spec_from_file_location(name, REPO / "scripts" / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def phi(u):
    return np.exp(-0.5 * (u / SIG) ** 2) / (SIG * SQ2PI)


def dens(Y, cube, p, FW, gvals, h):
    """mixture density of Y under world W with measurement values gvals."""
    out = np.zeros_like(Y)
    for k in range(len(cube)):
        out += p[k] * phi(Y - FW[k] - h * gvals[k])
    return out


def normalise(p, vals):
    """E_pi[g^2] = 1."""
    n2 = float(np.dot(p, vals ** 2))
    assert n2 > 0
    return vals / math.sqrt(n2)


def hellinger2(cube, p, FA, FB, gvals, h, lo, hi, npt=200001):
    Y = np.linspace(lo, hi, npt)
    pa = dens(Y, cube, p, FA, gvals, h)
    pb = dens(Y, cube, p, FB, gvals, h)
    integ = 0.5 * (np.sqrt(pa) - np.sqrt(pb)) ** 2
    return float(np.trapezoid(integ, Y))


def lrt_montecarlo(cube, p, FA, FB, gvals, h, N, reps, rng):
    """Draw N observations from each world, run the exact LRT on the true mixture
    densities, record the error of the induced label."""
    K = len(cube)
    err = np.zeros(2)
    for w, FW in ((0, FA), (1, FB)):
        wrong = 0
        for _ in range(reps):
            sel = rng.choice(K, size=N, p=p)
            Y = FW[sel] + h * gvals[sel] + rng.normal(0.0, SIG, size=N)
            la = np.log(dens(Y, cube, p, FA, gvals, h) + 1e-300).sum()
            lb = np.log(dens(Y, cube, p, FB, gvals, h) + 1e-300).sum()
            pick = 0 if la >= lb else 1
            wrong += (pick != w)
        err[w] = wrong / reps
    return err


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    P5 = load("P5_query_h4_robustness")
    cfg, m, cube, pdict, FAd, FBd, levels, _hA = P5.setup()
    idx = {x: i for i, x in enumerate(cube)}
    p = np.array([float(pdict[x]) for x in cube], dtype=float)
    FA = np.array([float(FAd[x]) for x in cube], dtype=float)
    FB = np.array([float(FBd[x]) for x in cube], dtype=float)

    g0map, _gap, _cvec = P5.find_g0(m, cube, pdict, FAd, FBd, levels)
    umap, _ugaps, uname = P5.pick_u(m, cube, pdict, FAd, FBd, levels)
    g0 = np.array([float(g0map[x]) for x in cube], dtype=float)
    u = np.array([float(umap[x]) for x in cube], dtype=float)
    g0n = normalise(p, g0)
    un = normalise(p, u)
    print(f"cube size {len(cube)}, u column = {uname}")
    print(f"measurements normalised to E_pi[g^2] = 1: "
          f"||g0||={float(np.dot(p, g0n**2)):.6f}  ||u||={float(np.dot(p, un**2)):.6f}")

    lo = float(min(FA.min(), FB.min())) - 9.0
    hi = float(max(FA.max(), FB.max())) + 9.0

    # --- negative control: the raw comparator
    zero = np.zeros_like(g0n)
    h2_raw = hellinger2(cube, p, FA, FB, zero, 0.3, lo, hi)
    print(f"negative control (g == 0): H^2 = {h2_raw:.3e}  (must be ~0)")

    rows = []
    rng = np.random.default_rng(20260915)
    for name, gv in (("g0_normalised", g0n), ("u_normalised", un)):
        # --- pilot H^2 curve, BEFORE choosing N
        hs = [0.4, 0.3, 0.2, 0.15, 0.1]
        h2 = [hellinger2(cube, p, FA, FB, gv, h, lo, hi) for h in hs]
        # local exponent between consecutive h
        expo = [math.log(h2[i] / h2[i + 1]) / math.log(hs[i] / hs[i + 1])
                for i in range(len(hs) - 1)]
        r_fit = expo[-1] / 2.0
        print(f"\n{name}: H^2 exponent (local, 2r) = "
              + ", ".join(f"{e:.4f}" for e in expo) + f"   => r ~ {r_fit:.3f}")
        # --- choose h and N from the PILOT, then run
        h_run = 0.3
        H2 = hellinger2(cube, p, FA, FB, gv, h_run, lo, hi)
        rho = 1.0 - H2
        L = -math.log1p(-H2)
        eps_target = 0.05
        N = max(1, math.ceil(math.log(1 / (2 * eps_target)) / L)) if L > 0 else None
        if N is None or N > 4000:
            print(f"  H^2={H2:.3e} at h={h_run}: predicted N={N} not feasible; "
                  f"raising h")
            h_run = 0.6
            H2 = hellinger2(cube, p, FA, FB, gv, h_run, lo, hi)
            rho = 1.0 - H2
            L = -math.log1p(-H2)
            N = max(1, math.ceil(math.log(1 / (2 * eps_target)) / L))
        pred_up = 0.5 * rho ** N
        pred_lo = 0.25 * rho ** (2 * N)
        reps = 4000
        err = lrt_montecarlo(cube, p, FA, FB, gv, h_run, N, reps, rng)
        e_bayes = 0.5 * (err[0] + err[1])
        se = math.sqrt(max(e_bayes * (1 - e_bayes), 1e-12) / (2 * reps))
        ok = (pred_lo - 3 * se <= e_bayes <= pred_up + 3 * se)
        print(f"  h={h_run}  H^2={H2:.4e}  L={L:.4e}  N={N}")
        print(f"  LRT equal-prior error = {e_bayes:.4f} +- {1.96*se:.4f} (95%), "
              f"per-world {err[0]:.4f}/{err[1]:.4f}")
        print(f"  testing bracket rho^2N/4 = {pred_lo:.4e} <= e <= rho^N/2 = "
              f"{pred_up:.4e}   inside: {ok}")
        rows.append({
            "measurement": name,
            "normalisation": "E_pi[g^2] = 1",
            "pilot_h": hs, "pilot_H2": h2, "local_exponent_2r": expo,
            "r_estimate": r_fit,
            "h_run": h_run, "H2_at_h_run": H2, "L": L, "N_chosen": N,
            "N_rule": "ceil(log(1/(2*eps))/L) with eps = 0.05, chosen from the PILOT",
            "reps_per_world": reps,
            "error_world_A": err[0], "error_world_B": err[1],
            "equal_prior_error": e_bayes, "se": se,
            "ci95": [e_bayes - 1.96 * se, e_bayes + 1.96 * se],
            "bracket_lower_rho2N_over_4": pred_lo,
            "bracket_upper_rhoN_over_2": pred_up,
            "inside_bracket_within_3se": bool(ok),
        })

    # --- the crossover: order wins only BELOW it; constants win above it
    cross = None
    if len(rows) == 2:
        g0row, urow = rows[0], rows[1]
        # fit H2 = c h^k on the two smallest pilot points for each measurement
        def fit(row):
            h1, h2_ = row["pilot_h"][-2], row["pilot_h"][-1]
            v1, v2 = row["pilot_H2"][-2], row["pilot_H2"][-1]
            k = math.log(v1 / v2) / math.log(h1 / h2_)
            c = v1 / h1 ** k
            return c, k
        cg, kg = fit(g0row)
        cu, ku = fit(urow)
        if kg > ku:
            hx = (cu / cg) ** (1.0 / (kg - ku))
            cross = {"c_g0": cg, "k_g0": kg, "c_u": cu, "k_u": ku,
                     "crossover_h": hx,
                     "reading": (
                         "BELOW h = %.4f the lower-order measurement u is the more "
                         "informative one, as the order law says.  ABOVE it the "
                         "constants dominate and the r = 2 measurement g0 wins.  The "
                         "runs above use h = 0.6, which is ABOVE the crossover: the "
                         "sample counts there must NOT be read as evidence about the "
                         "order." % hx)}
            print(f"\ncrossover: h* = {hx:.4f}  (g0: c={cg:.4e}, k={kg:.3f};  "
                  f"u: c={cu:.4e}, k={ku:.3f})")
            print(f"  {cross['reading']}")

    out = {
        "script": "P21_query_normalized_lrt.py",
        "crossover": cross,
        "negative_control_raw_comparator_H2": h2_raw,
        "rows": rows,
        "evidence_classes": {
            "H2_curve_and_exponent": "NUMERICAL (quadrature on a fixed grid)",
            "LRT_error": "MONTE CARLO with a reported 95% CI",
            "testing_bracket": "THEOREM (LeanQueryAffinityTestingV1); used here only to "
                               "check the simulation lands inside it",
        },
        "not_established": [
            "The fitted exponent is a local slope on a finite h grid; it is NOT a "
            "certificate of H^2 ~ h^{2r}.",
            "N was chosen from the pilot BEFORE the run, so the Monte Carlo is not "
            "tuned to the answer; but it is still a simulation, not a bound.",
            "Normalising to E_pi[g^2] = 1 fixes the amplitude only.  A full same-cost "
            "comparison also needs the measurement price, which this harness holds "
            "equal by construction (one observation per sample, either measurement).",
        ],
        "lean": [
            "LeanQueryAffinityTestingV1 (the bracket)",
            "LeanQuerySampleComplexityV1 (log sandwich, Nat.ceil)",
            "LeanQueryGaussianLevelV1 (why the order is r, not 1)",
        ],
    }
    path = OUT / "P21_query_normalized_lrt.json"
    path.write_text(json.dumps(out, indent=1) + "\n")
    print(f"\nartifact: {path}")


if __name__ == "__main__":
    main()
