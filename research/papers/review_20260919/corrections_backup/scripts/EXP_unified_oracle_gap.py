#!/usr/bin/env python3
"""What a conservative certificate costs over the decision it is used to justify.

Setting (sec 3 of the unified batch).  Family

    F_theta(x) = a x1 + b x2 + c x1 x2,   theta = (a,b,c),  a > b > 0, c > 0,

on the full cube with a corner reference.  Exact losses (verified in
EXP_unified_geometry_decision.py):

    L({1}) = (b+c)/2,   L({2}) = (a+c)/2,   delta_I = c,   rho = a - b.

So the DECISION "retain coordinate 1" is settled by the sign of a-b alone, while the
Top-C margin CERTIFICATE asks for rho >= 2 delta_I, i.e. a - b >= 2c.  Both are half-space
questions about theta, but about DIFFERENT half-spaces, and the certificate's boundary is
strictly closer to the truth whenever c > 0.

Observations are Gaussian and linear in theta:

    q1 -> a,   q2 -> b,   q3 -> a + b + c,

each unit variance, unit cost, with an allocation w on the simplex.  For a half-space
alternative {theta' : v . theta' <= t} the profiled information is

    (1/2) (v.theta - t)^2 / (v^T W(w)^{-1} v),   W(w) = sum_q w_q M_q^T M_q,

and the game value is its maximum over w.  This script computes both games by blind
numerical search over the simplex and reports the cost ratio

    cost_certificate / cost_decision = Gamma_dec / Gamma_cert.

SELF-CHECKS: the half-space formula is confirmed against a direct constrained minimisation
that knows nothing about it; the certificate game is never cheaper than the decision game;
and in the regime a-b < 2c the certificate is unattainable at any cost while the decision
is settled -- the extreme form of the separation.
"""

import json
import sys

import numpy as np

# design: rows are the linear functionals each query measures
M = np.array([[1.0, 0.0, 0.0],      # q1 reads a
              [0.0, 1.0, 0.0],      # q2 reads b
              [1.0, 1.0, 1.0]])     # q3 reads a+b+c
COSTS = np.array([1.0, 1.0, 1.0])

V_DEC = np.array([1.0, -1.0, 0.0])    # decision boundary uses a-b
V_CERT = np.array([1.0, -1.0, -2.0])  # certificate boundary uses a-b-2c

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def W_of(w):
    return sum(w[q] * np.outer(M[q], M[q]) for q in range(len(w)))


def halfspace_info(w, v, margin):
    """(1/2) margin^2 / (v^T W^{-1} v), the profiled information against the
    half-space at signed distance `margin`."""
    W = W_of(w)
    try:
        Winv = np.linalg.inv(W + 1e-12 * np.eye(3))
    except np.linalg.LinAlgError:
        return 0.0
    denom = float(v @ Winv @ v)
    if denom <= 0:
        return 0.0
    return 0.5 * margin * margin / denom


def halfspace_info_bruteforce(w, v, theta, t, ntrial=200000, seed=0):
    """The same infimum by blind constrained minimisation, to confirm the formula."""
    rng = np.random.default_rng(seed)
    W = W_of(w)
    best = float("inf")
    # sample theta' on the boundary v.theta' = t (the infimum is attained there)
    for _ in range(3):
        base = rng.normal(size=(ntrial, 3)) * 2.0 + theta
        # project each sample onto the boundary hyperplane
        adj = (base @ v - t) / (v @ v)
        pts = base - np.outer(adj, v)
        d = pts - theta
        vals = 0.5 * np.einsum("ij,jk,ik->i", d, W, d)
        best = min(best, float(vals.min()))
    return best


def game(v, margin, npts=60):
    """max over the cost-normalised simplex of the profiled information."""
    best, bw = -1.0, None
    for i in range(npts + 1):
        for j in range(npts + 1 - i):
            k = npts - i - j
            w = np.array([i, j, k], dtype=float) / npts
            # normalise so that sum_q c_q w_q = 1
            s = float(COSTS @ w)
            if s <= 0:
                continue
            w = w / s
            val = halfspace_info(w, v, margin)
            if val > best:
                best, bw = val, w
    return best, bw


def main():
    print("=" * 76)
    print("The price of certifying a margin over the price of making the decision")
    print("=" * 76)

    # --- confirm the half-space formula against blind minimisation
    print("\n  half-space information formula vs blind constrained minimisation")
    print("  " + "-" * 70)
    worst = 0.0
    for w in [np.array([1 / 3, 1 / 3, 1 / 3]), np.array([0.6, 0.3, 0.1]),
              np.array([0.2, 0.2, 0.6])]:
        theta = np.array([3.0, 1.0, 0.5])
        for v, t in [(V_DEC, -0.4), (V_CERT, 0.0)]:
            margin = float(v @ theta - t)
            f = halfspace_info(w, v, margin)
            b = halfspace_info_bruteforce(w, v, theta, t)
            rel = abs(f - b) / max(abs(f), 1e-12)
            worst = max(worst, rel)
    check("closed-form half-space information matches blind minimisation",
          worst < 5e-3, f"worst relative gap {worst:.2e}")

    # --- the two games across the family
    print("\n  cost of the certificate against cost of the decision")
    print("  " + "-" * 70)
    eps = 0.1
    rows = []
    a, b = 3.0, 1.0
    for c in [0.05, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0, 1.25, 1.5]:
        theta = np.array([a, b, c])
        m_dec = (a - b) + 2 * eps          # distance to {a'-b' <= -2 eps}
        m_cert = (a - b) - 2 * c           # distance to {a'-b'-2c' <= 0}
        g_dec, w_dec = game(V_DEC, m_dec)
        if m_cert <= 0:
            g_cert, w_cert = 0.0, None
        else:
            g_cert, w_cert = game(V_CERT, m_cert)
        ratio = (g_dec / g_cert) if g_cert > 0 else float("inf")
        rows.append({"a": a, "b": b, "c": c, "eps": eps,
                     "margin_dec": m_dec, "margin_cert": m_cert,
                     "Gamma_dec": g_dec, "Gamma_cert": g_cert,
                     "cost_ratio": ratio})
        rs = "infinite" if ratio == float("inf") else f"{ratio:8.3f}"
        print(f"      c={c:4.2f}:  Gamma_dec={g_dec:8.4f}  Gamma_cert={g_cert:8.4f}"
              f"   cost ratio = {rs}")

    check("the certificate is never cheaper than the decision",
          all(r["Gamma_cert"] <= r["Gamma_dec"] + 1e-9 for r in rows))
    check("the cost ratio grows as the interaction grows",
          all(rows[i + 1]["cost_ratio"] >= rows[i]["cost_ratio"] - 1e-9
              for i in range(len(rows) - 1)))
    finite = [r for r in rows if r["cost_ratio"] != float("inf")]
    check("and the extra cost is already large well before the certificate dies",
          any(r["cost_ratio"] > 3 for r in finite),
          f"largest finite ratio {max(r['cost_ratio'] for r in finite):.2f}")

    # --- the regime where the certificate is unattainable but the decision is not
    print("\n  the regime a - b < 2c")
    print("  " + "-" * 70)
    unattainable = [r for r in rows if r["margin_cert"] <= 0]
    for r in unattainable:
        print(f"      c={r['c']:4.2f}:  a-b={a-b:.2f} < 2c={2*r['c']:.2f}  ->  "
              f"certificate unattainable at any cost; decision settled at "
              f"Gamma={r['Gamma_dec']:.4f}")
    check("there is a regime with a settled decision and NO attainable certificate",
          len(unattainable) > 0 and all(r["Gamma_dec"] > 0 for r in unattainable),
          f"{len(unattainable)} of {len(rows)} cells")
    check("in that regime the true world itself fails the margin condition",
          all((a - b) <= 2 * r["c"] for r in unattainable))
    strict = [r for r in unattainable if (a - b) < 2 * r["c"]]
    check("including cells strictly inside the certificate-failure region",
          len(strict) > 0, f"{len(strict)} strictly-interior cells")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 76)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 76)
    out = {"rows": rows, "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/oracle_gap.json", "w") as f:
        json.dump(out, f, indent=2, default=str)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
