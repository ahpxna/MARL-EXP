"""Margin--regret frontier for the D6 decision-interaction functional.

R_m(mu) = max { 2D : delta_square <= 1, Top-C margin >= mu }

2D = osc(retained residual on S) - osc(retained residual on T), corner reference,
T = complement of S, |S| = k = m/2.

Why this is a linear program and not a search
---------------------------------------------
Once (a) the sign of each response span and (b) the argmax/argmin classes of the
selected residual are fixed, every constraint and the objective are linear in the
world values.  Both are finite combinatorial data, so the problem is a finite
union of LPs.  Every previous instrument for this question searched instead, and
each either failed or returned a demonstrated false negative.

Ansatz (--ansatz)
-----------------
  full       every cube point is a variable                      2^m vars
  symmetric  F(x) = g(|x cap S|, |x cap T|)                      (k+1)^2 vars
  block      F(x) = g(x_i0, |x cap S\\{i0}|, x_j0, |x cap T\\{j0}|)  4k^2 vars

`symmetric` is the permutation-symmetric relaxation; its optimum is the (m-1)
law.  `block` breaks the symmetry with one distinguished coordinate per side and
recovers the true optimum at m = 6 and 8.  At m = 4 the block class map is a
bijection onto the cube, so `block` and `full` coincide there.

Exactness
---------
The floating LP supplies a candidate. Coefficients are rounded to a finite
rational denominator ladder, and feasibility, response margins and residual
oscillations are recomputed on the full cube using Fraction. This certifies a
LOWER bound. Global equality requires an independent matching upper theorem;
neither a numerical LP objective nor an unproved symmetry reduction supplies it.
"""
from __future__ import annotations
import argparse, itertools, json, sys
from fractions import Fraction as F
from itertools import product
from pathlib import Path

import numpy as np

PROTOCOL_VERSION = "d6_margin_regret_frontier_v1"
EVIDENCE_CLASS = "EXACT_RATIONAL_LP_VERTEX_INDEPENDENTLY_RECOMPUTED"


def build(m, ansatz):
    k = m // 2
    S, T = list(range(k)), list(range(k, m))
    cube = list(product(*[[0, 1]] * m))
    if ansatz == "full":
        cls = lambda x: x
    elif ansatz == "symmetric":
        cls = lambda x: (sum(x[i] for i in S), sum(x[j] for j in T))
    elif ansatz == "block":
        i0, j0 = S[0], T[0]
        Sr = [i for i in S if i != i0]
        Tr = [j for j in T if j != j0]
        cls = lambda x: (x[i0], sum(x[i] for i in Sr), x[j0], sum(x[j] for j in Tr))
    else:
        raise ValueError(f"unknown ansatz {ansatz!r}")
    V = sorted({cls(x) for x in cube})
    vid = {v: i for i, v in enumerate(V)}
    return k, S, T, cube, cls, V, vid


def rows(m, ansatz):
    k, S, T, cube, cls, V, vid = build(m, ansatz)
    n = len(V)

    def ind(x):
        r = np.zeros(n)
        r[vid[cls(x)]] += 1.0
        return r

    upd = lambda x, i, u: tuple(u if q == i else x[q] for q in range(m))
    e = lambda i, u: tuple(u if q == i else 0 for q in range(m))

    def res(block, x):
        r = ind(x)
        for j in block:
            r = r - ind(e(j, x[j]))
        return r

    md = set()
    for i in range(m):
        for x in cube:
            for c in cube:
                if x[i] == c[i]:
                    continue
                r = ind(x) - ind(upd(x, i, c[i])) - ind(upd(c, i, x[i])) + ind(c)
                if np.abs(r).sum() > 1e-9:
                    md.add(tuple(np.round(r, 9)))
    A = np.array([list(t) for t in sorted(md)])
    span = [ind(e(j, 1)) - ind(e(j, 0)) for j in range(m)]
    Rs, Rt = {}, {}
    for x in cube:
        Rs.setdefault(cls(x), res(S, x))
        Rt.setdefault(cls(x), res(T, x))
    return dict(k=k, S=S, T=T, cube=cube, cls=cls, V=V, vid=vid, n=n,
                A=A, span=span, Rs=Rs, Rt=Rt, ind=ind, upd=upd, e=e)


def exact_check(P, m, gvec):
    """Recompute every reported quantity over Q on the full cube."""
    cls, cube, S, T = P["cls"], P["cube"], P["S"], P["T"]
    val = lambda x: gvec[P["vid"][cls(x)]]
    e, upd = P["e"], P["upd"]

    def res(block, x):
        return val(x) - sum(val(e(j, x[j])) for j in block)

    rs = [res(S, x) for x in cube]
    rt = [res(T, x) for x in cube]
    two_d = (max(rs) - min(rs)) - (max(rt) - min(rt))
    db = max(abs(val(x) - val(upd(x, i, c[i])) - val(upd(c, i, x[i])) + val(c))
             for i in range(m) for x in cube for c in cube if x[i] != c[i])
    osc = [abs(val(e(j, 1)) - val(e(j, 0))) for j in range(m)]
    margin = min(osc[i] for i in S) - max(osc[j] for j in T)
    return two_d, db, osc, margin


def certify_exact(P, m, xf, mu, ladder=(1,2,3,4,6,8,12,16,24,32,48,64)):
    """Round the float solution to Q and VERIFY exactly.

    The LP optimum need not be a vertex -- the feasible set contains lines -- so
    active-set recovery is the wrong tool.  Instead each rounded candidate is
    checked exactly on the full cube; a candidate that satisfies every constraint
    is a certified feasible world, hence an exact LOWER bound on R.  Nothing is
    reported that has not passed this check.
    """
    best = None
    for den in ladder:
        g = [F(round(float(v) * den), den) for v in xf[:P["n"]]]
        two_d, db, osc, margin = exact_check(P, m, g)
        if db == 0 or db > 1:
            continue
        if min(osc[i] for i in P["S"]) - max(osc[j] for j in P["T"]) < mu:
            continue
        ratio = F(two_d, 1) / F(db, 1)
        if best is None or ratio > best[0]:
            best = (ratio, g, two_d, db, osc, margin, den)
    return best


def frontier(m, mu, ansatz, corner_only):
    from scipy.optimize import linprog
    P = rows(m, ansatz)
    n, V, A, span = P["n"], P["V"], P["A"], P["span"]
    S, T, Rs, Rt = P["S"], P["T"], P["Rs"], P["Rt"]
    Trows = np.array([np.append(Rt[u] - Rt[v], -1.0)
                      for u, v in itertools.product(V, repeat=2) if u != v])
    MD = np.vstack([np.hstack([A, np.zeros((len(A), 1))]),
                    np.hstack([-A, np.zeros((len(A), 1))])])
    bMD = np.ones(2 * len(A))
    if corner_only and ansatz in ("block", "symmetric"):
        if ansatz == "block":
            smax = max(v[1] for v in V); tmax = max(v[3] for v in V)
            C = [v for v in V if v[1] in (0, smax) and v[3] in (0, tmax)]
        else:
            pmax = max(v[0] for v in V); qmax = max(v[1] for v in V)
            C = [v for v in V if v[0] in (0, pmax) and v[1] in (0, qmax)]
    else:
        C = V
    # sign patterns: one per distinguished coordinate + one per symmetric block
    if ansatz == "block":
        groups = [[S[0]], S[1:], [T[0]], T[1:]]
    elif ansatz == "symmetric":
        groups = [S, T]
    else:
        groups = [[j] for j in range(m)]
    best = None
    for sg in product([1, -1], repeat=len(groups)):
        sgn = [0] * m
        for s, grp in zip(sg, groups):
            for j in grp:
                sgn[j] = s
        osc = [sgn[j] * span[j] for j in range(m)]
        con = [np.append(-o, 0.0) for o in osc]; rhs = [0.0] * m
        for i in S:
            for j in T:
                con.append(np.append(osc[j] - osc[i], 0.0)); rhs.append(-float(mu))
        A_ub = np.vstack([MD, Trows, np.array(con)])
        b_ub = np.concatenate([bMD, np.zeros(len(Trows)), np.array(rhs)])
        for u, v in itertools.product(C, repeat=2):
            if u == v:
                continue
            r = linprog(-np.append(Rs[u] - Rs[v], -1.0), A_ub=A_ub, b_ub=b_ub,
                        bounds=[(None, None)] * (n + 1), method="highs")
            if r.status == 0 and (best is None or -r.fun > best[0] + 1e-9):
                best = (-r.fun, r.x, A_ub, b_ub)
    if best is None:
        return {"status": "INFEASIBLE", "mu": str(mu)}
    val, xf, A_ub, b_ub = best
    out = {"mu": str(mu), "mu_float": float(mu), "lp_objective_float": float(val)}
    cert = certify_exact(P, m, xf, mu)
    if cert is None:
        out["status"] = "NO_EXACT_CERTIFICATE"
        return out
    ratio, g, two_d, db, osc, margin, den = cert
    out["certified_denominator"] = den
    out.update({
        "status": "OK",
        "two_D_exact": str(two_d), "delta_square_exact": str(db),
        "ratio_exact": str(ratio), "ratio_float": float(ratio),
        "certified_lower_bound": True,
        "margin_exact": str(margin), "margin_float": float(margin),
        "response_oscillations_exact": [str(o) for o in osc],
        "top_c_holds": bool(min(osc[i] for i in S) >= max(osc[j] for j in T)),
        "margin_constraint_met": bool(F(margin, 1) >= F(mu)),
        "lp_minus_certified": float(float(val) - float(ratio)),
        "world_classes": [{"class": list(c), "value": str(g[i])}
                          for i, c in enumerate(P["V"])],
    })
    return out


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--m", type=int, default=6, help="even width; S is the first m/2 coordinates")
    p.add_argument("--mu", nargs="+", default=["0"],
                   help="margin thresholds, exact rationals e.g. 0 1/8 1/2")
    p.add_argument("--ansatz", choices=("block", "symmetric", "full"), default="block")
    p.add_argument("--all-classes", action="store_true",
                   help="enumerate every argmax/argmin class pair (slow); default restricts to block corners")
    p.add_argument("--out", default=None)
    a = p.parse_args(argv)
    if a.m % 2:
        raise SystemExit("m must be even (balanced complement)")
    res = [frontier(a.m, F(s), a.ansatz, not a.all_classes) for s in a.mu]
    payload = {
        "protocol_version": PROTOCOL_VERSION, "development_only": True,
        "evidence_class": EVIDENCE_CLASS, "m": a.m, "k": a.m // 2,
        "ansatz": a.ansatz,
        "uv_enumeration": "all_classes" if a.all_classes else "corner_classes",
        "lower_bound_only": True,
        "proved_upper_bound_2min_k_mk": 2 * min(a.m // 2, a.m - a.m // 2),
        "symmetric_law_m_minus_1": a.m - 1,
        "method": ("finite union of LPs over response-span sign patterns and "
                   "argmax/argmin classes; candidates rounded to rational coefficients, "
                   "then full-cube feasibility and all reported quantities checked with Fractions"),
        "non_claim": ("Every reported value is an exactly certified FEASIBLE world, hence a "
                      "LOWER bound on R for the stated ansatz. Unless the ansatz is proved WLOG, "
                      "it is also only a lower bound on the true optimum. The float LP objective "
                      "is reported separately and is not evidence."),
        "points": res,
    }
    if a.out:
        out = Path(a.out)
        if out.exists():
            raise SystemExit(f"refusing to overwrite existing ledger artifact: {out}")
        out.parent.mkdir(parents=True, exist_ok=True)
        try:
            sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
            from research_chains.provenance import write_artifact_with_provenance
            write_artifact_with_provenance(
                out, payload,
                protocol={"protocol_version": PROTOCOL_VERSION, "m": a.m,
                          "ansatz": a.ansatz, "mu": a.mu,
                          "all_classes": bool(a.all_classes)},
                seed=0, evidence_class=EVIDENCE_CLASS, chain="D6")
        except Exception as exc:
            print(f"provenance wrapper unavailable ({exc!r}); "
                  f"writing artifact WITHOUT provenance manifest", file=sys.stderr)
            out.write_text(json.dumps(payload, indent=2))
    print(json.dumps({k: v for k, v in payload.items() if k != "points"}, indent=2))
    for r in res:
        print(json.dumps({k: v for k, v in r.items() if k != "world_classes"}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
