#!/usr/bin/env python3
"""P22 -- MASTER: the gain matrix G_{u,l} derived from REAL instruments.

Package F asked for `G_{u,l} = (c_l^T K^{-1} M_u)^2 / (2 nu_l kappa_l)` to be connected
to actual instruments and fed into the rank-two theorem: "a matrix witness on its own
is not enough".  This script does the connection and checks it two ways.

THE MODEL.  Parameters theta in R^d.  Instrument l measures c_l^T theta with variance
nu_l at price kappa_l.  A design x (samples per unit budget) has information matrix
K(x) = sum_l (x_l/nu_l) c_l c_l^T.  Alternative u is a boundary constraint
a_u^T theta = tau_u at signed distance Delta_u, whose profiled information is

    I_u(x) = Delta_u^2 / (2 a_u^T K(x)^{-1} a_u).

THE IDENTITY.  Write q_u = a_u^T K^{-1} a_u and M_u = Delta_u a_u / q_u -- the PROFILED
contrast, which is what makes the formula about instruments rather than about three
unrelated numbers.  Then moving the design towards the one-point design at instrument l,

    d/d alpha  I_u((1-alpha)x + alpha e_l) |_{alpha=0}  =  G_{u,l} - I_u,
    G_{u,l} = (c_l^T K^{-1} M_u)^2 / (2 nu_l).

Part 1 verifies this against a central finite difference.  Part 2 computes the RANK of
G: G is the entrywise square of B_{u,l} = c_l^T K^{-1} M_u / sqrt(2 nu_l), so
rank(B) <= min(#u, #l, d) and rank(G) <= rank(B)(rank(B)+1)/2.  The rank-one and
rank-two cases are exhibited from instruments, not posited.
"""
import json, os
import numpy as np

OUT = "research/worker_P22_master_20260915"


def Kmat(C, nu, x):
    d = C.shape[1]
    K = np.zeros((d, d))
    for l in range(C.shape[0]):
        K += (x[l] / nu[l]) * np.outer(C[l], C[l])
    return K


def Ival(C, nu, x, a, Delta):
    K = Kmat(C, nu, x)
    Ki = np.linalg.inv(K)
    q = float(a @ Ki @ a)
    return Delta ** 2 / (2 * q)


def gain(C, nu, x, A, Deltas):
    """G_{u,l} and the underlying B, from the instruments."""
    K = Kmat(C, nu, x)
    Ki = np.linalg.inv(K)
    U, L = A.shape[0], C.shape[0]
    B = np.zeros((U, L))
    Is = np.zeros(U)
    for u in range(U):
        a = A[u]
        q = float(a @ Ki @ a)
        M = Deltas[u] * a / q
        Is[u] = Deltas[u] ** 2 / (2 * q)
        for l in range(L):
            B[u, l] = float(C[l] @ Ki @ M) / np.sqrt(2 * nu[l])
    return B ** 2, B, Is


def main():
    os.makedirs(OUT, exist_ok=True)
    rng = np.random.default_rng(20260915)
    rows = []
    print("PART 1 -- the directional-derivative identity, against a finite difference")
    for trial in range(6):
        d = rng.integers(2, 5)
        L = int(rng.integers(d, d + 4))
        U = int(rng.integers(2, 5))
        C = rng.normal(size=(L, d))
        # make sure the design is non-singular
        nu = np.abs(rng.normal(size=L)) + 0.5
        kap = np.abs(rng.normal(size=L)) + 0.5
        x = np.abs(rng.normal(size=L)) + 0.2
        x = x / (kap @ x)
        if np.linalg.matrix_rank(C) < d:
            continue
        A = rng.normal(size=(U, d))
        Deltas = np.abs(rng.normal(size=U)) + 0.3
        G, B, Is = gain(C, nu, x, A, Deltas)
        worst = 0.0
        for u in range(U):
            for l in range(L):
                e = np.zeros(L); e[l] = 1.0
                h = 1e-6
                f1 = Ival(C, nu, (1 - h) * x + h * e, A[u], Deltas[u])
                f0 = Ival(C, nu, (1 + h) * x - h * e, A[u], Deltas[u])
                num = (f1 - f0) / (2 * h)
                ana = G[u, l] - Is[u]
                worst = max(worst, abs(num - ana) / max(abs(ana), 1e-9))
        rows.append({"trial": trial, "d": int(d), "L": L, "U": U,
                     "worst_relative_error": worst, "ok": bool(worst < 1e-4)})
        print(f"   d={d} L={L} U={U}: worst relative error "
              f"{worst:.2e}  {'OK' if worst < 1e-4 else 'FAIL'}")

    print("\nPART 2 -- the rank of G, from instruments")
    ranks = []
    for name, d, U in (("rank-one B (one alternative)", 3, 1),
                       ("rank-two B (two alternatives)", 3, 2),
                       ("rank-three B", 4, 3)):
        L = d + 2
        C = rng.normal(size=(L, d))
        nu = np.abs(rng.normal(size=L)) + 0.5
        kap = np.abs(rng.normal(size=L)) + 0.5
        x = np.abs(rng.normal(size=L)) + 0.2
        x = x / (kap @ x)
        A = rng.normal(size=(U, d))
        Deltas = np.abs(rng.normal(size=U)) + 0.3
        G, B, Is = gain(C, nu, x, A, Deltas)
        rB = int(np.linalg.matrix_rank(B, tol=1e-9))
        rG = int(np.linalg.matrix_rank(G, tol=1e-9))
        bound = rB * (rB + 1) // 2
        ranks.append({"case": name, "rank_B": rB, "rank_G": rG,
                      "hadamard_square_bound": bound,
                      "within_bound": bool(rG <= bound)})
        print(f"   {name:30s}: rank(B)={rB}  rank(G)={rG}  "
              f"bound r(r+1)/2 = {bound}  {'OK' if rG <= bound else 'FAIL'}")

    out = {
        "script": "P22_master_gain_instruments.py",
        "identity": "d/dalpha I_u((1-alpha)x + alpha e_l) = G_{u,l} - I_u  with  "
                    "G_{u,l} = (c_l^T K^{-1} M_u)^2/(2 nu_l),  M_u = Delta_u a_u/q_u",
        "why_this_matters": "M_u is the PROFILED contrast Delta_u a_u/(a_u^T K^{-1} a_u), "
                            "not a free vector.  Writing G with a free M is what lets a "
                            "matrix witness stand in for an instrument model.",
        "part1_rows": rows,
        "part1_all_ok": all(r["ok"] for r in rows),
        "part2_ranks": ranks,
        "rank_rule": "G is the entrywise square of B, so rank(G) <= rank(B)(rank(B)+1)/2; "
                     "a rank-one B gives a rank-one G, a rank-two B gives rank <= 3",
        "not_established": [
            "This is a numerical verification of the derivative identity and the rank "
            "bound; it is not a Lean theorem.",
            "kappa_l enters only as the budget normalisation; the identity above is "
            "stated per unit of design mass, and the priced version divides by kappa_l.",
            "No optimality of any design is claimed here.",
        ],
    }
    path = os.path.join(OUT, "P22_master_gain_instruments.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"\nidentity verified in all trials: {all(r['ok'] for r in rows)}")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
