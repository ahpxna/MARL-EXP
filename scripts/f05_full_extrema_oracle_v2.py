#!/usr/bin/env python3
"""F05 v2: the shrink-interval / open-pair oracle for the FULL alternative set,
checked against an independent exhaustive-region oracle.

Fixes the four defects of the v1 probe: uses v4's own world law, scans EVERY
crossing pair, never infers "extrema changed" from an argmax index, and keeps
J_scalar / J_old / J_full distinct.

  python3 scripts/f05_full_extrema_oracle_v2.py certify   # 8-case agreement table
  python3 scripts/f05_full_extrema_oracle_v2.py search N   # J_full vs J_scalar
"""
import sys, itertools, json
import numpy as np
from scipy.optimize import minimize, minimize_scalar

# ---- v4 world law (sigma is PER ACTION, capacities sorted, extrema pinned) ----
def draw_world(rng, R, K, random_extrema=True):
    caps = np.sort(rng.uniform(.35, 2.0, size=R))[::-1] - np.arange(R)*1e-3
    th = np.zeros((R, K))
    for r, cap in enumerate(caps):
        c = float(rng.normal(scale=.3))
        th[r] = rng.uniform(c-cap/2, c+cap/2, size=K)
        lo, hi = (rng.choice(K, 2, replace=False) if random_extrema else (0, K-1))
        th[r, lo], th[r, hi] = c-cap/2, c+cap/2
    return th, rng.uniform(.15, .85, size=K)

def topk(th, k):
    return list(np.argsort(-np.ptp(th, axis=1), kind="stable")[:k])

def extrema(v):
    return int(np.argmax(v)), int(np.argmin(v))

# ---- the oracle under test ----
def S(theta_i, a_i, z):
    if z >= np.ptp(theta_i): return 0.0
    f = lambda l: .5*np.sum(a_i*(np.clip(theta_i, l, l+z)-theta_i)**2)
    r = minimize_scalar(f, bounds=(theta_i.min()-z, theta_i.max()),
                        method="bounded", options={"xatol": 1e-12})
    return float(r.fun)

def E_pair(theta_j, a_j, p, q, z):
    g = z - (theta_j[p]-theta_j[q])
    return 0.0 if g <= 0 else g*g/(2.0*(1.0/a_j[p] + 1.0/a_j[q]))

def J_decomp(th, al, k):
    T = topk(th, k); out = [r for r in range(th.shape[0]) if r not in T]
    best, arg = np.inf, None
    for i in T:
        zmax = np.ptp(th[i])
        for j in out:
            for p, q in itertools.permutations(range(th.shape[1]), 2):
                f = lambda z: S(th[i], al[i], z) + E_pair(th[j], al[j], p, q, z)
                r = minimize_scalar(f, bounds=(0.0, zmax), method="bounded",
                                    options={"xatol": 1e-12})
                v = min(float(r.fun), f(0.0), f(zmax))
                if v < best: best, arg = v, (i, j, p, q, float(r.x))
    return best, arg

# ---- independent reference: every extrema region, each its own QP ----
def _region_qp(ti, tj, ai, aj, s, t, p, q, K):
    cons = []
    for a in range(K):
        if a != s: cons.append({'type':'ineq','fun':(lambda v,a=a,s=s: v[s]-v[a])})
        if a != t: cons.append({'type':'ineq','fun':(lambda v,a=a,t=t: v[a]-v[t])})
        if a != p: cons.append({'type':'ineq','fun':(lambda v,a=a,p=p,K=K: v[K+p]-v[K+a])})
        if a != q: cons.append({'type':'ineq','fun':(lambda v,a=a,q=q,K=K: v[K+a]-v[K+q])})
    cons.append({'type':'ineq','fun':(lambda v,p=p,q=q,s=s,t=t,K=K:
                 (v[K+p]-v[K+q])-(v[s]-v[t]))})
    obj = lambda v: .5*(np.sum(ai*(v[:K]-ti)**2)+np.sum(aj*(v[K:]-tj)**2))
    jac = lambda v: np.concatenate([ai*(v[:K]-ti), aj*(v[K:]-tj)])
    return minimize(obj, np.concatenate([ti, tj]), jac=jac, constraints=cons,
                    method="SLSQP", options={"maxiter": 200, "ftol": 1e-14})

def J_region(th, al, k):
    R, K = th.shape
    T = topk(th, k); out = [r for r in range(R) if r not in T]
    best, arg = np.inf, None
    for i in T:
        for j in out:
            for (s, t) in itertools.permutations(range(K), 2):
                for (p, q) in itertools.permutations(range(K), 2):
                    r = _region_qp(th[i], th[j], al[i], al[j], s, t, p, q, K)
                    if r.success and r.fun < best:
                        v = r.x
                        if np.ptp(v[K:]) - np.ptp(v[:K]) >= -1e-9:   # original constraint
                            best, arg = float(r.fun), (i, j, s, t, p, q)
    return best, arg

def J_scalar(th, al, k):
    "pair-flip at the CURRENT extrema, ordering constraints dropped"
    T = topk(th, k); out = [r for r in range(th.shape[0]) if r not in T]
    best = np.inf
    for i in T:
        s, t = extrema(th[i])
        for j in out:
            p, q = extrema(th[j])
            gap = (th[i][s]-th[i][t]) - (th[j][p]-th[j][q])
            if gap <= 0: return 0.0
            v = 1/al[i][s] + 1/al[i][t] + 1/al[j][p] + 1/al[j][q]
            best = min(best, gap*gap/(2*v))
    return best

def J_old(th, al, k):
    "QP in the CURRENT extrema region only"
    R, K = th.shape
    T = topk(th, k); out = [r for r in range(R) if r not in T]
    best = np.inf
    for i in T:
        s, t = extrema(th[i])
        for j in out:
            p, q = extrema(th[j])
            r = _region_qp(th[i], th[j], al[i], al[j], s, t, p, q, K)
            if r.success: best = min(best, float(r.fun))
    return best

def certify():
    rows = []
    for seed in (701, 709, 719, 727):
        rng = np.random.default_rng(np.random.SeedSequence([seed, 0, 0]))
        th, sig = draw_world(rng, 4, 4)
        rows.append((f"gen{seed}", th, sig, np.ones_like(th)))
    th = np.array([[0.,0.,0.,1.0],[0.,0.,0.,.9],[0.,0.,0.,.5],[0.,0.,0.,.4]])
    sig = np.ones(4)
    th2 = th.copy(); th2[1, 3] = 1.0
    w3 = np.ones_like(th); w3[:, 1] = 1e4
    rows += [("tie_gap", th, sig, np.ones_like(th)),
             ("tie_rel0_rel1", th2, sig, np.ones_like(th)),
             ("skew_w_1e4", th, sig, w3),
             ("skew_sigma_0.1", th, np.array([1., .1, 1., 1.]), np.ones_like(th))]
    print(f"{'case':<16}{'J_decomp':>14}{'J_region':>14}{'rel.diff':>11}  {'J_scalar':>12}{'J_old':>12}")
    bad = 0
    for name, th, sig, w in rows:
        al = w/(sig[None, :]**2)
        jd, _ = J_decomp(th, al, 2); jr, _ = J_region(th, al, 2)
        rel = abs(jd-jr)/max(jr, 1e-12); bad += rel >= 2e-6
        print(f"{name:<16}{jd:>14.6e}{jr:>14.6e}{rel:>11.1e}  "
              f"{J_scalar(th,al,2):>12.6e}{J_old(th,al,2):>12.6e}")
    print(f"mismatches: {bad}/{len(rows)}")

def search(n):
    rng = np.random.default_rng(20260912)
    lt = gt = eq = used = 0; wlo = whi = None
    for _ in range(n):
        th = rng.uniform(-1, 1, size=(3, 4))
        al = 10.0**rng.uniform(-2.5, 2.5, size=(3, 4))
        js = J_scalar(th, al, 1); jf, _ = J_decomp(th, al, 1)
        if js <= 0 or jf <= 0: continue
        used += 1; r = jf/js
        if r < 1-1e-9:
            lt += 1
            if wlo is None or r < wlo[0]: wlo = (r, th.copy(), al.copy())
        elif r > 1+1e-9:
            gt += 1
            if whi is None or r > whi[0]: whi = (r, th.copy(), al.copy())
        else: eq += 1
    print(f"{used} worlds: J_full<J_scalar {lt}, J_full>J_scalar {gt}, equal {eq}")
    for tag, wz in (("min ratio", wlo), ("max ratio", whi)):
        if wz is None: continue
        r, th, al = wz
        jr, _ = J_region(th, al, 1); jd, _ = J_decomp(th, al, 1)
        print(f"  {tag}: {r:.6f}  decomp={jd:.6e} region={jr:.6e} "
              f"agree={abs(jd-jr)/max(jr,1e-12) < 2e-6}")

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "certify"
    if cmd == "certify": certify()
    else: search(int(sys.argv[2]) if len(sys.argv) > 2 else 600)
