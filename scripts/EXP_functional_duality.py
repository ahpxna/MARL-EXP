"""FUNCTIONAL: is there a duality gap on the pair-region programme?

The paper proves KKT sufficiency without inverting M, and lists strong duality
as an open question. The reason it is a question rather than a citation is the
semidefiniteness: M is only positive SEMIdefinite, deliberately, because an
allocator that has learned something concentrates its budget and its information
matrix loses rank. Classical strong duality for convex quadratic programmes with
linear constraints is usually quoted under a definiteness or a Slater condition,
and neither is assumed here.

The programme is

    minimise  (1/2)(lambda - mu)^T M (lambda - mu)    subject to   A lambda <= 0.

Its Lagrangian dual is finite only where A^T y lies in the range of M -- outside
that set the inner infimum is -infinity, which is exactly the effect a singular M
has. On the range, the dual objective is

    g(y) = -(1/2) (A^T y)^T M^+ (A^T y) + y^T A mu,

with M^+ the pseudo-inverse. The question the experiment asks is whether
sup g < inf primal ever happens.

This has a sharp refutable form: a single instance with a gap settles it
negatively, and no number of instances without one settles it positively. So the
experiment is run as a search for a counterexample, and reported as a search.

Three families of instance, in increasing awkwardness:
  full         M positive definite -- strong duality is classical here, so this
               arm is the self-check rather than a question
  singular     M with a deliberate null space, the case the paper cares about
  aligned      M singular AND its null space deliberately aligned with the
               constraint normals, which is where a gap would have to come from
               if it comes from anywhere

Self-check: on the positive-definite arm the gap must be zero to solver
tolerance. If it is not, the gap measurement is broken and nothing else in the
run means anything, so the sweep is not reported.
"""
import json
import time
import argparse
import os
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import minimize, linprog

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as _P

MASTER_SEED = 90909
FAMILIES = ('full', 'singular', 'aligned')
FLAG = 1e-4        # first-pass threshold; anything above it is re-solved and re-checked


def make_instance(rng, family, n, mconstr):
    """M (PSD), A (constraints), mu (the truth)."""
    if family == 'full':
        B = rng.normal(size=(n + 2, n))
        M = B.T @ B + 0.05 * np.eye(n)
        A = rng.normal(size=(mconstr, n))
    elif family == 'singular':
        rank = max(1, n - rng.integers(1, min(3, n) + 1))
        B = rng.normal(size=(rank, n))
        M = B.T @ B
        A = rng.normal(size=(mconstr, n))
    else:                                   # aligned
        rank = max(1, n - 2)
        B = rng.normal(size=(rank, n))
        M = B.T @ B
        # put constraint normals inside the null space of M, which is the only
        # structural way a semidefinite programme can lose its dual
        w, V = np.linalg.eigh(M)
        null = V[:, w < 1e-9 * max(w.max(), 1.0)]
        A = np.empty((mconstr, n))
        for i in range(mconstr):
            if null.shape[1] and i % 2 == 0:
                c = rng.normal(size=null.shape[1])
                A[i] = null @ c
            else:
                A[i] = rng.normal(size=n)
    mu = rng.normal(size=n)
    return M, A, mu


def primal(M, A, mu):
    n = M.shape[0]
    f = lambda l: 0.5 * float((l - mu) @ M @ (l - mu))
    jac = lambda l: M @ (l - mu)
    best = None
    for t in range(4):
        x0 = np.zeros(n) if t == 0 else mu + np.random.default_rng(5 + t).normal(0, 0.5, n)
        r = minimize(f, x0, jac=jac, method='SLSQP',
                     constraints=[{'type': 'ineq', 'fun': lambda l: -(A @ l),
                                   'jac': lambda l: -A}],
                     options={'maxiter': 800, 'ftol': 1e-14})
        if r.success and np.all(A @ r.x <= 1e-8):
            v = f(r.x)
            best = v if best is None else min(best, v)
    return best


def dual(M, A, mu, tol=1e-9, restarts=5, ftol=1e-14, seed=31):
    """sup over y >= 0 of the Lagrangian dual, with the range condition enforced.

    inf_lambda L(lambda, y) is finite only when A^T y is in range(M); off that
    set the dual is -infinity, so the range condition is imposed as an equality
    on the null-space components rather than penalised.
    """
    n = M.shape[0]; mcon = A.shape[0]
    w, V = np.linalg.eigh(M)
    keep = w > tol * max(w.max(), 1.0)
    Mp = V[:, keep] @ np.diag(1.0 / w[keep]) @ V[:, keep].T
    null = V[:, ~keep]

    def negg(y):
        # with d = lambda - mu and s = A^T y, inf_d L = -(1/2) s^T M^+ s + y^T A mu,
        # so the dual is maximised by minimising its negative
        s = A.T @ y
        return 0.5 * float(s @ Mp @ s) - float(y @ (A @ mu))

    cons = [{'type': 'ineq', 'fun': lambda y: y}]
    if null.shape[1]:
        cons.append({'type': 'eq', 'fun': lambda y: null.T @ (A.T @ y)})
    best = None
    for t in range(restarts):
        y0 = np.zeros(mcon) if t == 0 else np.abs(
            np.random.default_rng(seed + t).normal(0, 0.5 * (1 + t % 4), mcon))
        r = minimize(negg, y0, method='SLSQP', constraints=cons,
                     bounds=[(0, None)] * mcon,
                     options={'maxiter': 4000 if restarts > 10 else 800, 'ftol': ftol})
        if r.success:
            y = np.maximum(r.x, 0)
            if null.shape[1] == 0 or np.max(np.abs(null.T @ (A.T @ y))) < 1e-6:
                v = -negg(y)
                best = v if best is None else max(best, v)
    return best


def verify(M, A, mu, restarts=30):
    """Re-solve both sides much harder, for an instance that looked like a gap.

    A flagged gap is a claim, and SLSQP noise on the definite arm already reaches
    a few parts in 10^5, so a first-pass flag is not evidence. This re-runs each
    side from many starts and returns the best primal and best dual found; a gap
    that survives is one the optimisers could not close, which is the most the
    method can say.
    """
    n = M.shape[0]
    f = lambda l: 0.5 * float((l - mu) @ M @ (l - mu))
    jac = lambda l: M @ (l - mu)
    bp = None
    for t in range(restarts):
        x0 = np.zeros(n) if t == 0 else mu + np.random.default_rng(1000 + t).normal(0, 1.0, n)
        r = minimize(f, x0, jac=jac, method='SLSQP',
                     constraints=[{'type': 'ineq', 'fun': lambda l: -(A @ l),
                                   'jac': lambda l: -A}],
                     options={'maxiter': 4000, 'ftol': 1e-16})
        if r.success and np.all(A @ r.x <= 1e-10):
            v = f(r.x)
            bp = v if bp is None else min(bp, v)
    # the dual must be solved at least as hard as the primal: solving one side
    # well and the other poorly manufactures a gap out of the solver
    bd = None
    for t in range(4):
        d = dual(M, A, mu, restarts=restarts, ftol=1e-16, seed=5000 + 97 * t)
        if d is not None:
            bd = d if bd is None else max(bd, d)
    return bp, bd


def attainment_probe(M, A, mu, radii=(1, 3, 10, 30, 100, 300, 1000, 3000)):
    """Is an apparent gap a real gap, or a supremum that is never attained?

    Classical duality for a convex quadratic programme with affine constraints
    says the gap should be zero, so an apparent gap is more likely to mean the
    dual supremum is approached only as ||y|| grows rather than reached at a
    finite y. This solves the dual under a norm cap and raises the cap. A value
    that keeps climbing toward the primal is non-attainment; one that plateaus
    strictly below is a gap the optimisers cannot close.
    """
    n = M.shape[0]; mcon = A.shape[0]
    w, V = np.linalg.eigh(M)
    keep = w > 1e-9 * max(w.max(), 1.0)
    Mp = V[:, keep] @ np.diag(1.0 / w[keep]) @ V[:, keep].T
    null = V[:, ~keep]

    def negg(y):
        sv = A.T @ y
        return 0.5 * float(sv @ Mp @ sv) - float(y @ (A @ mu))

    out = []
    for R in radii:
        cons = [{'type': 'ineq', 'fun': lambda y, R=R: R - np.linalg.norm(y)}]
        if null.shape[1]:
            cons.append({'type': 'eq', 'fun': lambda y: null.T @ (A.T @ y)})
        best = None
        for t in range(8):
            y0 = np.zeros(mcon) if t == 0 else np.abs(
                np.random.default_rng(700 + t).normal(0, R / 3.0, mcon))
            r = minimize(negg, y0, method='SLSQP', constraints=cons,
                         bounds=[(0, None)] * mcon,
                         options={'maxiter': 3000, 'ftol': 1e-16})
            if r.success:
                y = np.maximum(r.x, 0)
                if null.shape[1] == 0 or np.max(np.abs(null.T @ (A.T @ y))) < 1e-6:
                    v = -negg(y)
                    best = v if best is None else max(best, v)
        out.append(dict(radius=R, dual=best,
                        norm_at_optimum=None if best is None else float(R)))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--instances', type=int, default=400)
    a = ap.parse_args()
    rng = np.random.default_rng(MASTER_SEED)
    t0 = time.time()

    # ---------------- self-check on the definite arm ---------------------
    chk = np.random.default_rng(MASTER_SEED + 1)
    worst = 0.0
    for _ in range(25):
        n = int(chk.integers(2, 6)); mc = int(chk.integers(1, 4))
        M, A, mu = make_instance(chk, 'full', n, mc)
        p, d = primal(M, A, mu), dual(M, A, mu)
        if p is None or d is None:
            continue
        worst = max(worst, abs(p - d) / max(abs(p), abs(d),
                                            0.5 * float(mu @ M @ mu), 1e-9))
    ok = worst < 1e-5
    print(f'self-check: definite arm, worst relative gap {worst:.2e} -> '
          f'{"PASS" if ok else "FAIL"}', flush=True)
    if not ok:
        raise SystemExit('self-check failed; sweep not reported')

    rows = []
    for fam in FAMILIES:
        for k in range(a.instances):
            n = int(rng.integers(2, 7)); mc = int(rng.integers(1, 5))
            M, A, mu = make_instance(rng, fam, n, mc)
            p, d = primal(M, A, mu), dual(M, A, mu)
            if p is None or d is None:
                rows.append(dict(family=fam, n=n, m=mc, solved=False))
                continue
            gap = p - d
            # Normalising by |primal| alone is wrong here: lambda = 0 is always
            # feasible, so the optimum is frequently zero, and a 1e-15 difference
            # divided by a 1e-13 optimum reads as a gap of 1e-2. Use the scale the
            # problem itself supplies -- the objective at the feasible point
            # lambda = 0 -- so a gap is measured against something that is not
            # itself vanishing.
            scale = max(abs(p), abs(d), 0.5 * float(mu @ M @ mu), 1e-12)
            rel = gap / scale
            rec_scale = scale
            rec = dict(family=fam, n=n, m=mc, solved=True,
                       primal=p, dual=d, gap=gap, relative_gap=rel,
                       scale=rec_scale,
                       rank=int(np.linalg.matrix_rank(M, tol=1e-9)))
            if rel > FLAG:
                vp, vd = verify(M, A, mu)
                if vp is not None and vd is not None:
                    vrel = (vp - vd) / max(abs(vp), abs(vd),
                                           0.5 * float(mu @ M @ mu), 1e-12)
                    rec.update(verified_primal=vp, verified_dual=vd,
                               verified_relative_gap=vrel,
                               survives=bool(vrel > FLAG))
                    if vrel > FLAG:
                        probe = attainment_probe(M, A, mu)
                        vals = [q['dual'] for q in probe if q['dual'] is not None]
                        rec['attainment_probe'] = probe
                        rec['dual_still_climbing'] = bool(
                            len(vals) >= 2 and vals[-1] > vals[0] + 1e-9
                            and vals[-1] >= max(vals) - 1e-12)
                        rec['probe_closes_the_gap'] = bool(
                            vals and (vp - max(vals)) / max(
                                abs(vp), 0.5 * float(mu @ M @ mu), 1e-12) <= FLAG)
                else:
                    rec.update(survives=None)
            rows.append(rec)
        print(f'{fam} done  {time.time()-t0:.0f}s', flush=True)

    summary = {}
    for fam in FAMILIES:
        v = [r['relative_gap'] for r in rows if r['family'] == fam and r['solved']]
        summary[fam] = dict(solved=len(v),
                            max_relative_gap=float(np.max(v)) if v else None,
                            median_relative_gap=float(np.median(v)) if v else None,
                            flagged=int(sum(1 for x in v if x > FLAG)),
                            surviving=int(sum(1 for r in rows if r['family'] == fam
                                              and r.get('survives'))),
                            closed_by_raising_the_norm_cap=int(
                                sum(1 for r in rows if r['family'] == fam
                                    and r.get('probe_closes_the_gap'))),
                            still_climbing=int(
                                sum(1 for r in rows if r['family'] == fam
                                    and r.get('dual_still_climbing'))))
    total_gap = sum(s['surviving'] for s in summary.values())
    out = dict(provenance=_P.stamp(__file__), script='EXP_functional_duality.py',
               design='a search for a duality gap on the pair-region programme, over three '
                      'families: positive definite (the self-check, where strong duality is '
                      'classical), singular, and singular with the null space aligned to the '
                      'constraint normals; reported as a search for a counterexample, since '
                      'no number of instances without one settles the question positively',
               master_seed=MASTER_SEED, families=list(FAMILIES),
               instances_per_family=a.instances,
               self_check=dict(definite_worst_relative_gap=worst, passed=bool(ok)),
               flag_threshold=FLAG,
               summary=summary, instances_with_a_surviving_gap=total_gap,
               rows=rows, wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'instances with a gap surviving re-solution:', total_gap)
    for fam in FAMILIES:
        s = summary[fam]
        print(f"  {fam:10s} solved {s['solved']:4d}  max rel gap "
              f"{s['max_relative_gap']:.2e}  flagged {s['flagged']}  surviving "
              f"{s['surviving']}  closed by a larger cap {s['closed_by_raising_the_norm_cap']}"
              f"  still climbing {s['still_climbing']}")


if __name__ == '__main__':
    main()
