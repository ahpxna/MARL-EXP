"""SUPPORT: does the decide/recover separation hold across the whole grid?

The paper reports twelve cells. Two questions it does not answer: whether the
decide threshold is flat in K everywhere or only on those cells, and whether the
recovery identity -- an inclusion-exclusion over events that are NOT independent
-- actually describes the process it is derived for.

Two experiments.

E2a, deterministic.  Invert both risks over a wide grid of (K, P, epsilon) and
record the least N meeting the tolerance.  The decide risk is R_dec = (1/2)(1-P)^N
and the recovery risk is R_rec = 1 - sum_k C(K,k) (-1/2)^k (1 - kP/K)^N.  The
recovery sum alternates in sign with binomial weights, so it loses about K bits to
cancellation; it is evaluated at high precision and checked against exact rational
arithmetic wherever the exact computation is affordable.

E2b, Monte Carlo.  Simulate the process the identity is derived for -- each
observation picks a class uniformly and resolves it with probability P -- and
compare the realised frequency of complete recovery with the identity.  The events
"class i is still unresolved" are dependent, because the draws compete for the same
N observations, so this is a real check on the identity rather than on arithmetic.

Self-checks, all of which must pass before any sweep result is reported:
  * R_rec at K=1 must equal R_dec exactly, in rational arithmetic, at every N;
  * the high-precision and exact-rational evaluations must agree;
  * the sandwich (1/2)Pr(U>0) <= R_rec <= Pr(U>0) must hold at every cell.
"""
import json
import time
import math
import argparse
from fractions import Fraction as F
from math import comb
from pathlib import Path

import numpy as np
from mpmath import mp, mpf, binomial

import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import EXP_provenance as _P

MASTER_SEED = 4242
BASE_DPS = 120


def dps_for(K):
    """Working precision for the recovery sum.

    The sum alternates with binomial weights, so the largest term exceeds the
    answer by roughly 2^K: it loses about K*log10(2) decimal digits to
    cancellation. Carry that, plus a fixed margin.
    """
    return int(BASE_DPS + math.ceil(K * 0.30103) + 40)


def r_dec_exact(P, N):
    return F(1, 2) * (1 - P) ** N


def r_rec_exact(K, P, N):
    return 1 - sum(comb(K, k) * F(-1, 2) ** k * (1 - k * P / K) ** N
                   for k in range(K + 1))


def r_rec_mp(K, P, N):
    mp.dps = dps_for(K)
    p = mpf(P.numerator) / mpf(P.denominator)
    return 1 - sum(binomial(K, k) * mpf(-1) ** k / mpf(2) ** k
                   * (1 - k * p / K) ** N for k in range(K + 1))


def pr_unresolved_any(K, P, N):
    """Pr(U > 0), the probability that some class is still unresolved."""
    mp.dps = dps_for(K)
    p = mpf(P.numerator) / mpf(P.denominator)
    # inclusion-exclusion on the union of "class i unresolved"
    return sum(binomial(K, k) * mpf(-1) ** (k + 1) * (1 - k * p / K) ** N
               for k in range(1, K + 1))


def least_N(risk, eps, cap):
    """Smallest N with risk(N) <= eps, by doubling then bisection."""
    lo, hi = 0, 1
    while hi <= cap and risk(hi) > eps:
        lo, hi = hi, hi * 2
    if hi > cap:
        return None
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if risk(mid) <= eps:
            hi = mid
        else:
            lo = mid
    return hi


def simulate(K, P, N, reps, rng):
    """Probability that the reported unsafe set is correct.

    The identity being tested is R_rec = 1 - E[(1/2)^U], where U counts the
    classes still unresolved after N observations and each of those is guessed
    with a fair coin. So the quantity to measure is E[(1/2)^U], not the
    probability that U = 0: reporting can be correct by luck. Averaging
    (1/2)^U directly rather than simulating the coins is the same expectation
    with less variance, and it still exercises the part of the identity that
    could be wrong -- the joint law of U, whose events compete for the same N
    observations and are therefore dependent.

    Returns the mean and the standard error of (1/2)^U over `reps` runs.
    """
    p = float(P)
    chunk = max(1, 4_000_000 // max(N, 1))
    acc, acc2, done = 0.0, 0.0, 0
    while done < reps:
        r = min(chunk, reps - done)
        cls = rng.integers(0, K, size=(r, N))
        hit = rng.random((r, N)) < p
        # scatter the hits straight into a (rep, class) table: looping over
        # classes would cost K passes over the whole draw
        ri, ci = np.nonzero(hit)
        resolved = np.zeros((r, K), dtype=bool)
        resolved[ri, cls[ri, ci]] = True
        unresolved = K - resolved.sum(axis=1)
        w = 0.5 ** unresolved
        acc += float(w.sum()); acc2 += float((w * w).sum())
        done += r
    mean = acc / reps
    var = max(acc2 / reps - mean * mean, 0.0)
    return mean, math.sqrt(var / reps)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--kmax', type=int, default=1024)
    ap.add_argument('--reps', type=int, default=400000)
    ap.add_argument('--sim-cells', type=int, default=200)
    ap.add_argument('--cap', type=int, default=2000000)
    ap.add_argument('--sim-nmax', type=int, default=50000)
    a = ap.parse_args()
    t0 = time.time()

    KS = [k for k in (1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128,
                      192, 256, 384, 512, 768, 1024) if k <= a.kmax]
    PS = [F(1, 20), F(1, 10), F(1, 5), F(1, 4), F(1, 3), F(1, 2), F(2, 3),
          F(3, 4), F(9, 10)]
    EPS = [F(1, 10), F(1, 20), F(1, 100), F(1, 1000), F(1, 100000), F(1, 1000000)]

    # ---------------- self-checks --------------------------------------
    sc = {'k1_identity': True, 'mp_vs_exact': 0.0, 'sandwich': True}
    for P in PS:
        for N in (1, 2, 5, 11, 30):
            if r_rec_exact(1, P, N) != r_dec_exact(P, N):
                sc['k1_identity'] = False
    for K in (2, 3, 4, 6, 8):
        for P in (F(1, 4), F(1, 2), F(3, 4)):
            for N in (3, 9, 25):
                ex = float(r_rec_exact(K, P, N))
                ap_ = float(r_rec_mp(K, P, N))
                if ex > 0:
                    sc['mp_vs_exact'] = max(sc['mp_vs_exact'], abs(ex - ap_) / ex)
    for K in (2, 4, 8, 16):
        for P in (F(1, 4), F(1, 2)):
            for N in (5, 20, 60):
                rr = r_rec_mp(K, P, N); u = pr_unresolved_any(K, P, N)
                if not (u / 2 - mpf('1e-40') <= rr <= u + mpf('1e-40')):
                    sc['sandwich'] = False
    passed = sc['k1_identity'] and sc['mp_vs_exact'] < 1e-12 and sc['sandwich']
    print(f"self-check: K=1 identity {sc['k1_identity']}; high-precision vs exact "
          f"{sc['mp_vs_exact']:.1e}; sandwich {sc['sandwich']} -> "
          f"{'PASS' if passed else 'FAIL'}", flush=True)
    if not passed:
        raise SystemExit('self-check failed; sweep not reported')

    # ---------------- E2a: exact thresholds ----------------------------
    rows = []
    for eps in EPS:
        for P in PS:
            nd = least_N(lambda N: r_dec_exact(P, N), eps, a.cap)
            for K in KS:
                nr = least_N(lambda N: r_rec_mp(K, P, N), mpf(eps.numerator) / eps.denominator,
                             a.cap)
                rows.append(dict(K=K, P=str(P), eps=str(eps), N_decide=nd, N_recover=nr,
                                 ratio=(nr / nd if (nd and nr) else None)))
            print(f'eps={eps} P={P} N_dec={nd}  {time.time()-t0:.0f}s', flush=True)

    # Flatness in K is structural, not measured: the proved decide expression
    # contains no K, so N_decide is computed once per (P, eps). It is recorded
    # as a property of the formula and must not be read as an empirical finding.
    flat = len({r['N_decide'] for r in rows
                if r['P'] == '1/2' and r['eps'] == '1/100'}) == 1

    # What IS measurable is how the recovery threshold grows. The coupon-collector
    # reading predicts N_rec ~ (K/P)(ln K + ln(1/eps)); fit its constant and see
    # how well the shape holds across the grid.
    fits = []
    for eps in EPS:
        for P in PS:
            sub = [r for r in rows if r['P'] == str(P) and r['eps'] == str(eps)
                   and r['N_recover'] and r['K'] > 1]
            if len(sub) < 4:
                continue
            x = np.array([(k['K'] / float(P)) * (math.log(k['K'])
                          + math.log(1 / float(eps))) for k in sub])
            y = np.array([k['N_recover'] for k in sub], dtype=float)
            c = float((x * y).sum() / (x * x).sum())
            ss = float(((y - c * x) ** 2).sum())
            st = float(((y - y.mean()) ** 2).sum())
            fits.append(dict(P=str(P), eps=str(eps), constant=c,
                             r2=(1 - ss / st if st > 0 else None),
                             max_rel_error=float(np.max(np.abs(c * x - y) / y))))
    mono = all(
        all(x['N_recover'] >= y['N_recover']
            for x, y in zip(sorted([r for r in rows if r['P'] == p and r['eps'] == e],
                                   key=lambda r: r['K'])[1:],
                            sorted([r for r in rows if r['P'] == p and r['eps'] == e],
                                   key=lambda r: r['K'])[:-1]))
        for p in {r['P'] for r in rows} for e in {r['eps'] for r in rows})

    # ---------------- E2b: Monte Carlo ---------------------------------
    rng = np.random.default_rng(MASTER_SEED)
    sims = []
    budget = a.sim_cells
    for r in rows:
        if budget <= 0 or r['N_recover'] is None or r['N_recover'] > a.sim_nmax:
            continue
        K, P, N = r['K'], F(r['P']), r['N_recover']
        # a long horizon costs proportionally more per replication, so trade
        # replications for horizon and report the standard error either way
        reps_eff = int(min(a.reps, max(20000, 40_000_000 // max(N, 1))))
        print(f'  sim K={K} P={P} N={N} reps={reps_eff}  {time.time()-t0:.0f}s', flush=True)
        got, se = simulate(K, P, N, reps_eff, rng)
        pred = 1 - float(r_rec_mp(K, P, N))
        sims.append(dict(K=K, P=r['P'], N=N, measured_correct=got, predicted_correct=pred,
                         deviation=got - pred, se=se, reps=reps_eff))
        budget -= 1
    dev = [abs(s['deviation']) for s in sims]
    z = [abs(s['deviation']) / s['se'] for s in sims if s['se'] > 0]

    out = dict(provenance=_P.stamp(__file__), script='EXP_support_thresholds.py',
               design='exact inversion of the decide and recovery risks over a grid of '
                      '(K, P, epsilon), at 240-digit precision because the recovery sum '
                      'alternates; plus a Monte Carlo of the resolution process compared '
                      'against the inclusion-exclusion identity',
               master_seed=MASTER_SEED, K_values=KS, P_values=[str(p) for p in PS],
               eps_values=[str(e) for e in EPS], reps=a.reps,
               precision_dps={str(k): dps_for(k) for k in KS},
               self_check=dict(k1_identity=sc['k1_identity'],
                               mp_vs_exact_worst_relative=sc['mp_vs_exact'],
                               sandwich_holds=sc['sandwich'], passed=bool(passed)),
               decide_flat_in_K_by_construction=bool(flat), recover_monotone_in_K=bool(mono),
               coupon_collector_fits=fits,
               rows=rows, sims=sims,
               sim_max_abs_deviation=(max(dev) if dev else None),
               sim_max_z=(max(z) if z else None),
               wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'cells', len(rows), 'sims', len(sims),
          'decide flat', flat, 'recover monotone', mono,
          'sim max|dev|', round(max(dev), 5) if dev else None,
          'max z', round(max(z), 2) if z else None)


if __name__ == '__main__':
    main()
