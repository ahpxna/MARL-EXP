#!/usr/bin/env python3
"""E1a-adaptive: does adaptivity remove the log|Amb| factor of T2?  (numerical diagnostic)

Model: the exact needle class of LeanMarlRepairCalibrationV1.  M = |Amb| ambiguous repairs,
unit-Gaussian excess observations, needle height beta; worlds = null + M needle worlds.
Correct output: P at the null world, T at needle world T (Acc; uniform-gap gains).

v2 (27/09): v1 is unchanged; this version fixes the decoder DESCRIPTION flagged by
MARL_E1_INDEPENDENT_AUDIT_20260927 §6 and makes the Monte-Carlo check execute the decoder literally.
The error formulas are those of v1; they are exact for the decoder stated here.

Designs, both with EXACT error formulas (independent Gaussian block means):
  fixed      n rollouts on every repair, fire if mean > t (t optimised); output the FIRST fired
             repair in index order, else P (the decoder `rdec` of LeanMarlRepairCalibrationV1).
             Null error = P(any fires) = 1-(1-p)^M; the needle is placed at the WORST (last) index,
             needle error = 1 - s(1-p)^(M-1).  Cost M*n in every world.
  two-stage  screen: n1 rollouts on every repair, keep if mean1 > t1; confirm: n2 FRESH
             rollouts on each survivor, fire if mean2 > t2; output the first confirmed survivor,
             else P; needle at the worst index.  Expected cost M*n1 + E[#survivors]*n2.
Each design is optimised over its grid to minimise the worst-world (expected) cost subject to
worst-world error <= alpha.

Compared with the COMPILED bounds (LeanMarlRepairCalibrationV1, LeanMarlCalibrationGapV1):
  sched_calibration_lower  fixed schedules:  cost*beta^2/2 >= M((1-a)log(M/(2a)) - log 2)
  calibration_lower        any protocol, null world:  E0[cost]*beta^2/2 >= M((1-a)log(1/a) - log 2)
  own_world_sum            any protocol:  sum_T E_T[N_T]*beta^2/2 >= M((1-a)log(M/(2a)) - log 2)
Self-checks (refuse to write results on failure): the three bounds hold for the optimised
designs (they must: the designs are in the classes), and a Monte-Carlo run reproduces the
analytic errors of one optimised two-stage design.
This is NOT a theorem: the two-stage upper bound is not proved.
"""
from __future__ import annotations
import argparse, hashlib, json, math, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
_erfc = np.frompyfunc(math.erfc, 1, 1)


def Q(x):
    """Gaussian upper tail."""
    return (0.5 * _erfc(np.asarray(x, dtype=float) / math.sqrt(2))).astype(float)


def none_of(M, p):
    """(1 - p)^M, stable."""
    return np.exp(M * np.log1p(-np.minimum(p, 1 - 1e-300)))


def ngrid(lo, hi, k):
    return np.unique(np.round(np.geomspace(lo, hi, k)).astype(int))


def fixed_opt(M, beta, alpha, ns, ts):
    n = ns[:, None]; t = ts[None, :]
    pf = Q(t * np.sqrt(n))                    # a null repair fires
    ph = Q((t - beta) * np.sqrt(n))           # the needle fires
    err_null = 1 - none_of(M, pf)
    err_needle = 1 - ph * none_of(M - 1, pf)
    ok = np.maximum(err_null, err_needle) <= alpha
    cost = np.where(ok, M * n * np.ones_like(t), np.inf)
    i, j = np.unravel_index(np.argmin(cost), cost.shape)
    if not np.isfinite(cost[i, j]):
        return None
    return dict(n=int(ns[i]), t=float(ts[j]), cost=float(cost[i, j]),
                err_null=float(err_null[i, j]), err_needle=float(err_needle[i, j]))


def two_stage_opt(M, beta, alpha, n1s, t1s, n2s, t2s):
    n1 = n1s[:, None, None, None]; t1 = t1s[None, :, None, None]
    n2 = n2s[None, None, :, None]; t2 = t2s[None, None, None, :]
    p1 = Q(t1 * np.sqrt(n1)); s1 = Q((t1 - beta) * np.sqrt(n1))
    p2 = Q(t2 * np.sqrt(n2)); s2 = Q((t2 - beta) * np.sqrt(n2))
    fa = p1 * p2                                # a null repair survives AND fires
    err_null = 1 - none_of(M, fa)
    err_needle = 1 - s1 * s2 * none_of(M - 1, fa)
    cost_null = M * n1 + M * p1 * n2
    cost_needle = M * n1 + ((M - 1) * p1 + s1) * n2
    worst_cost = np.maximum(cost_null, cost_needle)
    ok = np.maximum(err_null, err_needle) <= alpha
    obj = np.where(ok, worst_cost, np.inf)
    idx = np.unravel_index(np.argmin(obj), obj.shape)
    if not np.isfinite(obj[idx]):
        return None
    a, b, c, d = idx
    F = lambda x: np.broadcast_to(x, obj.shape)
    cost_null, cost_needle, err_null, err_needle = F(cost_null), F(cost_needle), F(err_null), F(err_needle)
    return dict(n1=int(n1s[a]), t1=float(t1s[b]), n2=int(n2s[c]), t2=float(t2s[d]),
                worst_expected_cost=float(obj[idx]), cost_null=float(cost_null[idx]),
                cost_needle=float(cost_needle[idx]), err_null=float(err_null[idx]),
                err_needle=float(err_needle[idx]),
                own_arm_needle_world=float(F(n1 + s1 * n2)[idx]))


def mc_two_stage(M, beta, d, trials, rng):
    """Monte-Carlo errors of the declared decoder, executed literally: output = first fired
    index (or none); the needle sits at the LAST index (the worst position)."""
    out = {}
    for world in ('null', 'needle'):
        mu = np.zeros(M)
        if world == 'needle':
            mu[M - 1] = beta
        e = 0
        done = 0
        while done < trials:
            b = min(20000, trials - done)
            m1 = mu + rng.normal(0, 1 / math.sqrt(d['n1']), size=(b, M))
            surv = m1 > d['t1']
            m2 = mu + rng.normal(0, 1 / math.sqrt(d['n2']), size=(b, M))
            fired = surv & (m2 > d['t2'])
            first = np.where(fired.any(1), fired.argmax(1), -1)       # decoder output: first fired or P
            if world == 'null':
                e += int((first != -1).sum())
            else:
                e += int((first != M - 1).sum())
            done += b
        out[world] = e / trials
    return out


def bounds(M, beta, alpha):
    c = beta ** 2 / 2
    return dict(sched_lower=M * max(0.0, (1 - alpha) * math.log(M / (2 * alpha)) - math.log(2)) / c,
                null_lower=M * max(0.0, (1 - alpha) * math.log(1 / alpha) - math.log(2)) / c,
                own_world_sum_lower=M * max(0.0, (1 - alpha) * math.log(M / (2 * alpha)) - math.log(2)) / c,
                proved_upper=M * math.ceil(8 * math.log(M / alpha) / beta ** 2))


def main(a):
    t0 = time.perf_counter()
    rng = np.random.default_rng(a.seed)
    src = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    beta = 1.0
    Ms = [int(x) for x in a.Ms.split(',')]
    alphas = [float(x) for x in a.alphas.split(',')]
    ns = ngrid(1, a.nmax, a.gridn)
    ts = np.linspace(0.0, beta, a.gridt)
    n1s = ngrid(1, a.nmax, a.gridn); n2s = ngrid(1, a.nmax, a.gridn)
    rows, failures = [], []
    for alpha in alphas:
        for M in Ms:
            B = bounds(M, beta, alpha)
            fx = fixed_opt(M, beta, alpha, ns, ts)
            ts2 = two_stage_opt(M, beta, alpha, n1s, np.linspace(-0.5 * beta, beta, a.gridt), n2s, ts)
            if fx is None or ts2 is None:
                failures.append(f'grid too small at M={M} alpha={alpha}')
                continue
            c = beta ** 2 / 2
            if fx['cost'] * c < B['sched_lower'] * c - 1e-9:
                failures.append(f'sched_calibration_lower violated M={M} a={alpha}')
            if ts2['cost_null'] < B['null_lower'] - 1e-9:
                failures.append(f'calibration_lower violated M={M} a={alpha}')
            if M * ts2['own_arm_needle_world'] < B['own_world_sum_lower'] - 1e-9:
                failures.append(f'own_world_sum violated M={M} a={alpha}')
            row = dict(M=M, alpha=alpha, beta=beta, **B, fixed=fx, two_stage=ts2,
                       fixed_over_two_stage=fx['cost'] / ts2['worst_expected_cost'],
                       two_stage_over_null_lower=ts2['worst_expected_cost'] / B['null_lower'],
                       fixed_over_sched_lower=fx['cost'] / B['sched_lower'])
            rows.append(row)
            print(f"a={alpha} M={M:6d}: fixed {fx['cost']:9.0f} (lower {B['sched_lower']:9.0f})  "
                  f"two-stage worst E[cost] {ts2['worst_expected_cost']:9.1f} (null lower {B['null_lower']:8.0f})  "
                  f"ratio fixed/two-stage {row['fixed_over_two_stage']:.2f}", flush=True)
    if not rows:
        print('no feasible design on the grid:', *failures, sep='\n  ')
        raise SystemExit(1)
    # Monte-Carlo check of one design
    chk = rows[min(2, len(rows) - 1)]
    mc = mc_two_stage(chk['M'], beta, chk['two_stage'], a.mc, rng)
    se = math.sqrt(chk['alpha'] * (1 - chk['alpha']) / a.mc)
    for w, key in (('null', 'err_null'), ('needle', 'err_needle')):
        if abs(mc[w] - chk['two_stage'][key]) > 5 * se + 1e-3:
            failures.append(f'MC {w} error {mc[w]:.4f} vs analytic {chk["two_stage"][key]:.4f}')
    if failures or not rows:
        print('SELF-CHECK FAILED, not writing results:', *failures, sep='\n  ')
        raise SystemExit(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    (out / 'results.json').write_text(json.dumps(dict(
        source_sha256=src, args=vars(a), rows=rows,
        mc_check=dict(M=chk['M'], alpha=chk['alpha'], mc=mc, trials=a.mc),
        seconds=time.perf_counter() - t0,
        evidence_class='NUMERICAL DIAGNOSTIC on the exact T2 needle model; exact error formulas; '
                       'the two-stage upper bound is not a theorem'), indent=1))
    print('written', out / 'results.json', f'{time.perf_counter() - t0:.1f}s')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--Ms', default='4,16,64,256,1024,4096,16384,65536')
    p.add_argument('--alphas', default='0.05,0.01')
    p.add_argument('--nmax', type=int, default=200)
    p.add_argument('--gridn', type=int, default=48)
    p.add_argument('--gridt', type=int, default=31)
    p.add_argument('--mc', type=int, default=200000)
    p.add_argument('--seed', type=int, default=0)
    p.add_argument('--out', required=True)
    main(p.parse_args())
