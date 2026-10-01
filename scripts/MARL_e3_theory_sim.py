#!/usr/bin/env python3
"""Traffic-free DIRECT CHECKS of corpus predictions on the E3 broadcast/relay scheduler (30/09 15:3x EDT; ledger L-176).

Model = PROTOCOL_HETERO_v0 prefix decoding + models/marl_relay merge (freshest copy per agent; a receiver keeps only its
own direct cache between steps), exactly as the relay evaluators, validated against the real AgeMirror ages (L-168: the
simulator's sticky order reproduced the real prefix-order age tail and agefirst's age distribution).  Capacity laws: iid
K ~ U{1..7}, low K ~ U{1..3}, cap<c> (stream capped at c), const<k> (every receiver K = k).

V-A  Paper A (frozen-surrogate STARVATION, linear REPAIR with no threshold).  The frozen surrogate is a sticky
     congestion-like ranking (adjacent swaps w.p. p; p = 0.1 reproduces the real prefix-order tail).  The repair mixes it
     with the rotation: each step, with probability beta the order is agefirst, else the sticky ranking.  Measured, over
     (receiver, other agent) pairs after burn-in: coverage, share of never-covered pairs, mean / P(age >= 4) / max age.
     Paper A's shape predictions (its own model, not transferred): starvation (beta = 0) gives exactly-zero information
     for starved cells; any beta > 0 buys some (no threshold); the gain is concave-to-linear near 0.
V-Q  ADAPTIVE (largest-deficit tracking vs quota) and Paper C's band.  Over a horizon T, each step's HEAD position
     (decoded by every other receiver) is apportioned to senders.  Targets w (uniform or weighted).  Rules:
     'deficit'  largest deficit t*w_i - N_i first (ADAPTIVE's online rule; for uniform w it is round-robin);
     'quota'    Balinski-Young quota method (house-monotone, within quota by construction): among senders whose
                upper quota allows one more seat, the one with the largest w_i/(N_i+1) (Jefferson divisor restricted);
     'sticky'   the frozen ranking (no targets).
     Reported: max over time and senders of |N_i - t*w_i| (quota error), and the max head gap (steps between two heads of
     the same sender).  ADAPTIVE's witness w = (17,1,1,3,1)/23 must reproduce deficit 26/23 at t = 11 for 'deficit'.
V-S  STRUCTURAL regime (information level): under const<k>, coverage and age as a function of k for raw packets
     (no relay: each packet carries its sender only) vs relay packets, for the sticky and the rotating order.
"""
from __future__ import annotations
import argparse, json, math
from fractions import Fraction
from pathlib import Path
import numpy as np

NEVER = -10 ** 9


def cap_sampler(kind, m):
    hi = m - 2
    if kind == 'iid' or kind.startswith('cap'):
        return lambda rng: rng.integers(1, hi + 1, size=m)
    if kind == 'low':
        return lambda rng: rng.integers(1, 4, size=m)
    if kind.startswith('const'):
        k = int(kind[5:]); return lambda rng: np.full(m, k)
    raise ValueError(kind)


def decode(order, K, i, cap):
    seq = [j for j in order if j != i][:K[i]]
    if cap is not None:
        head = set(order[:cap]); seq = [j for j in seq if j in head]
    return seq


def step(order, K, table, cache, t, m, cap, relay=True):
    new = np.full((m, m), NEVER, np.int64); S = []
    for i in range(m):
        s = decode(order, K, i, cap); S.append(s)
        best = cache[i].copy()
        if relay:
            for k in s:
                best = np.maximum(best, table[k])
        for k in s:
            best[k] = t
        best[i] = NEVER; new[i] = best
    for i in range(m):
        for k in S[i]:
            cache[i][k] = t
    return new, S


def agefirst(last, m):
    return tuple(sorted(range(m), key=lambda j: (0, j) if last[j] <= NEVER // 2 else (1, last[j], j)))


def sticky(prev, rng, m, p):
    o = list(prev)
    for a in range(m - 1):
        if rng.random() < p:
            o[a], o[a + 1] = o[a + 1], o[a]
    return tuple(o)


def run_mix(beta, cap_kind, m=9, N=26, episodes=300, seed=0, p=0.1, relay=True, burn=2):
    samp = cap_sampler(cap_kind, m); cap = int(cap_kind[3:]) if cap_kind.startswith('cap') else None
    ages, cov, never_pairs = [], [], []
    for e in range(episodes):
        rng = np.random.default_rng([seed, e, 17])
        last = np.full(m, NEVER, np.int64); prev = tuple(int(x) for x in rng.permutation(m))
        table = np.full((m, m), NEVER, np.int64); cache = np.full((m, m), NEVER, np.int64)
        seen = np.zeros((m, m), bool)
        for t in range(N):
            sk = sticky(prev, rng, m, p)
            order = agefirst(last, m) if rng.random() < beta else sk
            prev = sk                                   # the surrogate's own ranking keeps evolving
            K = samp(rng); table, S = step(order, K, table, cache, t, m, cap, relay)
            for s in S:
                for j in s:
                    last[j] = t
            if t >= burn:
                for i in range(m):
                    for j in range(m):
                        if i == j:
                            continue
                        if table[i, j] > NEVER // 2:
                            ages.append(t - table[i, j]); cov.append(1); seen[i, j] = True
                        else:
                            cov.append(0)
        never_pairs.append(float(((~seen) & ~np.eye(m, dtype=bool)).sum()) / (m * (m - 1)))
    a = np.asarray(ages)
    return dict(beta=beta, capacity=cap_kind, relay=relay, coverage=round(float(np.mean(cov)), 4),
                never_covered_pairs=round(float(np.mean(never_pairs)), 4), mean_age=round(float(a.mean()), 3) if len(a) else None,
                p_age_ge4=round(float((a >= 4).mean()), 4) if len(a) else None, max_age=int(a.max()) if len(a) else None)


def quota_run(w, T, rule, rng=None, p=0.1):
    """Apportion one head seat per step for T steps; returns max |N_i - t w_i| (exact Fractions) and max head gap."""
    m = len(w); N = [0] * m; lastpos = [-1] * m; maxdev = Fraction(0); maxgap = 0
    prev = list(range(m))
    for t in range(1, T + 1):
        if rule == 'deficit':                            # ADAPTIVE's rule: deficit BEFORE the step, D_i(t-1) = (t-1) w_i - N_i
            d = [(t - 1) * w[i] - N[i] for i in range(m)]; pick = max(range(m), key=lambda i: (d[i], -i))
        elif rule == 'quota':
            # Balinski-Young quota method: eligible if N_i + 1 <= ceil(t * w_i) (upper quota at house size t)
            elig = [i for i in range(m) if N[i] + 1 <= math.ceil(t * w[i])]
            if not elig:
                elig = list(range(m))
            pick = max(elig, key=lambda i: (w[i] / (N[i] + 1), -i))
        elif rule == 'sticky':
            prev = list(sticky(tuple(prev), rng, m, p)); pick = prev[0]
        else:
            raise ValueError(rule)
        N[pick] += 1
        if lastpos[pick] >= 0:
            maxgap = max(maxgap, t - lastpos[pick])
        lastpos[pick] = t
        for i in range(m):
            maxdev = max(maxdev, abs(N[i] - t * w[i]))
    for i in range(m):                                   # senders never (again) at the head count as a gap to the horizon
        maxgap = max(maxgap, T + 1 - lastpos[i] if lastpos[i] >= 0 else T + 1)
    return maxdev, maxgap


def main(a):
    out = dict(V_A=[], V_Q={}, V_S=[])
    for cap_kind in ['iid', 'low', 'cap4', 'cap2']:
        for beta in [0.0, 0.02, 0.05, 0.1, 0.25, 0.5, 1.0]:
            r = run_mix(beta, cap_kind, episodes=a.episodes); out['V_A'].append(r); print('V-A', json.dumps(r), flush=True)
    # V-Q: ADAPTIVE's witness, uniform targets, and a census over random weighted targets
    wit = [Fraction(x, 23) for x in (17, 1, 1, 3, 1)]
    d11 = None
    m = 5; N = [0] * m
    for t in range(0, 11):                             # the same rule as quota_run('deficit'): D_i(t) = t w_i - N_i(t) before the step
        d = [t * wit[i] - N[i] for i in range(m)]; pick = max(range(m), key=lambda i: (d[i], -i)); N[pick] += 1
    d11 = wit[0] * 11 - N[0]
    dev14, _ = quota_run(wit, 14, 'deficit')
    out['V_Q']['adaptive_witness'] = dict(counts_at_11=N, deficit_arm0_at_11=str(d11), reproduces_26_23=(d11 == Fraction(26, 23)), quota_run_max_dev_to_14=str(dev14))
    if d11 != Fraction(26, 23):
        raise SystemExit('SELF-CHECK FAIL: the deficit rule does not reproduce ADAPTIVE\'s witness')
    print('V-Q witness', out['V_Q']['adaptive_witness'], flush=True)
    uni = [Fraction(1, 9)] * 9
    for rule in ['deficit', 'quota']:
        dev, gap = quota_run(uni, 26 * 20, rule); out['V_Q'][f'uniform_{rule}'] = dict(max_quota_error=str(dev), max_head_gap=gap)
    rng = np.random.default_rng(5)
    sdev, sgap = [], []
    for _ in range(50):
        dev, gap = quota_run(uni, 26, 'sticky', rng=rng); sdev.append(float(dev)); sgap.append(gap)
    out['V_Q']['uniform_sticky'] = dict(mean_max_quota_error=round(float(np.mean(sdev)), 3), mean_max_head_gap=round(float(np.mean(sgap)), 2), horizon=26)
    print('V-Q uniform', {k: v for k, v in out['V_Q'].items() if k.startswith('uniform')}, flush=True)
    census = {'deficit': [0, 0, Fraction(0)], 'quota': [0, 0, Fraction(0)]}
    rng = np.random.default_rng(7)
    for _ in range(a.census):
        mm = int(rng.integers(3, 10)); d = int(rng.integers(mm, 64)); cuts = sorted(rng.choice(np.arange(1, d), size=mm - 1, replace=False))
        parts = np.diff([0] + list(cuts) + [d]); w = [Fraction(int(x), d) for x in parts]
        for rule in census:
            dev, _ = quota_run(w, 120, rule); census[rule][0] += 1; census[rule][1] += int(dev > 1); census[rule][2] = max(census[rule][2], dev)
    out['V_Q']['census'] = {r: dict(targets=c[0], violating_unit_quota=c[1], worst=str(c[2]), worst_float=round(float(c[2]), 4)) for r, c in census.items()}
    print('V-Q census', out['V_Q']['census'], flush=True)
    for relay in (False, True):
        for k in range(1, 8):
            for beta in (0.0, 1.0):
                r = run_mix(beta, f'const{k}', episodes=a.episodes // 2, relay=relay); out['V_S'].append(r); print('V-S', json.dumps(r), flush=True)
    Path(a.out).write_text(json.dumps(out, indent=1, default=str))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--episodes', type=int, default=300); p.add_argument('--census', type=int, default=2000)
    p.add_argument('--out', default='research/marl_budget/e3_theory_sim_20260930.json')
    main(p.parse_args())
