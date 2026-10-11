#!/usr/bin/env python3
"""E5-G6 (PROTOCOL_E3_E12_E14_G3_G6_20261004, frozen 01:21 EDT 04/10): offline sequential "find one adequate upgrade" on Q7b's rows.
Candidates per training seed t: FT, RL-H, RL-J, RL-C30 ... RL-C120 (9).  Per evaluation seed s (100-104), paired vs ACT:
  g_s = timeloss(ACT, human, s) - timeloss(U, human, s)          (the light's own gain)
  r_s = approach_cost(L-ACT | U, s) - approach_cost(L-ACT | ACT, s)  (the old fleet's regression)
Adequate: g >= gamma and r <= eps (gamma = 5 % of mean timeloss(ACT, human), eps = 5 % of mean approach_cost(L-ACT | ACT), per t);
truth = the 5-seed means.  RACING: every round each surviving candidate gets one more seed (random permutation of its 5 seeds);
from n = 2, two-sided t-bounds at level alpha / (2 * 9 * 4); eliminate if UCB(g) < gamma or LCB(r) > eps; accept the best-mean-g
candidate with LCB(g) >= gamma and UCB(r) <= eps.  ORDERED: candidates one at a time (RL-H, RL-C120 ... RL-C30, RL-J, FT) to n = 5
or a decision.  2000 permutation orders per t, rng 0.  Metrics: paid rollouts / 45, acceptance, false acceptance, missed,
retained gain.  GO (live run) iff pooled paid <= 60 % of full AND false acceptance <= 5 % AND mean retained gain >= 80 %.
SELF-CHECKS: every (t, candidate) has 5 paired seeds; the full-evaluation decisions are recomputed from the rows; the source of the
rows (eval manifests) is hashed into the manifest."""
from __future__ import annotations
import argparse, hashlib, json, time
from pathlib import Path
import numpy as np
from scipy import stats

ROOT = Path(__file__).resolve().parents[1]; Q7B = ROOT / 'research/city_sim/q7b_contract_20261002'
CANDS = ['FT', 'RL-H', 'RL-J', 'RL-C30', 'RL-C40', 'RL-C50', 'RL-C60', 'RL-C80', 'RL-C120']
ORDER = ['RL-H', 'RL-C120', 'RL-C80', 'RL-C60', 'RL-C50', 'RL-C40', 'RL-C30', 'RL-J', 'FT']
SEEDS = [100, 101, 102, 103, 104]


def data():
    rows = []
    for t in range(4):
        rows += json.loads((Q7B / f'eval_t{t}.json').read_text())
    D = {}
    for t in range(4):
        R = {(x['light'], x['fleet'], x['seed']): x for x in rows if x['t'] == t}
        tl0 = np.mean([R[('ACT', 'human', s)]['timeloss'] for s in SEEDS]); ac0 = np.mean([R[('ACT', 'L-ACT', s)]['approach_cost'] for s in SEEDS])
        g = {U: np.array([R[('ACT', 'human', s)]['timeloss'] - R[(U, 'human', s)]['timeloss'] for s in SEEDS]) for U in CANDS}
        r = {U: np.array([R[(U, 'L-ACT', s)]['approach_cost'] - R[('ACT', 'L-ACT', s)]['approach_cost'] for s in SEEDS]) for U in CANDS}
        assert all(len(g[U]) == 5 and len(r[U]) == 5 for U in CANDS)
        D[t] = dict(g=g, r=r, tl0=float(tl0), ac0=float(ac0))
    return D


def bounds(x, lvl):
    n = len(x); m = x.mean(); se = x.std(ddof=1) / np.sqrt(n); q = stats.t.ppf(1 - lvl / 2, n - 1)
    return m - q * se, m + q * se


def run(d, gam, eps, mode, rng, alpha):
    lvl = alpha / (2 * len(CANDS) * 4); perm = {U: rng.permutation(5) for U in CANDS}; n = {U: 0 for U in CANDS}; paid = 0
    alive = list(CANDS) if mode == 'racing' else []
    queue = list(ORDER)
    while True:
        if mode == 'ordered':
            if not alive:
                if not queue:
                    return None, paid
                alive = [queue.pop(0)]
        for U in alive:
            n[U] += 1; paid += 1
        acc = []
        for U in list(alive):
            if n[U] < 2:
                continue
            idx = perm[U][:n[U]]; gl, gu = bounds(d['g'][U][idx], lvl); rl, ru = bounds(d['r'][U][idx], lvl)
            if gu < gam or rl > eps:
                alive.remove(U); continue
            if gl >= gam and ru <= eps:
                acc.append((d['g'][U][idx].mean(), U))
        if acc:
            return max(acc)[1], paid
        alive = [U for U in alive if n[U] < 5]
        if mode == 'racing' and not alive:
            return None, paid


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); t0 = time.perf_counter()
    src = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__)] + sorted(Q7B.glob('eval_t*.json'))}
    D = data(); res = {}; lines = []
    for gp in a.gammas:
        for ep in a.epss:
            key = f'gamma{gp}_eps{ep}'; res[key] = {}
            for mode in ('racing', 'ordered'):
                agg = dict(paid=[], acc=[], false=[], missed=[], retained=[], full_cert=[])
                for t, d in D.items():
                    gam, eps = gp / 100 * d['tl0'], ep / 100 * d['ac0']
                    truth = {U: bool(d['g'][U].mean() >= gam and d['r'][U].mean() <= eps) for U in CANDS}
                    best = max([d['g'][U].mean() for U in CANDS if truth[U]], default=None)
                    lvl = a.alpha / (2 * len(CANDS) * 4)
                    cert = [U for U in CANDS if bounds(d['g'][U], lvl)[0] >= gam and bounds(d['r'][U], lvl)[1] <= eps]
                    rng = np.random.default_rng([0, t, int(gp * 10), int(ep * 10)])
                    for _ in range(a.reps):
                        U, paid = run(d, gam, eps, mode, rng, a.alpha)
                        agg['paid'].append(paid / 45); agg['acc'].append(U is not None)
                        agg['false'].append(U is not None and not truth[U]); agg['missed'].append(U is None and best is not None)
                        if best is not None:
                            agg['retained'].append(0.0 if U is None else d['g'][U].mean() / best)
                    agg['full_cert'].append(dict(t=t, adequate_truth=[U for U in CANDS if truth[U]], certified_at_n5=cert,
                                                 gamma=gam, eps=eps))
                s = {k: float(np.mean(v)) for k, v in agg.items() if k != 'full_cert'}
                s['retained_n'] = len(agg['retained']); s['full'] = agg['full_cert']
                go = s['paid'] <= 0.6 and s['false'] <= 0.05 and (s['retained'] >= 0.8 if agg['retained'] else False)
                s['GO'] = bool(go); res[key][mode] = s
                lines.append(f"{key} {mode:7s}: paid {s['paid']:.2f} of full, accept {s['acc']:.2f}, false {s['false']:.3f}, missed {s['missed']:.2f}, "
                             f"retained {s['retained']:.2f} (n {s['retained_n']}) -> {'GO' if go else 'NO-GO'}")
            lines.append(f"   truth / certified at n=5 per t: " + '; '.join(f"t{x['t']}: adequate {x['adequate_truth']} cert {x['certified_at_n5']}" for x in res[key]['racing']['full']))
    prim = res[f'gamma{5.0}_eps{5.0}']['racing']
    lines.insert(0, f"G6 PRIMARY (gamma 5 %, eps 5 %, racing): {'GO (a live run is justified)' if prim['GO'] else 'NO-GO (offline shows no saving that meets the rule)'}")
    if src != {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__)] + sorted(Q7B.glob('eval_t*.json'))}:
        raise RuntimeError('source changed during run')
    (out / 'result.json').write_text(json.dumps(res, indent=1)); (out / 'report.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), source_sha256=src,
                                                       seconds=time.perf_counter() - t0), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', required=True); p.add_argument('--reps', type=int, default=2000); p.add_argument('--alpha', type=float, default=0.05)
    p.add_argument('--gammas', type=float, nargs='+', default=[2.5, 5.0, 7.5]); p.add_argument('--epss', type=float, nargs='+', default=[2.5, 5.0, 10.0])
    main(p.parse_args())
