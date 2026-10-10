#!/usr/bin/env python3
"""R10 credit diagnostic (04/10/2026; requested by the R8-R10 progress audit §4; a DIAGNOSTIC, not an endpoint; the running v11 trainers
and their files are not touched).  One TRAINING-mode episode (record=True, stochastic, 3600 s) of CarPPOL with a COPY of a v11 checkpoint
(or a fresh zero-init net), with an independent per-second logger wrapped around the step:
  * every (vehicle, second) cost credited to an open segment is logged with the time of the decision that receives it;
  * before the episode cut, the last decision of every open segment is recorded (its accumulated reward and elapsed seconds), then
    finish() applies the inherited truncation (pop the last decision, bootstrap the previous one on the popped decision's observation).
Reports: (A) cost dropped by truncation / total credited cost, dropped elapsed seconds, and a bookkeeping check (logged per-second costs
summed per decision == the decision's reward); (B) seconds between consecutive decisions in a segment and seconds credited per decision,
and the per-segment discounted return with gamma per DECISION (what V8.gae uses) vs gamma per SECOND (cost discounted at its own second).
Usage: CITY_v11_credit_diag.py CKPT|fresh TRAIN_SEED"""
import os, shutil, sys, tempfile
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_fleet_v9 as V9  # noqa: E402
import scripts.CITY_fleet_v10 as V10  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402

if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1); torch.manual_seed(0)
    src, seed = sys.argv[1], int(sys.argv[2]); net = V9.NetR(7)
    if src != 'fresh':
        tmp = Path(tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))) / 'ckpt_copy.pt'; shutil.copy(src, tmp)
        net.load_state_dict(torch.load(tmp, weights_only=False)['net'])
    cars = V11.CarPPOL(net, Q7.RHO, seed, deterministic=False, record=True); LOG = []; inner = cars.step

    def step(t):
        ls = CE.ls
        for v, seg in cars.open.items():
            try:
                c = V10.dense_cost(ls, v)
            except Exception:
                c = None
            if c is not None:
                LOG.append((v, t, seg['dec'][-1]['t'], c))
        inner(t)
    cars.step = step
    CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, None, cars, end=3600); T = 3600
    last = {v: (seg['dec'][-1]['t'], -seg['dec'][-1]['rew']) for v, seg in cars.open.items() if seg['dec']}
    allD = [d for s in cars.segments for d in s['dec']] + [d for s in cars.open.values() for d in s['dec']]
    total = -sum(d['rew'] for d in allD); dropped = sum(c for _, c in last.values()); el = np.array([T - t0 for t0, _ in last.values()])
    agg = {}
    for v, t, td, c in LOG:
        agg[(v, td)] = agg.get((v, td), 0.0) + c
    bk = max(abs(-d['rew'] - agg.get((d['vid'], d['t']), 0.0)) for d in allD)
    cars.finish()
    gaps = np.array([b['t'] - a['t'] for s in cars.segments for a, b in zip(s['dec'], s['dec'][1:])])
    secs = {}
    for v, t, td, c in LOG:
        secs[(v, td)] = secs.get((v, td), 0) + 1
    dur = np.array(list(secs.values()))
    g = V8.GAMMA; rel = []
    for s in cars.segments:
        if len(s['dec']) < 2:
            continue
        t0 = s['dec'][0]['t']; Rdec = sum(g ** k * d['rew'] for k, d in enumerate(s['dec']))
        Rsec = -sum(g ** (t - t0) * c for v, t, td, c in LOG if v == s['vid'] and td >= t0 and td <= s['dec'][-1]['t'])
        if Rsec != 0:
            rel.append(Rdec / Rsec)
    rel = np.array(rel)
    print(f'== R10 credit diagnostic: {src} on TRAIN seed {seed} (3600 s, training mode)')
    print(f'decisions {len(allD)}, segments closed {len(cars.segments)}, open at the cut {len(last)}, stats popped {cars.stats["popped"]} (with reward {cars.stats.get("popped_with_reward", 0)})')
    print(f'(A) total credited cost {total:.1f}; dropped at the cut {dropped:.1f} = {100 * dropped / total:.2f} %; dropped elapsed seconds after the last '
          f'decision: median {np.median(el):.0f}, p90 {np.percentile(el, 90):.0f}, max {el.max():.0f}; bookkeeping max |reward - logged sum| {bk:.2e}')
    print(f'(B) seconds between consecutive decisions in a segment: n {len(gaps)}, share == 1 s {np.mean(gaps == 1):.3f}, median {np.median(gaps):.0f}, '
          f'p90 {np.percentile(gaps, 90):.0f}, p99 {np.percentile(gaps, 99):.0f}, max {gaps.max()}; gaps > 10 s: {np.mean(gaps > 10):.3f}')
    print(f'    seconds credited per decision: median {np.median(dur):.0f}, mean {dur.mean():.2f}, p90 {np.percentile(dur, 90):.0f}, max {dur.max()}')
    print(f'    per-segment discounted return, gamma per decision / gamma per second (segments with >= 2 decisions, n {len(rel)}): '
          f'median {np.median(rel):.3f}, p10 {np.percentile(rel, 10):.3f}, p90 {np.percentile(rel, 90):.3f}')
