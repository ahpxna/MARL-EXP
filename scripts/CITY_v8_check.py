#!/usr/bin/env python3
"""v8 PPO-path and reward-B trace check (PROTOCOL_CITY_SPAT_PILOT_20261004 R1 / R2; review SPAT_PILOT_REVIEW §4).  One FT episode per arm
(traffic 0, END s, stochastic policy from an untrained Net), then:
  C1 segments: one vehicle each; consecutive seconds; end in {terminal, truncated}; truncated segments carry a bootstrap obs
  C2 actions: stored log-prob == Net.dist(obs).log_prob(u); a == squash(u); cmd == clip(sp + a, 0, .) and cmd == the value passed to
     SUMO's setSpeed (spy) for the same (t, vehicle)
  C3 GAE: an independent naive per-segment recursion equals V8.gae (advantages and returns)
  C4 reward B: every closed interval's reward equals an independent implementation of Eq. 9-10 on its logged (f, v, s, start-stop)
  C5 credit: the credited decision of each (interval, agent) is that agent's LAST decision on that light inside the interval, and the sum
     of credited rewards over decisions equals the sum over intervals x credited agents (dropped decisions excluded and counted)
  C6 arms: no-SPaT obs[:, 10:13] == 0 everywhere; SPaT valid == 1 for every decision under FT
  C7 gap path (synthetic): a truncated close pops the last decision, marks it dropped and bootstraps on its obs
Exit 1 on any failure.  Also prints throughput (sim seconds and wall seconds) for the budget decision."""
import math, os, sys, time
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402

END = int(os.environ.get('V8CHECK_END', '600'))


def eq910(f, v, s, ss):
    if ss:
        return -100.0
    if f <= 0.01:
        return (-5 + 5 * math.exp(v)) if s == 0 else (-5 + 5 * math.exp(v) - 10 * s)
    return -7 - 3 * math.exp(min(1000 * f, 30.0)) + 4 * math.exp(v) - 10 * s


def naive_gae(seg, net, g=V8.GAMMA, lam=V8.LAM, sc=V8.REWARD_SCALE):
    dec = seg['dec']; n = len(dec)
    with torch.no_grad():
        V = [float(net.value(torch.as_tensor(d['obs'][None]))[0]) for d in dec]
        boot = 0.0 if seg['end'] == 'terminal' else float(net.value(torch.as_tensor(seg['boot_obs'][None]))[0])
    A = [0.0] * n
    for k in reversed(range(n)):
        nv = V[k + 1] if k + 1 < n else boot
        d = dec[k]['rew'] * sc + g * nv - V[k]; A[k] = d + g * lam * (A[k + 1] if k + 1 < n else 0.0)
    return np.array(A), np.array(A) + np.array(V)


def run_arm(spat_on, bad):
    net = V8.Net(13); seed = 0; spy = []; orig = CE.ls.vehicle.setSpeed
    phases = defaultdict(list)                                       # tid -> [(t_start, phase)]
    o_reset = V8.PhaseRewardB._reset

    def reset(self, L, ph, _t=[0]):
        o_reset(self, L, ph); phases[[k for k, x in self.lights.items() if x is L][0]].append((CE.ls.simulation.getTime(), ph))
    V8.PhaseRewardB._reset = reset
    CE.ls.vehicle.setSpeed = lambda v, x: (spy.append((CE.ls.simulation.getTime(), v, float(x))), orig(v, x))[1]
    cars = V8.CarPPO(net, Q7.RHO, seed, spat_on, deterministic=False, record=True, reward='B'); t0 = time.perf_counter()
    try:
        CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, None, cars, end=END)
    finally:
        CE.ls.vehicle.setSpeed = orig; V8.PhaseRewardB._reset = o_reset
    wall = time.perf_counter() - t0; cars.finish(); segs = [s for s in cars.segments if s['dec']]; tag = 'SPaT' if spat_on else 'noSPaT'
    allD = [d for s in segs for d in s['dec']]
    print(f'{tag}: {END} s simulated in {wall:.1f} s wall; decisions {cars.stats["decisions"]}; segments {len(segs)}; intervals {len(cars.tracker.log)}; stats {cars.stats}')
    # C1
    for s in segs:
        if len({d['vid'] for d in s['dec']}) != 1 or any(b['t'] - a['t'] != 1 for a, b in zip(s['dec'], s['dec'][1:])) or s['end'] not in ('terminal', 'truncated') \
           or (s['end'] == 'truncated' and s['boot_obs'] is None):
            bad.append(f'{tag} C1 segment of {s["vid"]}'); break
    # C2
    O = torch.as_tensor(np.stack([d['obs'] for d in allD])); U = torch.as_tensor(np.array([d['u'] for d in allD], np.float32))
    with torch.no_grad():
        lp = net.dist(O).log_prob(U).numpy()
    if np.max(np.abs(lp - np.array([d['logp'] for d in allD]))) > 1e-4:
        bad.append(f'{tag} C2 log-prob mismatch')
    if np.max(np.abs(V8.squash(np.array([d['u'] for d in allD])) - np.array([d['a'] for d in allD]))) > 1e-5:   # actions are float32
        bad.append(f'{tag} C2 squash mismatch')
    if any(d['cmd'] > max(d['sp'] + d['a'], 0.0) + 1e-9 or d['cmd'] < 0 for d in allD):
        bad.append(f'{tag} C2 cmd outside clip(sp + a)')
    sp = {(t, v): x for t, v, x in spy}
    if any(abs(sp.get((d['t'], d['vid']), -99) - d['cmd']) > 1e-9 for d in allD):
        bad.append(f'{tag} C2 command passed to SUMO differs from the stored cmd')
    # C3
    b = V8.gae(cars.segments, net); A = np.concatenate([naive_gae(s, net)[0] for s in segs]); R = np.concatenate([naive_gae(s, net)[1] for s in segs])
    if b is None or np.max(np.abs(b[3] - A)) > 1e-4 or np.max(np.abs(b[4] - R)) > 1e-4:
        bad.append(f'{tag} C3 GAE mismatch')
    # C4
    if any(abs(eq910(x[3], x[4], x[5], x[6]) - x[7]) > 1e-6 * max(1, abs(x[7])) for x in cars.tracker.log):
        bad.append(f'{tag} C4 reward-B mismatch')
    # C5: reconstruct intervals per light from the reset log; credited = last decision per (agent, light) inside [start, next start)
    expect = defaultdict(float); n_expect = 0
    for t_end, tid, nvs, f, v, s, ss, r, br, ncr in cars.tracker.log:
        starts = [ts for ts, _ in phases[tid] if ts < t_end]; t_start = max(starts) if starts else 0
        last = {}
        cand = [d for d in all_decisions(cars) if d['tid'] == tid and t_start <= d['t'] < t_end]
        for d in cand:
            if d['vid'] not in last or d['t'] > last[d['vid']]['t']:
                last[d['vid']] = d
        for d in last.values():
            if not d.get('dropped'):
                expect[id(d)] += r; n_expect += 1
        if sum(1 for d in last.values() if not d.get('dropped')) != ncr:
            bad.append(f'{tag} C5 credited count mismatch at {tid} t {t_end}'); break
    got = {id(d): d['rew'] for d in all_decisions(cars) if d['rew'] != 0.0 and not d.get('dropped')}
    if set(got) != {k for k, x in expect.items() if x != 0.0} or any(abs(got[k] - expect[k]) > 1e-9 * max(1, abs(expect[k])) for k in got):
        bad.append(f'{tag} C5 credited rewards differ from the reconstruction')
    # C6
    obs = np.stack([d['obs'] for d in allD])
    if not spat_on and np.any(obs[:, 10:13] != 0):
        bad.append('noSPaT C6 SPaT inputs not zero')
    if spat_on and np.any(obs[:, 12] != 1.0):
        bad.append('SPaT C6 invalid SPaT under FT')
    return wall


def all_decisions(cars):
    out = [d for s in cars.segments for d in s['dec']]
    dropped = getattr(cars, '_dropped_log', [])
    return out + dropped


def c7(bad):
    class N:
        def value(self, O): return torch.zeros(len(O))
    c = V8.CarPPO(N(), 0.5, 0, False, record=True, reward=None)
    d1 = dict(vid='x', t=1, obs=np.ones(13, np.float32), u=0.0, logp=0.0, val=0.0, a=0.0, sp=0.0, cmd=0.0, rew=0.0, tid='A0')
    d2 = dict(d1, t=2, obs=np.full(13, 2, np.float32))
    c.open['x'] = dict(vid='x', dec=[d1, d2], end=None, boot_obs=None); c._close('x', 'truncated')
    s = c.segments[-1] if c.segments else None
    if not (s and len(s['dec']) == 1 and s['end'] == 'truncated' and np.all(s['boot_obs'] == 2) and d2.get('dropped')):
        bad.append('C7 gap path')


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1); bad = []
    # keep dropped decisions visible for C5 (they are excluded from credit sums but must be found as the 'last' decision)
    o_close = V8.CarPPO._close

    def close(self, v, end, boot_obs=None):
        seg = self.open.get(v)
        if seg and end == 'truncated' and seg['dec']:
            self.__dict__.setdefault('_dropped_log', []).append(seg['dec'][-1])
        return o_close(self, v, end, boot_obs)
    V8.CarPPO._close = close
    w = [run_arm(False, bad), run_arm(True, bad)]; c7(bad)
    print(f'throughput: {END} s of FT traffic in {np.mean(w):.1f} s wall per arm (untrained policy)')
    print('V8 CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
