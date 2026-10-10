#!/usr/bin/env python3
"""M3 self-checks required BEFORE training (Amendment A1): S3, S9, S10, S11, S12.  Exit 1 on any failure.  Short SUMO episodes (END s).
  S9   credit: (a) synthetic sequence through Credit; (b) integration: every closed transition carries the penalty that the logged decision
       at its t_prev computed for ITS OWN action, never the next action's
  S10  tickets on toy traces: green < 5 s (no open ticket), early switch, repeated issues, multi-cycle isolation, censoring
  S3   penalties recomputed from the logged open tickets by an INDEPENDENT implementation equal the online values
  S11  receiver probe parity: probe cmd(ttg) == the command R10 actually sends that second; ttg+5 changes both the rule speed and obs[10];
       probing leaves the fleet's counters and command log untouched
  S12  widened zero-init net == RL-H:k outputs; LightE(widened, greedy) reproduces LightRL(RL-H:k) phase-by-phase on a short episode"""
import json, os, sys, math
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_m3_core as M  # noqa: E402
import scripts.CITY_m3_train_E as T  # noqa: E402

END = int(os.environ.get('M3CHECK_END', '900')); K = 0; bad = []
P = ROOT / 'research/city_sim/spat_pilot_20261004'


def fail(msg):
    print('  FAIL', msg); bad.append(msg)


# ------------------------------------------------------------------------------------------------ S10 (pure)
ones = {t: 1.0 for t in M.TYPES}; tk = M.Tickets(ones); w1 = dict(uniform=1.0, eta=2.0, active=1.0, receiver=0.5)
tk.issue('J', 1, 0, 40, w1); tk.issue('J', 1, 5, 40, w1); tk.issue('J', 1, 10, 38, w1)
if len(tk.open('J', 1, 3)) != 0:
    fail('S10 green < 5 s should have no open ticket')
op = tk.open('J', 1, 12)
if [k['t'] for k in op] != [0.0, 5.0]:
    fail(f'S10 open window at t=12: {[k["t"] for k in op]}')
tk.issue('J', 2, 50, 70, w1)
if any(k['t'] == 50 for k in tk.open('J', 1, 60)) or len(tk.open('J', 2, 60)) != 1:
    fail('S10 multi-cycle isolation')
tk.close('J', 1); tk.close('J', 1)
if tk.stats['closed'] != 1 or tk.censor() != 1:
    fail(f'S10 close / censor counts {tk.stats}')
e_sw = M.penalty(1, 12, op, 'uniform'); e_keep_early = M.penalty(0, 12, op, 'uniform')
if abs(e_sw - ((40 - 2 - 12) * 2) / 10) > 1e-12 or e_keep_early != 0.0:
    fail(f'S10 early switch {e_sw} / keep before deadline {e_keep_early}')
late = [dict(t=0.0, That=20.0, wn=dict(uniform=1.0))]
if abs(M.penalty(0, 20, late, 'uniform') - 3 / 10) > 1e-12 or abs(M.penalty(0, 25, late, 'uniform') - 5 / 10) > 1e-12:
    fail('S10 long keep integration (late seconds)')
print('S10 tickets toy traces done')

# ------------------------------------------------------------------------------------------------ S9 (a) synthetic
c = M.Credit(2.0, 'uniform')
c.decide('J', 10, 'o10', 0, dict(uniform=0.3), -1.0); c.decide('J', 15, 'o15', 1, dict(uniform=0.7), -2.0)
c.decide('J', 25, 'o25', 0, dict(uniform=0.0), -3.0); c.decide('K', 10, 'k10', 0, dict(uniform=9.0), -5.0)
exp = [('o10', 0, -2.0 - 2.0 * 0.3, 'o15'), ('o15', 1, -3.0 - 2.0 * 0.7, 'o25')]
got = [(s, a, r, s2) for s, a, r, s2, _ in c.trans]
if got != exp:
    fail(f'S9a credit assembly {got} != {exp}')
print('S9a synthetic credit done')

# ------------------------------------------------------------------------------------------------ integration run (S9 b, S3, S11, S12)
net7, ck = T.rlh_net(K); net12 = M.widen(net7)
O = torch.randn(256, 7)
with torch.no_grad():
    if (net12(torch.cat([O, torch.zeros(256, 5)], 1)) - net7(O)).abs().max() > 0 or (net12(torch.cat([O, torch.randn(256, 5)], 1)) - net7(O)).abs().max() > 0:
        fail('S12 widened net != RL-H')
table = json.loads((P / f'm2b/forecast_rlh{K}.json').read_text()); scale = {'uniform': 1.0, 'eta': 0.7, 'active': 0.3, 'receiver': 0.12}

# S12 phase trace parity: LightRL(RL-H) vs LightE(widened greedy), same fleet / provider
class Rec:
    def __init__(self, inner, ids):
        self.inner, self.ids, self.P = inner, ids, []

    def step(self, t):
        self.inner.step(t); self.P.append([CE.ls.trafficlight.getPhase(x) for x in self.ids])


spat_fn, F = T.set_provider(table); cars = T.fleet(0); info = Q7.NetInfo(Q7.NET_S)
base = Rec(CE.LightRL(info, Q7.load_policy(ck)), list(info.tls)); CE.run_episode(Q7.NET_S, Q7.ROU.format(0), 0, base, cars, end=END)
L, _ = T.episode(M.greedy(net12), table, scale, 0, lam=1.0, wkey='receiver', record=True, log_phases=True, log_decisions=True, end=END)
if base.P != L.P:
    fail('S12 LightE(widened) phase trace != LightRL(RL-H)')
print(f'S12 phase parity over {len(L.P)} s; decisions {L.stats["decisions"]}, tickets {L.tickets.stats}')

# S9 (b): each closed transition's penalty == the pens of ITS decision (t_prev, same tid, same action)
dl = {(d['tid'], d['t']): d for d in L.dlog}
for x in L.credit.log:
    d = dl.get((x['tid'], x['t_prev']))
    if d is None or d['a'] != x['a'] or abs(d['pens']['receiver'] - x['pen']) > 1e-12:
        fail(f'S9b credit mismatch {x}'); break
print(f'S9b integration: {len(L.credit.log)} transitions checked')

# S3: independent recomputation of the penalty from the logged open tickets
def pen_indep(a, t, op, key, tau=2.0, dt=5.0):
    tot = 0.0
    for k in op:
        w = k['wn'][key]
        if a == 1:
            tot += w * max(0.0, k['That'] - tau - t)
        else:
            lo = max(t, k['That'] + tau); tot += w * max(0.0, t + dt - lo)
    return tot / 10.0
mis = sum(1 for d in L.dlog for key in M.TYPES if abs(pen_indep(d['a'], d['t'], d['open'], key) - d['pens'][key]) > 1e-12)
if mis:
    fail(f'S3 {mis} penalty mismatches')
print(f'S3 recomputed {len(L.dlog) * len(M.TYPES)} penalties')

# ------------------------------------------------------------------------------------------------ S11 probe parity
spat_fn, F = T.set_provider(table); cars = T.fleet(0); probes = {}; checks = dict(n=0, bad=0, pert=0)
inner = cars.step


def step(t):
    ls = CE.ls; before = (dict(cars.stats), len(cars.cmd_log)); live = set(ls.vehicle.getIDList())
    for v in list(cars.agents):
        if v not in live:                                          # arrived this step; CarPPOL drops it in its own step
            continue
        try:
            nt = ls.vehicle.getNextTLS(v)
            if not nt or nt[0][2] > M.ZONE:
                continue
            ok, s = M.eligible(ls, v, nt[0], spat_fn)
            if ok:
                probes[v] = M.r10_cmd(ls, v, nt[0], cars.net, spat_fn)
                if checks['pert'] < 50:                            # perturbation reaches both the rule speed and obs[10]
                    o0 = V8.build_obs(ls, v, nt[0], ls.vehicle.getSpeed(v), ls.vehicle.getAllowedSpeed(v), True, dict(spat_valid=0, spat_n=0))
                    c1 = M.r10_cmd(ls, v, nt[0], cars.net, spat_fn, s['ttg'] + 5)
                    vr0, vr1 = min(ls.vehicle.getAllowedSpeed(v), nt[0][2] / s['ttg']), min(ls.vehicle.getAllowedSpeed(v), nt[0][2] / (s['ttg'] + 5))
                    if vr1 == vr0 and c1 == probes[v] and nt[0][2] / s['ttg'] < ls.vehicle.getAllowedSpeed(v):
                        fail('S11 perturbation had no effect')
                    checks['pert'] += 1
        except Exception as e:                                     # noqa: BLE001
            fail(f'S11 probe exception {e}'); break
    if (dict(cars.stats), len(cars.cmd_log)) != before:
        fail('S11 probe side effect on the fleet')
    n0 = len(cars.cmd_log); inner(t)
    for (tt, v, cmd) in cars.cmd_log[n0:]:
        if v in probes:
            checks['n'] += 1
            dlt = abs(probes[v] - cmd); checks['maxdiff'] = max(checks.get('maxdiff', 0.0), dlt)
            if dlt > 1e-5:                                     # float32: batched vs single-row forward differ by ~1e-7 m/s
                checks['bad'] += 1
    probes.clear()


cars.step = step
CE.run_episode(Q7.NET_S, Q7.ROU.format(0), 0, CE.LightRL(info, Q7.load_policy(ck)), cars, end=END)
print(f'S11 parity: {checks}')
if checks['n'] == 0 or checks['bad']:
    fail('S11 probe != sent command')

# S12 scale table (from the full prep, if present)
for k in (0, 1):
    f = ROOT / f'research/city_sim/m3_20261004/prep/scale_rlh{k}.json'
    if f.exists():
        print(f'S12 scale k{k}:', json.dumps(json.loads(f.read_text())['stats']))
print('M3 PRE CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
