#!/usr/bin/env python3
"""Oracle event check (04/10/2026, C-70 item 2): in the M3 headroom replay (CITY_m3_headroom: replayed RL-H:k schedule, oracle SPaT), log
every oracle prediction at sampled seconds (t % 5 == 0) and an independent per-second phase observer; compare the predicted event times
(t + ttg = observed green onset of a serving phase; t + ttr = observed end of the serving phases) with the observed events of the run.
Usage: CITY_oracle_event_check.py K SEED  (fleet: R10 seed 213 + 100 K, as in the headroom pairing)"""
import json, sys
from collections import Counter
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_m3_headroom as H  # noqa: E402  (rebinds spat to the oracle)
import scripts.CITY_env as CE  # noqa: E402
import argparse  # noqa: E402
K, SEED = int(sys.argv[1]), int(sys.argv[2]); E4 = H.E4; PRED = []; PH = []
_or = H.spat_oracle


def spat_logged(tid, link):
    s = _or(tid, link); t = CE.ls.simulation.getTime()
    if s['valid'] and int(t) % 5 == 0:
        PRED.append((float(t), tid, int(link), s['ttg'], s['ttr']))
    return s


for m in (H.V8, H.ES, H.GL, H.LD, H.V11):
    m.spat = spat_logged
_run = E4.run_episode


def run_episode(net, rou, seed, light, cars, end=3600, tripinfo=None, extra=()):
    class Obs:
        def step(self, t):
            light.step(t); PH.append((float(t), {x: CE.ls.trafficlight.getPhase(x) for x in CE.ls.trafficlight.getIDList()}))
    return _run(net, rou, seed, Obs(), cars, end=end, tripinfo=tripinfo, extra=extra)


E4.run_episode = run_episode
P = 'research/city_sim/spat_pilot_20261004'
a = argparse.Namespace(light='FT', light_obs='raw', light_fallback='none', fleet=f'PL:{P}/fleets_v11/L11_s{213 + 100 * K}_fleet.pt', guard='none', record=None,
                       replay=None, replay_dir=f'{P}/m3_headroom/replay_rlh{K}', discharge=False, delay_trace=False, swap_at=None, swap_light=None, swap_fleet=None,
                       seeds=[SEED], smoke=False, tag='orc', out='/tmp')
a.replay = str(Path(a.replay_dir) / f'phases_s{SEED}.npz')
E4.run(a, SEED, 5400)
states = {}
for tid in PH[0][1]:
    pass
import libsumo  # noqa: E402,F401
ch = {}; prev = {}
for t, ph in PH:
    for tid, p in ph.items():
        if tid in prev and p != prev[tid]:
            ch.setdefault(tid, []).append((t, prev[tid], p))
        prev[tid] = p
import scripts.CITY_fleet_v8  # noqa: E402,F401
ST = H.REC['states']
eg, er = Counter(), Counter()
for t, tid, link, ttg, ttr in PRED:
    st = ST[tid]
    if ttg > 0:
        on = next((tt for tt, a_, b_ in ch.get(tid, []) if tt > t and st[b_][link] in 'Gg'), None)
        if on is not None:
            eg[round(t + ttg - on, 6)] += 1
    elif ttr < 999:
        off = next((tt for tt, a_, b_ in ch.get(tid, []) if tt > t and st[b_][link] not in 'Gg'), None)
        if off is not None:
            er[round(t + ttr - off, 6)] += 1
for nm, c in (('ttg (green onset)', eg), ('ttr (green end)', er)):
    n = sum(c.values()); print(f'{nm}: n {n}; predicted - observed -> ' + ', '.join(f'{v:+g}: {100 * m / max(1, n):.2f} %' for v, m in c.most_common(4)))
