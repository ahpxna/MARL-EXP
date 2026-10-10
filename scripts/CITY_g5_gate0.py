#!/usr/bin/env python3
"""G5 Gate 0 (03/10/2026 11:0x EDT; design check before PROTOCOL_CITY_G5 — no training, no hypothesis): do actuated lights with
max green M in {40, 50, 60, 80} actually produce different green durations under the human traffic the fleets train on?
Human traffic only (routes research/city_sim/demand/grid4/rou_s{0..7}.xml, 3600 s).  Per light and run: the duration of every
completed green phase (state has G/g and no y).  Pass (from the G5 design): ACT40's max <= 40; ACT80's realised max >= 70 s and
>= 5 % of its green-seconds in phases longer than 50 s."""
import json, sys, time
from pathlib import Path
import numpy as np
import libsumo as ls
import sumolib
ROOT = Path(__file__).resolve().parents[1]
NETS = {50: 'research/city_sim/net/grid4_actuated.net.xml', 40: 'research/city_sim/net/grid4_actuated_max40.net.xml',
        60: 'research/city_sim/net/grid4_actuated_max60.net.xml', 80: 'research/city_sim/net/grid4_actuated_max80.net.xml'}
ROU = 'research/city_sim/demand/grid4/rou_s{}.xml'


def run(net, seed, end=3600):
    ls.start([sumolib.checkBinary('sumo'), '-n', str(ROOT / net), '-r', str(ROOT / ROU.format(seed)), '--seed', str(seed),
              '--no-step-log', '--no-warnings', '--time-to-teleport', '300', '--step-length', '1'])
    tls = ls.trafficlight.getIDList(); cur = {t: (None, 0.0) for t in tls}; greens = []
    while ls.simulation.getTime() < end:
        ls.simulationStep(); now = ls.simulation.getTime()
        for t in tls:
            st = ls.trafficlight.getRedYellowGreenState(t); g = ('G' in st or 'g' in st) and 'y' not in st
            ph = ls.trafficlight.getPhase(t); prev, since = cur[t]
            if ph != prev:
                if prev is not None and cur[t + '#g'] if (t + '#g') in cur else False:
                    greens.append(now - since)
                cur[t] = (ph, now); cur[t + '#g'] = g
    ls.close()
    return greens


out = {}; t0 = time.perf_counter()
for M, net in sorted(NETS.items()):
    g = []
    for s in range(8):
        g += run(net, s)
    g = np.array(g); share50 = float(g[g > 50].sum() / g.sum()) if g.size else 0.0
    out[M] = dict(n=int(g.size), max=float(g.max()), p50=float(np.median(g)), p95=float(np.percentile(g, 95)),
                  share_greensec_over50=share50, share_phases_at_max=float(np.mean(g >= M - 1)))
    print(f'[{time.perf_counter() - t0:.0f}s] M={M}: {out[M]}', flush=True)
ok = out[40]['max'] <= 40.5 and out[80]['max'] >= 70 and out[80]['share_greensec_over50'] >= 0.05
out['gate0'] = 'PASS' if ok else 'FAIL'
(ROOT / 'research/city_sim/g5_gate0_20261003/gate0.json').write_text(json.dumps(out, indent=1))
print('GATE 0', out['gate0'], flush=True)
