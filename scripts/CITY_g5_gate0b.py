#!/usr/bin/env python3
"""G5 Gate 0b (03/10/2026 11:1x EDT; design check, no training, no hypothesis).  Gate 0 (human traffic only) showed actuated
greens gap out at <= 19 s on every max-green net — the 50 s support of the Q7 / Q7b fleets arises only in CLOSED LOOP with the
learned fleet present (cars' detector occupancy extends the phases).  Here the EXISTING fleet policy L-ACT_t1 (trained against
ACT50) drives at the Q7 penetration on each ACT_M net (M in 40, 50, 60, 80), training seeds 0-7, 3600 s; recorded: the
fleet's decision-time tau (the light's spent duration) per decision, as CarRL.oos_log does.  Pass: tau reaches >= M - 2 on every
net and the share of decisions with tau > 50 on ACT80 is >= 2 %."""
import json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_env import CarRL, run_episode  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
NETS = {50: Q7.NET_A, 40: 'research/city_sim/net/grid4_actuated_max40.net.xml', 60: 'research/city_sim/net/grid4_actuated_max60.net.xml',
        80: 'research/city_sim/net/grid4_actuated_max80.net.xml'}
pol = Q7.load_policy('research/city_sim/q7b_contract_20261002/L-ACT_t1.pt'); out = {}
for M, net in sorted(NETS.items()):
    taus = []
    for s in Q7.TRAIN_SEEDS:
        cars = CarRL(pol, Q7.RHO, s, record=True); run_episode(str(ROOT / net) if not str(net).startswith('/') else net, Q7.ROU.format(s), s, None, cars, end=3600)
        taus += [t for _, t in cars.oos_log]
    t = np.array(taus)
    out[M] = dict(n=int(t.size), max=float(t.max()), p95=float(np.percentile(t, 95)), p99=float(np.percentile(t, 99)),
                  share_over_50=float(np.mean(t > 50)), share_over_40=float(np.mean(t > 40)))
    print(f'M={M}: {out[M]}', flush=True)
ok = all(out[M]['max'] >= M - 2 for M in NETS) and out[80]['share_over_50'] >= 0.02
out['gate0b'] = 'PASS' if ok else 'FAIL'
(ROOT / 'research/city_sim/g5_gate0_20261003/gate0b.json').write_text(json.dumps(out, indent=1)); print('GATE 0b', out['gate0b'])
