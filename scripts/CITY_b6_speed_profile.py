#!/usr/bin/env python3
"""B6-D1 (PROTOCOL_CITY_B6_BENEFICIAL_FLEET_20261004.md): share of agent zone-seconds halted / crawling / moving under ACT, per fleet
(always-SUMO via guard `always` = SUMO's default driver model on the same agent vehicles).  Descriptive; PYTHONHASHSEED=0."""
import json, os, sys
from pathlib import Path
from types import SimpleNamespace
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_eval3 as E  # noqa: E402

if os.environ.get('PYTHONHASHSEED') != '0':
    sys.exit('run with PYTHONHASHSEED=0')
out = {}
for F, g in [('L-ACT:0', 'always'), ('L-ACT:0', 'none'), ('U:L-ACT-v2_t0', 'none'), ('U:L-ACT-v2_t1', 'none'), ('U:L-ACT-v3_t0', 'none'), ('U:L-ACT-v3_t1', 'none')]:
    cnt = np.zeros(3); stops = 0
    for seed in (100, 101):
        cars, _ = E.load_fleet(F, seed, g); prev = {}
        class Log:
            def step(self, t):
                global stops
                for v in list(cars.agents):
                    try:
                        nt = CE.ls.vehicle.getNextTLS(v)
                        if not nt or nt[0][2] > CE.ZONE:
                            continue
                        sp = CE.ls.vehicle.getSpeed(v)
                    except Exception:
                        continue
                    cnt[0 if sp < 0.1 else (1 if sp < 2.0 else 2)] += 1
        class Multi:
            def step(self, t):
                cars.step(t); Log().step(t)
        CE.run_episode(E.Q7.NET_A, E.Q7.ROU.format(seed), seed, Multi(), None, end=5400)
    sh = cnt / cnt.sum(); out[f'{F}/{g}'] = dict(halt=sh[0], crawl=sh[1], move=sh[2], zone_seconds=float(cnt.sum()))
    print(f'{F:16s} {g:7s} halt {sh[0]:.3f} crawl {sh[1]:.3f} move {sh[2]:.3f} zone-seconds {cnt.sum():.0f}', flush=True)
Path('research/city_sim/wave2_20261004/b6_d1_speed_profile.json').write_text(json.dumps(out, indent=1))
