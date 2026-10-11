#!/usr/bin/env python3
"""Fleet-benefit audit (04/10/2026 wake 3; post hoc, no new simulation; prompted by L4's missing comparator).  For every h0-panel run with a
learned fleet (research/city_sim/xplay_h0_20261004, default sensing, tripinfo kept), compare the AGENT vehicles' time loss and fuel with the
SAME vehicles (CarRL.is_agent is a function of seed and vehicle id only) in the all-human run of the same light and seed: the
"fleet off" comparator.  Also the city time loss.  A fleet with no benefit over human driving under its own training light is not an
upgrade of anything; protecting it is a mechanism study, not a deployment result."""
import json, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_env import read_tripinfo, CarRL  # noqa: E402

D = Path('research/city_sim/xplay_h0_20261004/tripinfo'); S = [100, 101, 102, 103, 104]


def agg(path, seed):
    rows = read_tripinfo(str(path)); car = CarRL(None, 0.5, seed); ag = [r for r in rows if car.is_agent(r['id'])]
    return np.mean([r['timeloss'] for r in ag]), np.mean([r['fuel'] for r in ag]), np.mean([r['timeloss'] for r in rows])


def main():
    out = ['== Fleet-benefit audit: agent vehicles driven by the fleet vs the same vehicles driven by SUMO\'s human model (fleet off)']
    res = defaultdict(dict)
    lights = ['ACT'] + [f'{f}{t}' for f in ('RL-H', 'RL-C50', 'RL-J') for t in range(4)]
    for L in lights:
        off = [agg(D / f'{L}_human_default_s{s}.xml', s) for s in S]
        for F in ['L-ACT0', 'L-ACT1', 'L-ACT2', 'L-ACT3', 'L-RLH0']:
            on = [agg(D / f'{L}_{F}_default_s{s}.xml', s) for s in S]
            dT = np.mean([a[0] - b[0] for a, b in zip(on, off)]); dF = np.mean([a[1] / b[1] - 1 for a, b in zip(on, off)]); dC = np.mean([a[2] - b[2] for a, b in zip(on, off)])
            res[L][F] = (dT, dF, dC)
    out.append('cells: agent TL change (s/veh) / agent fuel change (%) / city TL change, fleet ON minus OFF, mean over seeds 100-104')
    for L in lights:
        out.append(f'  {L:8s} ' + ' | '.join(f'{F} {v[0]:+6.2f} {100 * v[1]:+5.1f}% {v[2]:+6.2f}' for F, v in res[L].items()))
    tr = [res['ACT'][f'L-ACT{t}'] for t in range(4)] + [res['RL-H0']['L-RLH0']]
    out.append(f'Under each fleet\'s OWN training light (L-ACT_t x ACT, L-RLH_0 x RL-H_0): agent TL change {[round(x[0], 2) for x in tr]}, fuel {[round(100 * x[1], 1) for x in tr]} % '
               f'-> fleets beating human driving on time: {sum(x[0] < 0 for x in tr)}/5, on fuel: {sum(x[1] < 0 for x in tr)}/5')
    txt = '\n'.join(out) + '\n'; Path('research/city_sim/fleet_benefit_audit_20261004.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main()
