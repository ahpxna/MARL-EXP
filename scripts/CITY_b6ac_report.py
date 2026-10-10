#!/usr/bin/env python3
"""B6-AC report (PROTOCOL_CITY_B6 §B6-AC, registered 04/10/2026 wake 9 before the run): ACC fleet (route variant) under frozen lights.
Usage: CITY_b6ac_report.py DIR SEED... ; rows tagged ctrl_<L>, acc_<L>, OFF_<L> with L in ACT, RL-H-0..3.  Crossed light-seed x traffic."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

L = [f'RL-H-{i}' for i in range(4)]; KEYS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent')


def main(d, seeds):
    Rt = {}
    for f in Path(d).glob('*.json'):
        x = json.loads(f.read_text())
        if isinstance(x, dict) and 'rows' in x:
            for r in x['rows']:
                Rt[(f.stem, r['seed'])] = r
    need = [(f'{a}_{l}', s) for a in ('ctrl', 'acc', 'OFF') for l in ['ACT'] + L for s in seeds]
    miss = [k for k in need if k not in Rt]
    out = [f'== B6-AC ACC fleet (SUMO carFollowModel ACC on the agent cars) under frozen lights, traffic {seeds[0]}-{seeds[-1]} ({d})']
    if miss:
        out.append(f'B6-AC INCOMPLETE ({len(miss)} missing)'); print('\n'.join(out)); return
    v = lambda a, l, s, k: Rt[(f'{a}_{l}', s)][k]
    ok0 = all(abs(v('ctrl', l, s, k) - v('OFF', l, s, k)) < 1e-9 for l in ['ACT'] + L for s in seeds for k in KEYS)
    out.append(f'AC-0 ctrl == always-SUMO on every light and seed: {"PASS" if ok0 else "FAIL (report void)"}')
    if not ok0:
        print('\n'.join(out)); return
    d1 = R.draws((len(seeds),)); dr = R.draws((4, len(seeds)))
    pct = lambda a, b: 100 * (a / b - 1)
    for lab, lights in (('ACT', ['ACT']), ('RL-H', L)):
        T = lambda k: (np.array([v('acc', 'ACT', s, k) - v('OFF', 'ACT', s, k) for s in seeds]) if lab == 'ACT' else
                       np.array([[v('acc', l, s, k) - v('OFF', l, s, k) for s in seeds] for l in L]))
        Fp = (np.array([pct(v('acc', 'ACT', s, 'fuel_agent'), v('OFF', 'ACT', s, 'fuel_agent')) for s in seeds]) if lab == 'ACT' else
              np.array([[pct(v('acc', l, s, 'fuel_agent'), v('OFF', l, s, 'fuel_agent')) for s in seeds] for l in L]))
        D = d1 if lab == 'ACT' else dr
        tel = np.mean([v('acc', l, s, 'teleports') for l in lights for s in seeds]); unf = np.mean([v('acc', l, s, 'unfinished') for l in lights for s in seeds])
        out.append(f'AC-1 ACC - always-SUMO under {lab}: agent TL {R.fmt(*R.crossed(T("timeloss_agent"), D))}; human TL {R.fmt(*R.crossed(T("timeloss_human"), D))}; '
                   f'city TL {R.fmt(*R.crossed(T("timeloss"), D))}; agent fuel % {R.fmt(*R.crossed(Fp, D))}; teleports / run {tel:.2f}; unfinished {unf:.2f}')
    for k in KEYS:
        if k == 'fuel_agent':
            c = np.array([[pct(v('acc', l, s, k), v('OFF', l, s, k)) - pct(v('acc', 'ACT', s, k), v('OFF', 'ACT', s, k)) for s in seeds] for l in L])
        else:
            c = np.array([[(v('acc', l, s, k) - v('OFF', l, s, k)) - (v('acc', 'ACT', s, k) - v('OFF', 'ACT', s, k)) for s in seeds] for l in L])
        p, ci, _ = R.crossed(c, dr)
        ver = (f' -> {"COMPATIBLE (inside ±0.5)" if ci[0] > -0.5 and ci[1] < 0.5 else "NOT inside ±0.5"}' if k == 'timeloss' else '')
        out.append(f'AC-2 interaction [{k}{" %" if k == "fuel_agent" else ""}] (ACC - base)|RL-H - (ACC - base)|ACT: {R.fmt(p, ci)}{ver}')
    g = lambda a: np.mean([[v(a, l, s, 'timeloss') - v(a, 'ACT', s, 'timeloss') for s in seeds] for l in L])
    out.append(f'AC-3 light gain RL-H - ACT (city TL): SUMO cars {g("OFF"):+.2f}; ACC fleet {g("acc"):+.2f}')
    txt = '\n'.join(out) + '\n'; (Path(d) / 'report_b6ac.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main(sys.argv[1], [int(x) for x in sys.argv[2:]])
