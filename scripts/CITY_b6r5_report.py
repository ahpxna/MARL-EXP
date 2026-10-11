#!/usr/bin/env python3
"""B6-R5 report (PROTOCOL_CITY_B6 §B6-R5, registered 09:39 04/10/2026, written before the run): replication of R5h on new DQN seeds
213 / 313 / 413 / 513 (t2..t5) on fresh traffic 410-419, under ACT, directory wave2_20261004/050r.
  R5-1 pooled (crossed fleet-seed x traffic): agent fuel superiority, agent TL NI +0.5, human TL NI +0.5
  R5-2 pooled S-2 vs the σ-family (σ 0, 0.1, 0.2, 0.3, 0.4 and always-SUMO = σ 0.5)
  R5-3 every new seed: teleports / run <= always-SUMO + 1, unfinished <= always-SUMO
Per-seed B6-1 verdicts, city TL, and the development seeds t0 / t1 are reported, not judged."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

D = R.W / '050r'; TS = list(range(410, 420)); NEW = [2, 3, 4, 5]; SIG = ['0.0', '0.1', '0.2', '0.3', '0.4']


def main(d=D, ts=TS):
    Rt = {}
    for f in Path(d).glob('*.json'):
        x = json.loads(f.read_text())
        if isinstance(x, dict) and 'rows' in x:
            for r in x['rows']:
                Rt[(f.stem, r['seed'])] = r
    F = lambda t: f'U-L-ACT-R5h_t{t}_ACT'; ref = {'0.5': 'OFF_ACT', **{s: f'S{s}_ACT' for s in SIG}}
    need = [(F(t), s) for t in NEW for s in ts] + [(v, s) for v in ref.values() for s in ts]
    miss = [k for k in need if k not in Rt]
    if miss:
        print('B6-R5 INCOMPLETE', len(miss), 'missing, e.g.', miss[:3]); return
    g = lambda t, s, k: Rt[(F(t), s)][k]; b = lambda nm, s, k: Rt[(nm, s)][k]
    dr = R.draws((len(NEW), len(ts))); out = [f'== B6-R5 replication of R5h (v3 / release / trip), new seeds t2..t5, fresh traffic {ts[0]}-{ts[-1]}, ACT ({d})']
    cube = lambda fn: np.array([[fn(t, s) for s in ts] for t in NEW])
    fu = lambda nm: R.crossed(cube(lambda t, s: 100 * (g(t, s, 'fuel_agent') / b(nm, s, 'fuel_agent') - 1)), dr)
    tl = lambda nm, k='timeloss_agent': R.crossed(cube(lambda t, s: g(t, s, k) - b(nm, s, k)), dr)
    Fu, Tl, Hu, Ci = fu('OFF_ACT'), tl('OFF_ACT'), tl('OFF_ACT', 'timeloss_human'), tl('OFF_ACT', 'timeloss')
    r1 = Fu[2] < 0 and Tl[2] < 0.5 and Hu[2] < 0.5
    out.append(f'R5-1 pooled vs always-SUMO: agent fuel % {R.fmt(*Fu)}; agent TL {R.fmt(*Tl)}; human TL {R.fmt(*Hu)}; city TL {R.fmt(*Ci)} -> {"SUPPORTED" if r1 else "NOT SUPPORTED"}')
    r2 = True; parts = []
    for sg, nm in sorted(ref.items()):
        a, c = fu(nm), tl(nm); ok = a[2] < 0 or c[2] < 0; r2 &= ok
        parts.append(f'σ{sg}: fuel {a[0]:+.2f}% (up {a[2]:+.2f}), TL {c[0]:+.2f} (up {c[2]:+.2f}) {"better" if ok else "NOT better"}')
    out.append('R5-2 pooled S-2: ' + '; '.join(parts) + f' -> {"SUPPORTED (beyond the σ-family)" if r2 else "NOT SUPPORTED"}')
    r3 = True; per = []
    for t in NEW + [0, 1]:
        if any((F(t), s) not in Rt for s in ts):
            per.append(f'  t{t}: missing'); continue
        tel = np.mean([g(t, s, 'teleports') for s in ts]); tel0 = np.mean([b('OFF_ACT', s, 'teleports') for s in ts])
        unf = np.mean([g(t, s, 'unfinished') for s in ts]); unf0 = np.mean([b('OFF_ACT', s, 'unfinished') for s in ts])
        d1 = R.draws((len(ts),)); one = lambda fn: R.crossed(np.array([fn(s) for s in ts]), d1)
        f1 = one(lambda s: 100 * (g(t, s, 'fuel_agent') / b('OFF_ACT', s, 'fuel_agent') - 1)); t1 = one(lambda s: g(t, s, 'timeloss_agent') - b('OFF_ACT', s, 'timeloss_agent'))
        h1 = one(lambda s: g(t, s, 'timeloss_human') - b('OFF_ACT', s, 'timeloss_human'))
        okc = tel <= tel0 + 1 and unf <= unf0
        if t in NEW:
            r3 &= okc
        p = f1[2] < 0 and t1[2] < 0.5 and h1[2] < 0.5 and okc
        per.append(f'  t{t}{" (development seed, descriptive)" if t in (0, 1) else ""}: fuel % {R.fmt(*f1)}; agent TL {R.fmt(*t1)}; human TL {R.fmt(*h1)}; '
                   f'teleports {tel:.1f} ({tel0:.1f}); unfinished {unf:.1f} ({unf0:.1f}) -> B6-1 {"PASS" if p else "FAIL"}')
    out.append(f'R5-3 teleports / unfinished on every new seed -> {"SUPPORTED" if r3 else "NOT SUPPORTED"}'); out += per
    out.append(f'VERDICT: R5h {"CONFIRMED as a beneficial learned fleet (fuel; beyond the σ-family)" if (r1 and r2 and r3) else "NOT CONFIRMED"}')
    txt = '\n'.join(out) + '\n'; (Path(d) / 'report_b6r5.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main()
