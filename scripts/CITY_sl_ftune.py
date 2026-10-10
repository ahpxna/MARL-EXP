#!/usr/bin/env python3
"""F1 Amendment A2 (PROTOCOL_CITY_F1_SALTLAKE_20261008): simulation-tuned fixed-time plan per site.  Start = Webster durations
(programs.json); coordinate descent over (signal, green): +-5 s within [5, 60] s, accept if mean city time loss over 8 TRAIN days
(every 10th TRAIN day from the first; all SUMO cars) improves by > 0.1 s/veh; at most 4 passes.  Candidate programs are loaded as an
additional tlLogic (programID ft_try, the last loaded program is active) on the Webster net.  Then the Webster net is kept as
saltlake_<site>_webster.net.xml and saltlake_<site>.net.xml is rebuilt with the tuned durations (KSL-3 rechecked).
Usage: PYTHONHASHSEED=0 CITY_sl_ftune.py <site>   (W_SMOKE=1: 2 days, 1 pass)"""
import json, os, shutil, sys, tempfile
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_sl_build as B  # noqa: E402
site = sys.argv[1]; SM = os.environ.get('W_SMOKE') == '1'; TMP = Path(tempfile.mkdtemp(prefix='slft_'))
NETW = B.NET / f'saltlake_{site}_webster.net.xml'
if not NETW.exists():
    shutil.copy(B.NET / f'saltlake_{site}.net.xml', NETW)
P = json.loads((B.DEM / site / 'programs.json').read_text()); dur = {tl: list(v['webster']['g']) for tl, v in P.items()}
D = [d.timetuple().tm_yday for d in B.days(site, 'train')][::10][:2 if SM else 8]; cache = {}


def score(du):
    key = json.dumps(du, sort_keys=True)
    if key in cache:
        return cache[key]
    f = B.programs(site, du, write_tll=str(TMP / 'try.tll.xml')); f.write_text(f.read_text().replace('programID="f1"', 'programID="ft_try"'))
    tl = []
    for s in D:
        ti = str(TMP / 'ti.xml'); CE.run_episode(str(NETW), str(B.DEM / site / f'rou_s{s}.xml'), s, None, None, end=3600, tripinfo=ti, extra=('-a', str(f)))
        R = CE.read_tripinfo(ti); tl.append(float(np.mean([r['timeloss'] for r in R])))
    cache[key] = float(np.mean(tl)); return cache[key]


hist = [dict(pass_=0, dur=json.loads(json.dumps(dur)), tl=score(dur))]; print('start', hist[-1], flush=True); best = hist[-1]['tl']
for p in range(1 if SM else 4):
    improved = False
    for tl in sorted(dur):
        for i in range(4):
            for step in (5, -5):
                g = dur[tl][i] + step
                if not 5 <= g <= 60:
                    continue
                cand = json.loads(json.dumps(dur)); cand[tl][i] = g; sc = score(cand)
                if sc < best - 0.1:
                    dur, best, improved = cand, sc, True; print(f'pass {p} {tl} green {i} -> {g} s: {sc:.2f}', flush=True)
                    break
    hist.append(dict(pass_=p + 1, dur=json.loads(json.dumps(dur)), tl=best))
    if not improved:
        break
(B.DEM / site / ('ftune_smoke.json' if SM else 'ftune.json')).write_text(json.dumps(dict(days=D, hist=hist, evaluations=len(cache), final=dur, final_tl=best), indent=1))
print(f'{site}: Webster {hist[0]["tl"]:.2f} -> tuned {best:.2f} s/veh city TL on TRAIN days {D}; durations {dur}; {len(cache)} evaluations')
if not SM:
    ok = B.programs(site, dur)
    sys.exit(0 if ok else 1)
