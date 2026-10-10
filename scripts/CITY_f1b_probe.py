#!/usr/bin/env python3
"""F1-B KB0-3 online probe (exit 1 on failure): one live grid4 episode (RL-H:<k> through the F1-A1 light_spec patch, all SUMO cars), and
every second, for every light and every link, the OLD provider (CITY_spat_forecast_c.make_spat_c) and the NEW one (c2) on the same table and q.
They must be identical except in the yellow -> green-after-next branch (light in a non-green phase, link served only by greens other than the
next one), where new.ttg - old.ttg = +1 exactly.  Usage: CITY_f1b_probe.py <k> <table> <q> <seed> <out txt>"""
import json, sys
from collections import Counter
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_f1a1_run  # noqa: E402,F401  (RL-H:4..8 light_spec patch)
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_spat_forecast_c as FCC  # noqa: E402
import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402
if __name__ == '__main__':
    k, tb, q, seed, out_f = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    table = json.loads(Path(tb).read_text()); old, Fo = FCC.make_spat_c(table, q); new, Fn = C2.make_spat_c2(table, q)
    _n, ck, _m = X2.light_spec(f'RL-H:{k}'); info = Q7.NetInfo(Q7.NET_S); light = CE.LightRL(info, Q7.load_policy(ck)); C = Counter(); bad = []; st = {}

    class Probe:
        def step(self, t):
            light.step(t); ls = CE.ls
            for tid in info.tls:
                if tid not in st:
                    st[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
                gs = Fn.G[tid]; ph = ls.trafficlight.getPhase(tid); nxt_g = None
                if ph not in gs:
                    j = ph
                    while True:
                        j = (j + 1) % len(st[tid])
                        if j in gs:
                            nxt_g = j; break
                for link in range(len(st[tid][0])):
                    a, b = old(tid, link), new(tid, link); serve = {g for g in gs if st[tid][g][link] in 'Gg'}
                    branch = (ph not in gs and serve and len(serve) < len(gs) and nxt_g not in serve)
                    same = a['valid'] == b['valid'] and abs(a['ttg'] - b['ttg']) < 1e-9 and abs(a['ttr'] - b['ttr']) < 1e-9
                    if branch:
                        good = a['valid'] and b['valid'] and abs((b['ttg'] - a['ttg']) - 1.0) < 1e-9 and abs(a['ttr'] - b['ttr']) < 1e-9; C['c84_branch_' + ('plus1' if good else 'OTHER')] += 1
                        if not good and len(bad) < 5:
                            bad.append((t, tid, link, a, b))
                    else:
                        C['other_' + ('identical' if same else 'DIFFERENT')] += 1
                        if not same and len(bad) < 5:
                            bad.append((t, tid, link, a, b))
    m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, Probe(), None, end=3600)
    ok = C['other_DIFFERENT'] == 0 and C['c84_branch_OTHER'] == 0 and C['c84_branch_plus1'] > 0 and C['other_identical'] > 0
    t = f'== F1-B KB0-3 online probe: RL-H:{k}, table {tb}, q {q}, seed {seed}\n  counts {dict(C)}\n  first mismatches {bad}\nKB0-3: {"PASS" if ok else "FAIL"}\n'
    Path(out_f).write_text(t); print(t); sys.exit(0 if ok else 1)
