#!/usr/bin/env python3
"""W21-E (PROTOCOL_CITY_WAVE21_20261015): copy of scripts/CITY_w20_twin_calib.py for the W17 field-matched world.  Workers are
spawned and do not inherit a wrapper, so each worker imports scripts.CITY_w17_world (its module-level patches route every grid4 SUMO start
through the W17 IDM copies) and asserts that CE.run_episode is the W17 one; KW17-0 then prints in every worker.  Run it directly (no
wrapper needed): CITY_w21_twin_calib_w17.py <out json> <end s> <seed> ...
Original docstring: W20 site calibration of the TSI-G human twin (PROTOCOL_CITY_WAVE20_20261009): its one site parameter CREEP (seconds a twin rolls at the
queue tail before halting) is chosen so that, on all-human pre-deployment logs, twins reproduce the human halting time.  Every vehicle is
twinned (rho 1) in a shadow tracker, with the pure twin model (a real halt does not force the twin, FORCE_REAL False); the signals run their fixed-time program (no controller is affected).  Grid CREEP in {0, 1, ..., 10} s;
criterion |sum twin halted vehicle-seconds / sum real halted vehicle-seconds - 1| (ties: higher per-vehicle-second agreement).  Also reports
agreement and the per-lane halting-count error at 5-s ticks on lanes with any halting.
Usage: CITY_w20_run.py scripts/CITY_w20_twin_calib.py <out json> <end s> <seed> [<seed> ...]"""
import json, sys
from multiprocessing import Pool
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
GRID = list(range(11))


def one(args):
    c, seed, end = args
    import scripts.CITY_w17_world  # noqa: F401  (W17 world patches in this spawned worker)
    import scripts.CITY_env as CE, scripts.CITY_q7_cross_version as Q7, scripts.CITY_w20_bench as B  # noqa: E401
    assert CE.run_episode.__module__ == 'scripts.CITY_w17_world', 'W17 world not in force in the worker'
    B.CREEP = float(c); B.FORCE_REAL = False; B.TRACK.reset(); B.TRACK.seed = seed; B.TRACK.rho = 1.0; B.TRACK.bis = True; B.TRACK.info = None
    info = CE.NetInfo(Q7.NET_S); st = dict(tw=0, re=0, ag=0, n=0); err = []

    class P:
        def step(self, t):
            B.TRACK.update(info, t)
            for r in B.TRACK.veh.values():
                th, rh = r['tw']['s'] == 'halt', r['v'] < 0.1; st['tw'] += th; st['re'] += rh; st['ag'] += th == rh; st['n'] += 1
            if int(t) % 5 == 0:
                for l, recs in B.TRACK.bylane.items():
                    a, b = sum(r['tw']['s'] == 'halt' for r in recs), sum(r['v'] < 0.1 for r in recs)
                    if a or b:
                        err.append(a - b)
    CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, P(), None, end=end)
    return c, seed, st, err


if __name__ == '__main__':
    out, end, seeds = sys.argv[1], int(sys.argv[2]), [int(x) for x in sys.argv[3:]]
    with Pool(int(__import__('os').environ.get('W20_CAL_P', 4))) as p:
        R = p.map(one, [(c, s, end) for c in GRID for s in seeds])
    res = {}
    for c in GRID:
        rows = [x for x in R if x[0] == c]; tw = sum(x[2]['tw'] for x in rows); re = sum(x[2]['re'] for x in rows)
        ag = sum(x[2]['ag'] for x in rows) / sum(x[2]['n'] for x in rows); e = np.concatenate([np.array(x[3], float) for x in rows])
        res[c] = dict(ratio=tw / re, agree=ag, err_mean=float(e.mean()), err_mae=float(np.abs(e).mean()), n_lane_ticks=int(len(e)))
        print(f'CREEP {c:2d} s: twin / real halted vehicle-seconds {tw / re:.3f}; agreement {ag:.4f}; lane-tick error {e.mean():+.3f}, MAE {np.abs(e).mean():.3f} (n {len(e)})', flush=True)
    best = min(GRID, key=lambda c: (abs(res[c]['ratio'] - 1), -res[c]['agree']))
    Path(out).write_text(json.dumps(dict(creep=best, grid=res, seeds=seeds, end=end), indent=1)); print('chosen CREEP', best, flush=True)
