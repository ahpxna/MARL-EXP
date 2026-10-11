#!/usr/bin/env python3
"""M3 HEADROOM DIAGNOSTIC (04/10/2026; an ORACLE, not deployable, not an M3 arm): how much of its benefit can a frozen fleet recover under the
learned light's timing if it knew the light's FUTURE switches exactly?  The light is an open-loop REPLAY (CITY_eval4.Replay) of a recorded
RL-H:k run with σ* cars (m2b/traces, SELECT 100-104); the fleet's spat() reads the recorded future phases of that replay:
    ttg = first future index whose phase serves the link - now;  ttr = first future index whose phase does not serve it - now
(convention of CITY_spat_feature: P[i] is the phase observed at time i + 1).  The bound is for information-only methods (forecast or
message shaping) under THIS timing; the replayed light does not react to the fleet's traffic.
Usage: CITY_m3_headroom.py <CITY_eval4 arguments with --replay-dir and --fleet>  (σ* rows: CITY_eval4_sigma.py with the same --replay-dir)"""
import sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_v11 as _E  # noqa: E402,F401
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_glosa_lane_d as LD  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
import hashlib  # noqa: E402

E4.SRC = f"{E4.SRC}+m3oracle:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
REC = {}; N = dict(total=0, valid=0)
_init = E4.Replay.__init__


def init(self, rec, info):
    _init(self, rec, info); REC.update(P=np.asarray(rec['phases']), ids=[str(x) for x in rec['ids']], nxt={}, states={})


E4.Replay.__init__ = init


def _next(j, serve, want):
    key = (j, serve, want)
    if key not in REC['nxt']:
        col = REC['P'][:, j]; out = np.full(len(col), -1); last = -1
        for i in range(len(col) - 1, -1, -1):
            if (int(col[i]) in serve) == want:
                last = i
            out[i] = last
        REC['nxt'][key] = out
    return REC['nxt'][key]


def spat_oracle(tid, link):
    N['total'] += 1; ls = CE.ls; t = int(round(ls.simulation.getTime())); j = REC['ids'].index(tid); k0 = t - 1; P = REC['P']
    if tid not in REC['states']:
        REC['states'][tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
    serve = frozenset(p for p, st in enumerate(REC['states'][tid]) if st[link] in 'Gg')
    if not serve or k0 < 0 or k0 + 1 >= len(P):
        return dict(ttg=0.0, ttr=0.0, valid=False, source='oracle-unavailable')
    if int(P[k0, j]) in serve:
        i = _next(j, serve, False)[k0 + 1]; N['valid'] += 1
        return dict(ttg=0.0, ttr=float(i - k0) if i >= 0 else 999.0, valid=True, source='oracle')
    i = _next(j, serve, True)[k0 + 1]
    if i < 0:
        return dict(ttg=0.0, ttr=0.0, valid=False, source='oracle-unavailable')
    N['valid'] += 1
    return dict(ttg=float(i - k0), ttr=0.0, valid=True, source='oracle')


for m in (V8, ES, GL, LD, V11):
    m.spat = spat_oracle

if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    E4.main(p.parse_args()); print('oracle spat calls', N, flush=True)
