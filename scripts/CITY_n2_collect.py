#!/usr/bin/env python3
"""N2 data collection (PROTOCOL_CITY_N2_STATE_FORECAST_20261005): CITY_eval_f1b (UNCHANGED, imported; its --spat-arm decides the fleet's SPaT,
here fc2:<q>:<table>, i.e. the deployed condition) plus a per-second FEATURE logger (a subclass of CITY_eval4.Logger, installed by name):
for every light (sorted ids) the phase, getSpentDuration, halting and vehicle counts on each green's served lanes, and the number of
fleet SPaT queries at that light in that second.  Writes <featlog>/feat_s<seed>.npz (ids, phases, spent, H [T,L,2], V [T,L,2], Q [T,L]);
phases / spent use the same layout as the --record traces, so CITY_spat_forecast.fit works on them.  Usage as CITY_eval_f1b.py + --featlog DIR."""
import argparse, sys
from collections import Counter
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--featlog', required=True); A0, REST = pre.parse_known_args()
sys.argv = [sys.argv[0]] + REST
import scripts.CITY_eval_f1b as EF  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
E4 = EF.E4; QC = Counter(); CUR = {}
_base = EF.BASE


def counted(tid, link):
    QC[tid] += 1; return _base(tid, link)


EF.BASE = counted


class FeatLogger(E4.Logger):
    def __init__(self, *a, **k):
        super().__init__(*a, **k); self.ids_f = sorted(self.info.tls); self.P, self.S, self.H, self.V, self.Q = [], [], [], [], []; CUR['log'] = self

    def step(self, t):
        super().step(t); ls = CE.ls; p, s, h, v, q = [], [], [], [], []
        for tid in self.ids_f:
            d = self.info.tls[tid]; p.append(ls.trafficlight.getPhase(tid)); s.append(ls.trafficlight.getSpentDuration(tid))
            h.append([sum(ls.lane.getLastStepHaltingNumber(l) for l in sv) for sv in d['serve'][:2]])
            v.append([sum(ls.lane.getLastStepVehicleNumber(l) for l in sv) for sv in d['serve'][:2]]); q.append(QC.pop(tid, 0))
        self.P.append(p); self.S.append(s); self.H.append(h); self.V.append(v); self.Q.append(q)


E4.Logger = FeatLogger
_run = E4.run


def run(a, seed, end):
    QC.clear(); out = _run(a, seed, end); L = CUR['log']; Path(A0.featlog).mkdir(parents=True, exist_ok=True)
    np.savez_compressed(Path(A0.featlog) / f'feat_s{seed}.npz', ids=np.array(L.ids_f), phases=np.array(L.P, np.int16), spent=np.array(L.S, np.float64),
                        H=np.array(L.H, np.int16), V=np.array(L.V, np.int16), Q=np.array(L.Q, np.int32))
    return out


E4.run = run
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[0]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    E4.main(p.parse_args(EF.REST))
