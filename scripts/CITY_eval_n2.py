#!/usr/bin/env python3
"""N2 grid4 evaluator (PROTOCOL_CITY_N2_STATE_FORECAST_20261005): CITY_eval_f1 (UNCHANGED, imported with --spat-arm none) with the fleet
SPaT replaced by the N2 provider (--n2 <q>:<model.pt>).  A Logger subclass feeds the provider's run-length Tracker every second; with
--featlog DIR it also writes the CITY_n2_collect feature file and the provider's first 20 000 computed feature rows (KN2-1 parity).
Usage: CITY_eval_n2.py --n2 0.1:<model> [--featlog DIR] --light RL-H:k --fleet PL:... --seeds ... --tag T --out D"""
import argparse, hashlib, json, sys
from collections import Counter
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--n2', required=True); pre.add_argument('--featlog'); A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none'] + REST
import scripts.CITY_eval_f1 as EF  # noqa: E402
sys.argv = _argv
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_spat_forecast_n2 as N2  # noqa: E402
E4 = EF.E4; sha = lambda b: hashlib.sha256(b).hexdigest(); q, mp = A0.n2.split(':', 1); q = float(q)
TR = N2.Tracker(); INFO = E4.NetInfo(E4.Q7.NET_S); DBG = [] if A0.featlog else None
SPAT = N2.make_spat_n2(mp, q, INFO, TR, DBG); EF.BASE = SPAT; EF.META.update(n2=A0.n2, model_sha256=sha(Path(mp).read_bytes()))
E4.SRC = f"{E4.SRC}+n2:{sha(Path(__file__).read_bytes())}"; QC = Counter(); CUR = {}


def counted(tid, link):
    QC[tid] += 1; return SPAT(tid, link)


EF.BASE = counted


class TLogger(E4.Logger):
    def __init__(self, *a, **k):
        super().__init__(*a, **k); self.ids_f = sorted(self.info.tls); self.P, self.S, self.H, self.V, self.Q = [], [], [], [], []; CUR['log'] = self; TR.__init__()

    def step(self, t):
        super().step(t); TR.step(self.ids_f)
        if A0.featlog:
            ls = CE.ls; p, s, h, v, qq = [], [], [], [], []
            for tid in self.ids_f:
                d = self.info.tls[tid]; p.append(ls.trafficlight.getPhase(tid)); s.append(ls.trafficlight.getSpentDuration(tid))
                h.append([sum(ls.lane.getLastStepHaltingNumber(l) for l in sv) for sv in d['serve'][:2]]); v.append([sum(ls.lane.getLastStepVehicleNumber(l) for l in sv) for sv in d['serve'][:2]]); qq.append(QC.pop(tid, 0))
            self.P.append(p); self.S.append(s); self.H.append(h); self.V.append(v); self.Q.append(qq)


E4.Logger = TLogger
_run = E4.run


def run(a, seed, end):
    DBG and DBG.clear(); out = _run(a, seed, end)
    if A0.featlog:
        L = CUR['log']; Path(A0.featlog).mkdir(parents=True, exist_ok=True)
        np.savez_compressed(Path(A0.featlog) / f'feat_s{seed}.npz', ids=np.array(L.ids_f), phases=np.array(L.P, np.int16), spent=np.array(L.S, np.float64),
                            H=np.array(L.H, np.int16), V=np.array(L.V, np.int16), Q=np.array(L.Q, np.int32))
        json.dump(DBG, open(Path(A0.featlog) / f'provider_rows_s{seed}.json', 'w'))
    return out


E4.run = run
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[600]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    Path(a.out, f'{a.tag}_n2.json').write_text(json.dumps(dict(n2=A0.n2, light=a.light, fleet=a.fleet, spat_total=EF.N['total'], spat_valid=EF.N['valid'])))
