#!/usr/bin/env python3
"""Spider TSI evaluator (PROTOCOL_CITY_SPIDER_TSI_20261005): CITY_m4s_f1k_eval (UNCHANGED, imported with --spat-arm none; spider net, RLK
lights, fleet SPaT rebinding) with
  --tk none | fk:<q>:<table> | n2k:<table>:<model>    fleet SPaT: unavailable | forecast-K at q | N2K direct-only hybrid (fallback forecast-K q0.5)
  --light RLKQ:<ckpt>:A:B                          the frozen RLK light behind the demand adapter (halting + A n[0.1,2) + B n[2,5))
  --featlog DIR                                    per-second feature log feat_s<seed>.npz (phases, spent, H / V per green index, queries, times)
                                                   and the provider's first 20 000 feature rows (KS-1)
Sidecar <tag>_tk.json: provider counters and adapter decisions.  Other options as CITY_m4s_f1k_eval."""
import argparse, hashlib, json, sys
from collections import Counter
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--tk', default='none'); pre.add_argument('--featlog'); A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none'] + REST
import scripts.CITY_m4s_f1k_eval as FE  # noqa: E402
sys.argv = _argv
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
import scripts.CITY_spat_forecast_n2 as N2  # noqa: E402
import scripts.CITY_n2k as NK  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402
E4 = FE.E4; Q7 = FE.Q7; sha = lambda b: hashlib.sha256(b).hexdigest(); E4.SRC = f"{E4.SRC}+m4s_tsi:{sha(Path(__file__).read_bytes())}"
INFO = NetInfoK(Q7.NET_S); TR = N2.Tracker(); DBG = [] if A0.featlog else None; QC = Counter(); CUR = {}; STATS = {}
kind = A0.tk.split(':')[0]
if kind == 'none':
    SPAT = lambda tid, link: dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')  # noqa: E731
elif kind == 'fk':
    _, qq, tb = A0.tk.split(':', 2); SPAT = FK.make_spat_k(json.loads(Path(tb).read_text()), float(qq))[0]
else:
    _, tb, mp = A0.tk.split(':', 2); FKS = FK.make_spat_k(json.loads(Path(tb).read_text()), 0.5)[0]
    SPAT = NK.make_provider(mp, 0.5, INFO, TR, FKS, DBG); STATS['provider'] = SPAT.stats


def counted(tid, link):
    QC[tid] += 1; return SPAT(tid, link)


FE.BASE = counted


class LightRLKQ(LightRLK):
    def __init__(self, info, policy, A, B):
        super().__init__(info, policy); self.A, self.B = A, B; STATS['adapter'] = dict(A=A, B=B)

    def obs(self, tid):
        o, halt, cur = super().obs(tid)
        if o is None or not (self.A or self.B):
            return o, halt, cur
        ls = CE.ls; d = self.info.tls[tid]; k = len(d['greens']); nxt = (cur + 1) % k; q = []
        for s in (d['serve'][cur], d['serve'][nxt]):
            h = m1 = m2 = 0
            for l in s:
                for v in ls.lane.getLastStepVehicleIDs(l):
                    sp = ls.vehicle.getSpeed(v); h += sp < 0.1; m1 += 0.1 <= sp < 2.0; m2 += 2.0 <= sp < 5.0
            q.append(h + self.A * m1 + self.B * m2)
        o = o.copy(); o[0], o[1] = q[0] / 10, q[1] / 10
        return o, halt, cur


_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('RLKQ:'):
        ck, A, B = spec[5:].rsplit(':', 2); return Q7.NET_S, LightRLKQ(NetInfoK(Q7.NET_S), Q7.load_policy(ck), float(A), float(B)), [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light


class TLogger(E4.Logger):
    def __init__(self, *a, **k):
        super().__init__(*a, **k); self.ids_f = sorted(INFO.tls); self.P, self.S, self.H, self.V, self.Q, self.T = [], [], [], [], [], []; CUR['log'] = self; TR.__init__()

    def step(self, t):
        super().step(t); TR.step(self.ids_f)
        if A0.featlog:
            ls = CE.ls; p, s, h, v, qq = [], [], [], [], []
            for tid in self.ids_f:
                d = INFO.tls[tid]; p.append(ls.trafficlight.getPhase(tid)); s.append(ls.trafficlight.getSpentDuration(tid))
                hh = [sum(ls.lane.getLastStepHaltingNumber(l) for l in sv) for sv in d['serve']]; vv = [sum(ls.lane.getLastStepVehicleNumber(l) for l in sv) for sv in d['serve']]
                h.append((hh + [0] * NK.KMAX)[:NK.KMAX]); v.append((vv + [0] * NK.KMAX)[:NK.KMAX]); qq.append(QC.pop(tid, 0))
            self.P.append(p); self.S.append(s); self.H.append(h); self.V.append(v); self.Q.append(qq); self.T.append(int(t))


E4.Logger = TLogger
_run = E4.run


def run(a, seed, end):
    DBG is not None and DBG.clear(); out = _run(a, seed, end)
    if A0.featlog:
        L = CUR['log']; Path(A0.featlog).mkdir(parents=True, exist_ok=True)
        np.savez_compressed(Path(A0.featlog) / f'feat_s{seed}.npz', ids=np.array(L.ids_f), phases=np.array(L.P, np.int16), spent=np.array(L.S, np.float64),
                            H=np.array(L.H, np.int16), V=np.array(L.V, np.int16), Q=np.array(L.Q, np.int32), times=np.array(L.T, np.int32))
        if DBG is not None:
            json.dump(DBG, open(Path(A0.featlog) / f'provider_rows_s{seed}.json', 'w'))
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
    a = p.parse_args(REST); E4.main(a)
    Path(a.out, f'{a.tag}_tk.json').write_text(json.dumps(dict(tk=A0.tk, light=a.light, fleet=a.fleet, **STATS, queries=int(sum(QC.values())))))
