#!/usr/bin/env python3
"""N3 grid4 evaluator (PROTOCOL_CITY_N3_FEEDBACK_20261005): CITY_eval_f1 (UNCHANGED, imported with --spat-arm none) with the N2 provider in
one of two modes, --n3 <q>:<pub|shadow>:<model.pt>:
  pub     the fleet receives the N2 forecast (= CITY_eval_n2)
  shadow  the forecast is computed at every fleet query but the fleet receives 'unavailable' (it drives sigma*; the light sees R's traffic)
Every 5th valid query (t, light, link, ttg, ttr) and the per-second phase of every light are logged; after each episode the realized time to
the queried event is computed (the first logged second at which the link state changes as asked) and the error pred - realized is
summarized in the sidecar <out>/<tag>_n3.json, overall and by horizon bucket (realized 0-5, 5-15, 15-30, >30 s), separately for ttg / ttr.
--featlog DIR writes the CITY_n2_collect feature file (refit data under the deployed service, N3b)."""
import argparse, hashlib, json, sys
from collections import Counter
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--n3', required=True); pre.add_argument('--featlog'); A0, REST = pre.parse_known_args()
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none'] + REST
import scripts.CITY_eval_f1 as EF  # noqa: E402
sys.argv = _argv
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_spat_forecast_n2 as N2  # noqa: E402
E4 = EF.E4; sha = lambda b: hashlib.sha256(b).hexdigest(); q, MODE, mp = A0.n3.split(':', 2); q = float(q); assert MODE in ('pub', 'shadow')
TR = N2.Tracker(); INFO = E4.NetInfo(E4.Q7.NET_S); SPAT = N2.make_spat_n2(mp, q, INFO, TR, None)
EF.META.update(n3=A0.n3, model_sha256=sha(Path(mp).read_bytes())); E4.SRC = f"{E4.SRC}+n3:{sha(Path(__file__).read_bytes())}"
QC = Counter(); LOG = dict(q=[], ph={}, n=0, states={}); SUM = []; CUR = {}


def served(tid, t, link):
    s = SPAT(tid, link); QC[tid] += 1
    if s['valid'] and s['ttr'] < 900:
        LOG['n'] += 1
        if LOG['n'] % 5 == 0:
            ls = CE.ls; st = LOG['states'].get(tid) or [x.state for x in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
            LOG['q'].append((float(t), tid, link, s['ttg'], s['ttr'], st[ls.trafficlight.getPhase(tid)][link] in 'Gg'))
    if MODE == 'shadow':
        return dict(ttg=0.0, ttr=0.0, valid=False, source='shadow')
    return s


EF.BASE = lambda tid, link: served(tid, CE.ls.simulation.getTime(), link)


class TLogger(E4.Logger):
    def __init__(self, *a, **k):
        super().__init__(*a, **k); self.ids_f = sorted(self.info.tls); self.P, self.S, self.H, self.V, self.Q = [], [], [], [], []; CUR['log'] = self; TR.__init__()

    def step(self, t):
        super().step(t); TR.step(self.ids_f); ls = CE.ls
        if not LOG['states']:
            LOG['states'] = {tid: [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases] for tid in self.ids_f}
        p = []
        for tid in self.ids_f:
            ph = ls.trafficlight.getPhase(tid); LOG['ph'].setdefault(tid, {})[int(t)] = ph; p.append(ph)
        if A0.featlog:
            s, h, v, qq = [], [], [], []
            for tid in self.ids_f:
                d = self.info.tls[tid]; s.append(ls.trafficlight.getSpentDuration(tid))
                h.append([sum(ls.lane.getLastStepHaltingNumber(l) for l in sv) for sv in d['serve'][:2]]); v.append([sum(ls.lane.getLastStepVehicleNumber(l) for l in sv) for sv in d['serve'][:2]]); qq.append(QC.pop(tid, 0))
            self.P.append(p); self.S.append(s); self.H.append(h); self.V.append(v); self.Q.append(qq)


E4.Logger = TLogger
_run = E4.run
BUCK = ((0, 5), (5, 15), (15, 30), (30, 1e9))


def summarize(seed):
    E = {'ttg': [], 'ttr': []}; cens = 0
    for t, tid, link, ttg, ttr, gnow in LOG['q']:
        P = LOG['ph'].get(tid); st = LOG['states'][tid]; i0 = int(t); want = not gnow; target = ttg if want else ttr; hit = None
        for i in range(i0 + 1, max(P) + 1):
            if i in P:
                g = st[P[i]][link] in 'Gg'
                if (want and g) or ((not want) and not g):
                    hit = i - i0; break
        if hit is None:
            cens += 1; continue
        E['ttg' if want else 'ttr'].append((target - hit, hit))
    out = dict(seed=seed, censored=cens)
    for k, v in E.items():
        a = np.array(v) if v else np.zeros((0, 2)); out[k] = dict(n=len(a), mae=float(np.abs(a[:, 0]).mean()) if len(a) else None, bias=float(a[:, 0].mean()) if len(a) else None,
                                                             by_h={f'{lo}-{hi:g}': (int(((a[:, 1] >= lo) & (a[:, 1] < hi)).sum()), float(np.abs(a[(a[:, 1] >= lo) & (a[:, 1] < hi), 0]).mean()) if ((a[:, 1] >= lo) & (a[:, 1] < hi)).any() else None) for lo, hi in BUCK})
    return out


def run(a, seed, end):
    LOG['q'].clear(); LOG['ph'].clear(); LOG['n'] = 0; LOG['states'] = {}; out = _run(a, seed, end); SUM.append(summarize(seed))
    if A0.featlog:
        L = CUR['log']; Path(A0.featlog).mkdir(parents=True, exist_ok=True)
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
    p.add_argument('--seeds', type=int, nargs='+', default=[600]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    Path(a.out, f'{a.tag}_n3.json').write_text(json.dumps(dict(n3=A0.n3, mode=MODE, runs=SUM)))
