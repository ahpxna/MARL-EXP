#!/usr/bin/env python3
"""M4 stage 4a evaluator (PROTOCOL_CITY_M4_ARTERIAL_20261004 Amendment M4-A6) on spider (CITY_m4s_run patches):
  --light WCK:<RLK checkpoint>:<W>   LightRLK's keep / advance decisions; an advance decided at t is EXECUTED at t + W (green held meanwhile, no
                                     new decision while pending); W = 0 is LightRLK exactly (check KW-1)
  --light RLK:<checkpoint>           LightRLK
  --spat-mode commit | none          commit: while a switch is pending at the light, links served by the current green get ttr = t_e - t, links
                                     served only by the NEXT green in cycle order get ttg = t_e - t + (program durations of the non-green phases
                                     between the two greens) + OBS; everything else 'unavailable'.  none: always 'unavailable' (the rule fleet
                                     then drives exactly as σ*, KM4-3c), used for R and the shadow rows.
Fleets: every CITY_eval6_v11 spec (GLOSAL:0.3 = the rule).  Sidecar <tag>_wck.json per seed: commitments, executions (green-end error), observed
onset errors (observed - promised), onsets into an unexpected green, spat calls (total / valid)."""
import argparse, hashlib, json, sys
from collections import Counter
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
pre = argparse.ArgumentParser(add_help=False); pre.add_argument('--spat-mode', choices=['commit', 'none'], required=True); A0, REST = pre.parse_known_args()
import scripts.CITY_m4s_run  # noqa: E402,F401  (spider patches)
import numpy as np  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6_v11 as _E  # noqa: E402,F401
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_fleet_v8 as V8, scripts.CITY_es_glosa as ES, scripts.CITY_glosa_lane as GL, scripts.CITY_glosa_lane_d as LD, scripts.CITY_fleet_v11 as V11  # noqa: E402,E401
from scripts.CITY_env import DT_L, MIN_G  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402
sha = lambda b: hashlib.sha256(b).hexdigest()
E4.SRC = f"{E4.SRC}+m4s_wck{A0.spat_mode}:{sha(Path(__file__).read_bytes())}"
OBS = 1.0; CUR = {}; N = dict(total=0, valid=0); SIDE = {}


class LightWCK(LightRLK):
    def __init__(self, info, policy, W):
        super().__init__(info, policy); self.W = float(W); self.pending = {}; self.await_on = {}; self.st = {}; self.ng = {}
        self.log = dict(commits=0, exec_err=Counter(), onset_err=Counter(), onset_wrong_green=0)

    def prog(self, tid):
        if tid not in self.st:
            ph = CE.ls.trafficlight.getAllProgramLogics(tid)[0].phases; d = self.info.tls[tid]; g = d['greens']; n = d['n_phases']
            self.st[tid] = [p.state for p in ph]; ng = []
            for i, gi in enumerate(g):
                j, s = (gi + 1) % n, 0.0
                while j != g[(i + 1) % len(g)]:
                    s += float(ph[j].duration); j = (j + 1) % n
                ng.append(s)
            self.ng[tid] = ng
        return self.st[tid], self.ng[tid]

    def step(self, t):
        ls = CE.ls
        for tid, (exp, g2) in list(self.await_on.items()):
            ph = ls.trafficlight.getPhase(tid)
            if ph in self.info.tls[tid]['greens']:
                self.log['onset_err'][round(float(t) - exp, 6)] += 1; self.log['onset_wrong_green'] += int(ph != g2); del self.await_on[tid]
        for tid, te in list(self.pending.items()):
            if t >= te:
                d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid); cur = d['greens'].index(ph); _st, ng = self.prog(tid)
                ls.trafficlight.setPhase(tid, (ph + 1) % d['n_phases']); self.log['exec_err'][round(float(t) - te, 6)] += 1; del self.pending[tid]
                self.await_on[tid] = (te + ng[cur] + OBS, d['greens'][(cur + 1) % len(d['greens'])])
        if int(t) % DT_L:
            return
        todo, O = [], []
        for tid in self.ids:
            o, halt, cur = self.obs(tid)
            if cur < 0:
                continue
            if tid in self.pending or ls.trafficlight.getSpentDuration(tid) < MIN_G:
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            todo.append((tid, cur)); O.append(o)
        if not todo:
            return
        A = np.asarray(self.policy(np.stack(O)))
        for (tid, cur), a in zip(todo, A):
            d = self.info.tls[tid]
            if a == 1 and self.W == 0:
                ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
            elif a == 1:
                self.prog(tid); self.pending[tid] = float(t) + self.W; self.log['commits'] += 1; ls.trafficlight.setPhaseDuration(tid, 1e5)
            else:
                ls.trafficlight.setPhaseDuration(tid, 1e5)


_bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('WCK:'):
        ck, W = spec[4:].rsplit(':', 1); L = LightWCK(NetInfoK(Q7.NET_S), Q7.load_policy(ck), float(W)); CUR['light'] = L; return Q7.NET_S, L, [], None
    if spec.startswith('RLK:'):
        L = LightRLK(NetInfoK(Q7.NET_S), Q7.load_policy(spec[4:])); CUR['light'] = L; return Q7.NET_S, L, [], None
    CUR['light'] = None; return _bl(spec, info, adapter, box)


E4.build_light = build_light
UNAV = dict(ttg=0.0, ttr=0.0, valid=False, source='unavailable')


def spat_wck(tid, link):
    N['total'] += 1; L = CUR.get('light')
    if A0.spat_mode == 'commit' and isinstance(L, LightWCK) and tid in L.pending:
        ls = CE.ls; t = ls.simulation.getTime(); te = L.pending[tid]; d = L.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
        if ph in d['greens']:
            st, ng = L.prog(tid); cur = d['greens'].index(ph); nxt = d['greens'][(cur + 1) % len(d['greens'])]
            g_now, g_nxt = st[ph][link] in 'Gg', st[nxt][link] in 'Gg'
            if g_now and not g_nxt:
                N['valid'] += 1; return dict(ttg=0.0, ttr=te - t, valid=True, source='commitment')
            if g_nxt and not g_now:
                N['valid'] += 1; return dict(ttg=te - t + ng[cur] + OBS, ttr=0.0, valid=True, source='commitment')
    return UNAV


for m in (V8, ES, GL, LD, V11):
    m.spat = spat_wck
_run = E4.run


def run(a, seed, end):
    n0 = dict(N); out = _run(a, seed, end); L = CUR.get('light')
    S = dict(spat_total=N['total'] - n0['total'], spat_valid=N['valid'] - n0['valid'])
    if isinstance(L, LightWCK):
        S.update(commits=L.log['commits'], exec_err={str(k): v for k, v in L.log['exec_err'].items()}, onset_err={str(k): v for k, v in L.log['onset_err'].items()},
                 onset_wrong_green=L.log['onset_wrong_green'], pending_at_end=len(L.pending), awaiting_at_end=len(L.await_on))
    SIDE[str(seed)] = S; return out


E4.run = run
if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(REST); E4.main(a)
    Path(a.out, f'{a.tag}_wck.json').write_text(json.dumps(dict(spat_mode=A0.spat_mode, light=a.light, fleet=a.fleet, per_seed=SIDE, source_sha256=sha(Path(__file__).read_bytes()))))
