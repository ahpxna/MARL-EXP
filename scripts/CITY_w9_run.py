#!/usr/bin/env python3
"""W9 runner (PROTOCOL_CITY_WAVE9_20261005): run-time perturbations of the frozen TSI evaluation, installed by monkey-patching module objects
(no existing file is edited), then the W8 light_spec patch (RL-H 4..18; scripts/CITY_w8_run.py, imported unchanged) and the target script.
  modes:  lat:<s>      SPaT latency: the fleet gets the provider answer computed s seconds earlier, aged (ttg/ttr - age, floored at 0)
          loss:<p>     each light's SPaT broadcast lost w.p. p per second (crc32(seed, light, second)); fleet keeps the last delivered answer, aged
          det:<p>      adapter count: each vehicle detected w.p. p per second (crc32(seed, second, vehicle)); missed vehicles add nothing to q_g
          spn:<sd>     adapter count: Gaussian speed noise sd (m/s) before the 0.1 / 2 / 5 m/s bins
          em:<class>   emission class of every vehicle set at departure (first second keeps the default); prints the default class once
          idm          SUMO --carfollow.model IDM for every vehicle (the route vType sets no model)
          none         no perturbation (identity check)
Usage: CITY_w9_run.py <mode> scripts/<x>.py <args>"""
import os, runpy, sys, zlib
from pathlib import Path
from statistics import NormalDist
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w8_run  # noqa: E402,F401  (light_spec patch 4..18)
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402

MODE = sys.argv[1]; KIND, _, PAR = MODE.partition(':'); assert KIND in ('lat', 'loss', 'det', 'spn', 'em', 'idm', 'none'), MODE
ST = dict(seed=0); U = lambda *k: zlib.crc32(':'.join(map(str, k)).encode()) / 4294967296.0  # noqa: E731  deterministic uniform in [0, 1)
ND = NormalDist()


def _now():
    return float(CE.ls.simulation.getTime())


# ------------------------------------------------------------------ fleet side: the SPaT channel (wraps the provider the fleet module calls)
def _aged(s, age):
    if not s.get('valid'):
        return dict(s)
    o = dict(s); o['ttg'] = max(0.0, float(s['ttg']) - age); o['ttr'] = max(0.0, float(s['ttr']) - age); return o


def _channel(base):
    hist = {}; last = {}; inval = lambda: dict(ttg=0.0, ttr=0.0, valid=False, source='w9-undelivered')  # noqa: E731

    def spat(tid, link):
        s = base(tid, link); t = _now(); key = (tid, link)            # the provider is called on every query (its state is unchanged)
        if KIND == 'lat':
            L = float(PAR); h = hist.setdefault(key, []); h.append((t, s))
            while len(h) > 1 and h[1][0] <= t - L + 1e-9:
                h.pop(0)
            return _aged(h[0][1], t - h[0][0]) if h[0][0] <= t - L + 1e-9 else inval()
        if KIND == 'loss':
            if U(ST['seed'], tid, int(t)) >= float(PAR):              # delivered this second
                last[key] = (t, s); return s
            return _aged(last[key][1], t - last[key][0]) if key in last else inval()
        return s
    return spat


# ------------------------------------------------------------------ light side: the adapter's speed-binned count with sensing errors
class LightRLXW(E4.LightRLX):
    def obs(self, tid):
        if not (self.adapter.split(':')[0] == 'q' and (self.qa or self.qb)) or KIND not in ('det', 'spn'):
            return super().obs(tid)
        o, halt, cur = E4.LightRL.obs(self, tid); ls = CE.ls; d = self.info.tls[tid]; t = int(_now()); q = []
        for s in d['serve']:
            h = m1 = m2 = 0.0
            for lane in s:
                for v in ls.lane.getLastStepVehicleIDs(lane):
                    sp = ls.vehicle.getSpeed(v)
                    if KIND == 'det' and U(ST['seed'], t, v, 'det') >= float(PAR):
                        continue
                    if KIND == 'spn':
                        u = min(max(U(ST['seed'], t, v, 'spn'), 1e-12), 1 - 1e-12); sp = sp + float(PAR) * ND.inv_cdf(u)
                    h += sp < 0.1; m1 += 0.1 <= sp < 2.0; m2 += 2.0 <= sp < 5.0
            q.append(h + self.qa * m1 + self.qb * m2)
        o = o.copy(); o[0], o[1] = q[0] / 10, q[1] / 10
        return o, halt, cur


E4.LightRLX = LightRLXW


# ------------------------------------------------------------------ simulator: emission class / car-following model; per-run seed and channel
_rep = E4.run_episode
_SAW = dict(default=None)


def run_episode(net, rou, seed, light, cars, **kw):
    extra = tuple(kw.pop('extra', ()))
    if KIND == 'idm':
        extra = extra + ('--carfollow.model', 'IDM')
    if KIND == 'em':
        inner = light

        class EmLight:
            def step(self, t):
                for v in CE.ls.simulation.getDepartedIDList():
                    if _SAW['default'] is None:
                        _SAW['default'] = CE.ls.vehicle.getEmissionClass(v); print('W9 em: default emission class', _SAW['default'], '->', PAR, flush=True)
                    CE.ls.vehicle.setEmissionClass(v, PAR)
                if inner is not None:
                    inner.step(t)
        light = EmLight()
    return _rep(net, rou, seed, light, cars, extra=extra, **kw)


E4.run_episode = run_episode
_run = E4.run


def run(a, seed, end):
    ST['seed'] = int(seed)
    if KIND in ('lat', 'loss'):                                        # a fresh channel per run, wrapping whichever provider the evaluator installed
        for mn in ('scripts.CITY_eval_f1', 'scripts.CITY_eval_f1b'):
            m = sys.modules.get(mn)
            if m is not None and hasattr(m, 'BASE'):
                if not hasattr(m, '_W9_BASE0'):
                    m._W9_BASE0 = m.BASE
                m.BASE = _channel(m._W9_BASE0)
    out = _run(a, seed, end); out['w9_mode'] = MODE
    if KIND == 'em':
        out['w9_default_emission_class'] = _SAW['default']
    return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w9:{MODE}"
if __name__ == '__main__':
    target = sys.argv[2]; sys.argv = [target] + sys.argv[3:]; runpy.run_path(str(ROOT / target), run_name='__main__')
