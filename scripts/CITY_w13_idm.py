#!/usr/bin/env python3
"""W13-6a (PROTOCOL_CITY_WAVE13_20261006, Amendment A1): run any target under SUMO's IDM car-following model for EVERY simulation, including
those started through CITY_env.run_episode directly (CITY_m3_train_E.prep, used by the closed-loop table prep), which CITY_w9_run's idm mode
does not reach (it patches CITY_eval4.run_episode only).  Patches CE.run_episode and E4.run_episode (no file is edited); optional W13_EM=<class>
sets every vehicle's emission class at departure (as CITY_w9_run em:).  Imports the W8 light_spec patch (RL-H 4..18).  Rows get w13_idm=True.
Self-check KI-0 (printed once per process): the first simulation's vehicle type car-following model is read back via libsumo and must be IDM.
Usage: CITY_w13_idm.py <target script> <its args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w8_run  # noqa: E402,F401
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
EM = os.environ.get('W13_EM'); _rep = CE.run_episode; ST = dict(checked=False)


class _Wrap:
    def __init__(self, inner):
        self.inner = inner

    def step(self, t):
        ls = CE.ls
        if not ST['checked']:
            ids = ls.vehicle.getIDList()
            if ids:
                vt = ls.vehicle.getTypeID(ids[0]); cf = ls.vehicletype.getParameter(vt, 'carFollowModel') if hasattr(ls.vehicletype, 'getParameter') else '?'
                print(f'KI-0: vehicle type {vt} carFollowModel {cf!r}', flush=True); ST['checked'] = True
                if cf not in ('IDM', '?', ''):
                    raise SystemExit(f'KI-0 FAIL: carFollowModel {cf}')
        if EM:
            for v in ls.simulation.getDepartedIDList():
                ls.vehicle.setEmissionClass(v, EM)
        if self.inner is not None:
            self.inner.step(t)

    def __getattr__(self, k):
        return getattr(self.inner, k)


def run_episode(net, rou, seed, light=None, cars=None, **kw):
    kw['extra'] = tuple(kw.get('extra', ())) + ('--carfollow.model', 'IDM')
    return _rep(net, rou, seed, _Wrap(light), cars, **kw)


CE.run_episode = run_episode; E4.run_episode = run_episode
_run = E4.run


def run(a, seed, end):
    out = _run(a, seed, end); out.update(w13_idm=True, w13_em=EM); return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w13idm:{EM}"
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]
    runpy.run_path(str(ROOT / target), run_name='__main__')
