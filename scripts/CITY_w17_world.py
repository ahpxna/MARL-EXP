#!/usr/bin/env python3
"""W17 (PROTOCOL_CITY_WAVE17_20261008): run any target in the FIELD-MATCHED world: a copy of CITY_w16_idm.py whose vType attributes come
from research/city_sim/w17_20261008/human.json (W17-0 joint calibration; IDM with delta), route copies in demand/grid4_w17, light specs
RL-H 29..33 = $W17_LIGHTS/RL-H_t<k>.pt (plus 4..23 via CITY_w15_run), emission class W17_EM, rows w17_world=True, check KW17-0.
Original docstring: W16 (PROTOCOL_CITY_WAVE16_20261008): run any target in the IDM world.  Every SUMO start made through CITY_env.run_episode on a grid4
route file runs on its IDM copy research/city_sim/demand/grid4_idm/rou_s<seed>.xml, whose vType v_passenger carries the IDM calibrated on
NGSIM Peachtree (F4) (Amendment A1: the grid4 routes define v_passenger, so a DEFAULT_VEHTYPE redefinition does not apply).  Patches CE.run_episode, CITY_eval4.run_episode and every already-imported module attribute bound to the original
run_episode (CITY_q7_cross_version imports it by name, which the W13 IDM wrapper did not reach for light training).  Light specs:
RL-H 4..23 via CITY_w15_run (W8 + W15 sets) and RL-H 24..28 = $W16_LIGHTS/RL-H_t<k>.pt.  Optional W16_EM=<class> sets every vehicle's
emission class at departure.  KW16-0 (once per process, on the first vehicle): vType tau 0.742 and decel 2.054 (+-0.001), accel and minGap
read back too; exit on mismatch.  Rows get w16_idm=True.  No file is edited.  Usage: CITY_w16_idm.py <target script> <its args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
_orig = CE.run_episode
import scripts.CITY_w15_run  # noqa: E402,F401  (light specs 4..23)
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import json  # noqa: E402
HUM = json.loads((ROOT / 'research/city_sim/w17_20261008/human.json').read_text()); EM = os.environ.get('W17_EM'); ST = dict(checked=False)
W16L = Path(os.environ['W17_LIGHTS']) if os.environ.get('W17_LIGHTS') else ROOT / 'research/city_sim/w17_20261008/fresh5/lights'
_prev = X2.light_spec


def light_spec(s):
    k, _, t = s.partition(':')
    if k == 'RL-H' and t and 29 <= int(t) <= 33:
        return X2.Q7.NET_S, W16L / f'RL-H_t{int(t)}.pt', None
    return _prev(s)


X2.light_spec = light_spec


class _Wrap:
    def __init__(self, inner):
        self.inner = inner

    def step(self, t):
        ls = CE.ls
        if not ST['checked']:
            ids = ls.vehicle.getIDList()
            if ids:
                vt = ls.vehicle.getTypeID(ids[0]); tau = ls.vehicletype.getTau(vt); dec = ls.vehicletype.getDecel(vt)
                acc = ls.vehicletype.getAccel(vt); mg = ls.vehicletype.getMinGap(vt)
                print(f'KW17-0: type {vt} tau {tau} decel {dec} accel {acc} minGap {mg}', flush=True); ST['checked'] = True
                if any(abs(x - HUM[k]) > 1e-3 for x, k in ((tau, 'tau'), (dec, 'decel'), (acc, 'accel'), (mg, 'minGap'))):
                    raise SystemExit('KW17-0 FAIL: vehicle type is not the W17 human')
        if EM:
            for v in ls.simulation.getDepartedIDList():
                ls.vehicle.setEmissionClass(v, EM)
        if self.inner is not None:
            self.inner.step(t)

    def __getattr__(self, k):
        return getattr(self.inner, k)


IDMV = (f'carFollowModel="{HUM["carFollowModel"]}" accel="{HUM["accel"]}" decel="{HUM["decel"]}" tau="{HUM["tau"]}" minGap="{HUM["minGap"]}" '
        f'delta="{HUM["delta"]}"'); G4 = ROOT / 'research/city_sim/demand/grid4'
G4I = ROOT / 'research/city_sim/demand/grid4_w17'


def idm_rou(rou):
    """grid4 route file -> its IDM copy (vType v_passenger gets the W16 IDM attributes); created atomically on first use."""
    p = Path(rou)
    if p.parent.resolve() != G4.resolve():
        return rou
    q = G4I / p.name
    if not q.exists():
        G4I.mkdir(parents=True, exist_ok=True); src = p.read_text(); tag = '<vType id="v_passenger" vClass="passenger"/>'
        assert src.count(tag) == 1, f'KW17-R FAIL: vType line not found once in {p}'
        tmp = q.with_suffix(f'.tmp{os.getpid()}'); tmp.write_text(src.replace(tag, f'<vType id="v_passenger" vClass="passenger" {IDMV}/>')); os.replace(tmp, q)
    return str(q)


def run_episode(net, rou, seed, light=None, cars=None, **kw):
    return _orig(net, idm_rou(rou), seed, _Wrap(light), cars, **kw)


CE.run_episode = run_episode; E4.run_episode = run_episode
for _m in list(sys.modules.values()):                                  # rebind names imported before this patch
    try:
        if getattr(_m, 'run_episode', None) is _orig:
            setattr(_m, 'run_episode', run_episode)
    except Exception:
        pass
_run = E4.run


def run(a, seed, end):
    out = _run(a, seed, end); out.update(w17_world=True, w17_em=EM); return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w17world:{EM}"
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]
    runpy.run_path(str(ROOT / target), run_name='__main__')
