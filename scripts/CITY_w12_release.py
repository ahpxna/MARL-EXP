#!/usr/bin/env python3
"""W12-3 S2a (PROTOCOL_CITY_WAVE12_20261006, Amendment A4): closed-loop release of gliding agents.  Patches CITY_glosa_lane.CarGlosaL.step
(the lane-aware GLOSA rule fleet) so that, at the moment the rule would command a glide, the agent is released to its base driver for that
second when
  W12_REL=targeted   a human vehicle follows within 50 m (getFollower(v, 50));
  W12_REL=random:p   a deterministic hash of (traffic seed, vehicle, second) falls below p (the matched-rate control);
  W12_REL=none       never (identity check KR-1).
Counters per run (rel_glide_s, rel_released) are added to the evaluator's output row.  Everything else is the original step, line for line.
Usage: W12_REL=<mode> CITY_w12_release.py <target script> <its args>"""
import hashlib, os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
TARGET, ARGS = sys.argv[1], sys.argv[2:]
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
MODE = os.environ.get('W12_REL', 'none'); P = float(MODE.split(':', 1)[1]) if MODE.startswith('random:') else 0.0
CNT = dict(glide=0, rel=0, seed=0)


def U(seed, v, t):
    h = hashlib.sha256(f'{seed}|{v}|{t}'.encode()).digest(); return int.from_bytes(h[:8], 'big') / 2 ** 64


def step(self, t):
    ls = CE.ls
    for v in ls.simulation.getDepartedIDList():
        if self.is_agent(v):
            self.agents.add(v)
            if self.base_sigma is not None:
                ls.vehicle.setImperfection(v, self.base_sigma)
    for v in ls.simulation.getArrivedIDList():
        self.agents.discard(v)
    for v in list(self.agents):
        try:
            nt = ls.vehicle.getNextTLS(v)
            if not nt or nt[0][2] > V8.ZONE:
                ls.vehicle.setSpeed(v, -1); continue
            tid, link, dist, st = nt[0]; s = GL.spat(tid, link); self.decisions += 1
            if st not in 'Gg' and s['valid'] and s['ttg'] > 0 and dist <= self.dact:
                if self.lane_aware and not GL.lane_ok(ls, v):
                    ls.vehicle.setSpeed(v, -1); self.lane_released += 1; continue
                CNT['glide'] += 1                                                     # W12-3: a glide would be commanded now
                if MODE == 'targeted':
                    f = ls.vehicle.getFollower(v, 50.0)
                    if f and f[0] and not self.is_agent(f[0]):
                        ls.vehicle.setSpeed(v, -1); CNT['rel'] += 1; continue
                elif MODE.startswith('random:') and U(CNT['seed'], v, int(t)) < P:
                    ls.vehicle.setSpeed(v, -1); CNT['rel'] += 1; continue
                vl = ls.vehicle.getAllowedSpeed(v); ls.vehicle.setSpeed(v, float(min(vl, max(self.vlo, dist / (s['ttg'] + self.b))))); self.fired += 1
            else:
                ls.vehicle.setSpeed(v, -1)
        except Exception:
            continue


GL.CarGlosaL.step = step
_run = E4.run


def run(a, seed, end):
    CNT.update(glide=0, rel=0, seed=int(seed)); out = _run(a, seed, end)
    out.update(rel_mode=MODE, rel_glide_s=CNT['glide'], rel_released=CNT['rel']); return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w12release:{MODE}"
if __name__ == '__main__':
    sys.argv = [TARGET] + ARGS; runpy.run_path(str(ROOT / TARGET), run_name='__main__')
