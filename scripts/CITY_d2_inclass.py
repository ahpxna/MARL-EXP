#!/usr/bin/env python3
"""D2 stage 3 (04/10/2026): is a GOOD behaviour representable in the continuous setSpeed(v + a) class at all?  A hand-written in-class
controller with the same information as GLOSA: in the zone, every second, command v + a with a in [LO, HI]:
  own movement not green and ttg valid -> a = clip(min(v_allowed, d / ttg) - v, LO, HI)   (GLOSA target)
  green (or no valid ttg)              -> a = clip(v_allowed - v, LO, HI)               (accelerate to the limit; SUMO safety still caps)
No release inside the zone (that is the point: the learned class has no release); release on leaving the zone.  Evaluated by
CITY_d1_reward_alignment.py as fleet spec IC:GLOSA (patched below).  Not a candidate method; a representability control."""
import sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
from scripts.CITY_spat_feature import spat  # noqa: E402


class CarICGlosa(V8.CarGLOSA):
    def step(self, t):
        ls = CE.ls
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v)
        for v in ls.simulation.getArrivedIDList():
            self.agents.discard(v)
        for v in list(self.agents):
            try:
                nt = ls.vehicle.getNextTLS(v)
                if not nt or nt[0][2] > V8.ZONE:
                    ls.vehicle.setSpeed(v, -1); continue
                tid, link, dist, st = nt[0]; sp = ls.vehicle.getSpeed(v); vl = ls.vehicle.getAllowedSpeed(v)
                if not (V8.ok(sp) and V8.ok(vl)):
                    continue
                s = spat(tid, link); self.decisions += 1
                tgt = min(vl, dist / s['ttg']) if (st not in 'Gg' and s['valid'] and s['ttg'] > 0) else vl
                a = float(np.clip(tgt - sp, V8.LO, V8.HI)); ls.vehicle.setSpeed(v, float(min(max(sp + a, 0.0), vl))); self.fired += 1
            except Exception:
                continue
