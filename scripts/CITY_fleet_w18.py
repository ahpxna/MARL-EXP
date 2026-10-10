#!/usr/bin/env python3
"""W18 fleet designs (PROTOCOL_CITY_WAVE18_20261008).  No existing file is edited.
  CarPPOLQ (D2, queue-aware and no-creep): CITY_fleet_v11.CarPPOL with the rule speed replaced by
      v_rule = min(v_allowed, d_q / (ttg + t_q)),  d_q = max(0, dist - 7.5 m * q),  t_q = 2.0 s * q,  q = halting vehicles on the car's lane
  (arrive at the back of the queue when it starts to discharge); if v_rule < VMIN = 5 m/s the car is released to SUMO (it stops as a human
  would) instead of creeping.  Everything else (residual action, credit, observation) is CarPPOL's.
  gentle(spec) (D5): the always-SUMO fleet (L-ACT:0, guard always) whose agents get setAccel(a) at departure: gentler departures, no SPaT."""
from __future__ import annotations
import math
import numpy as np
import torch
import scripts.CITY_env as CE
import scripts.CITY_fleet_v8 as V8
import scripts.CITY_fleet_v10 as V10
import scripts.CITY_fleet_v11 as V11
import scripts.CITY_glosa_lane as GL
from scripts.CITY_spat_feature import spat
from scripts.CITY_fleet_v11 import DV, SIG, DACT
VMIN, HDW, SPACE = 5.0, 2.0, 7.5


class CarPPOLQ(V11.CarPPOL):
    def step(self, t):
        ls = CE.ls
        if self.record:                                            # credit the cost observed now to each open segment's latest decision
            for v, seg in self.open.items():
                try:
                    c = V10.dense_cost(ls, v)
                except Exception:
                    c = None
                if c is None:
                    self.stats['dense_none'] += 1
                else:
                    seg['dec'][-1]['rew'] -= c; self.stats['dense_n'] += 1
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v); ls.vehicle.setImperfection(v, SIG)
        for v in ls.simulation.getArrivedIDList():
            if v in self.agents:
                if v in self.open:
                    self.stats['terminal_arrival'] += 1
                self._close(v, 'terminal'); self.agents.discard(v)
        todo = []
        for v in list(self.agents):
            try:
                lane = ls.vehicle.getLaneID(v); sp = ls.vehicle.getSpeed(v)
            except Exception:
                self.stats['exc'] += 1; continue
            if lane == '' or not V8.ok(sp):
                self.stats['teleport_hidden'] += 1
                if v in self.open:
                    self.stats['gap'] += 1; self._close(v, 'truncated')
                continue
            try:
                nt = ls.vehicle.getNextTLS(v)
                if not nt or nt[0][2] > V8.ZONE:
                    if v in self.open:
                        self.stats['terminal_exit'] += 1; self._close(v, 'terminal')
                    ls.vehicle.setSpeed(v, -1); self.ctrl.discard(v); continue
                tid, link, dist, st = nt[0]; s = spat(tid, link); vl = ls.vehicle.getAllowedSpeed(v)
                if not (st not in 'Gg' and s['valid'] and s['ttg'] > 0 and dist <= DACT and GL.lane_ok(ls, v)) or not (V8.ok(vl) and vl > 0):
                    ls.vehicle.setSpeed(v, -1); self.stats['released'] += 1; continue
                q = ls.lane.getLastStepHaltingNumber(ls.vehicle.getLaneID(v)); dq = max(0.0, dist - SPACE * q); tq = HDW * q      # W18 D2
                vr = min(vl, dq / (s['ttg'] + tq))
                if vr < VMIN:                                          # no creep: below VMIN the car is released (drives as a human)
                    ls.vehicle.setSpeed(v, -1); self.stats['released'] += 1; self.stats['nocreep'] = self.stats.get('nocreep', 0) + 1; continue
                o = V8.build_obs(ls, v, nt[0], sp, vl, True, self.stats)
            except Exception:
                self.stats['exc'] += 1; continue
            todo.append((v, tid, sp, vl, vr, o))
        if not todo:
            return
        O = torch.as_tensor(np.stack([x[5] for x in todo]))
        with torch.no_grad():
            d = self.net.dist(O); U = d.mean if self.det else d.sample(); LP = d.log_prob(U); V = self.net.value(O)
        U, LP, V = U.numpy(), LP.numpy(), V.numpy()
        for (v, tid, sp, vl, vr, o), u, lp, val in zip(todo, U, LP, V):
            cmd = float(min(max(vr + DV * math.tanh(float(u)), 0.0), vl))
            try:
                ls.vehicle.setSpeed(v, cmd)
            except Exception:
                self.stats['exc'] += 1; continue
            self.decisions += 1; self.stats['decisions'] += 1; self.stats['active'] += 1; self.ctrl.add(v)
            if self.record:
                dec = dict(vid=v, t=t, obs=o, u=float(u), logp=float(lp), val=float(val), a=cmd - sp, sp=sp, cmd=cmd, rew=0.0, tid=tid)
                self.open.setdefault(v, dict(vid=v, dec=[], end=None, boot_obs=None))['dec'].append(dec)
            self.cmd_log.append((t, v, cmd))
        self.digest.update(f'{t}|{len(todo)}'.encode())
