#!/usr/bin/env python3
"""Multi-green light controller for the second network (G4; prepared 04/10/2026 wake 4, not used by any registered job yet).
scripts/CITY_env.LightRL drives only the first two green phases of a program; RESCO cologne8 has lights with 3-4 greens.
  NetInfoK   every green phase of the program and the incoming lanes it serves
  LightRLK   keep / ADVANCE decision every DT_L s after MIN_G: advance = go to the phase after the current green (its yellow), the program
             then reaches the next green in cycle order.  Observation (7, same width as LightRL so the Q7 DQN shape is reused):
             [halting on current green's lanes / 10, halting on the next green's lanes / 10, vehicles current / 20, vehicles next / 20,
              current green index / max(1, k-1), spent / 60, 1 if the next green wraps the cycle else 0]
             reward -(halting on all served lanes)/10 at the decision (RL-H's reward), recorded like LightRL.
On a two-green light the decision set equals LightRL's (keep / switch to the other green); the observation encoding differs, so a
grid4 RL-H checkpoint is NOT transferable — lights for the second network are trained there."""
from __future__ import annotations
import numpy as np
import sumolib
import scripts.CITY_env as CE
from scripts.CITY_env import DT_L, MIN_G


class NetInfoK:
    def __init__(self, net_file):
        net = sumolib.net.readNet(net_file, withPrograms=True); self.tls = {}
        for t in net.getTrafficLights():
            prog = list(t.getPrograms().values())[0]; phases = prog.getPhases(); links = {}
            for in_lane, _o, idx in t.getConnections():
                links.setdefault(idx, in_lane.getID())
            greens = [i for i, p in enumerate(phases) if ('G' in p.state or 'g' in p.state) and 'y' not in p.state.lower()]
            if len(greens) < 2:
                continue
            serve = [sorted({links[k] for k, c in enumerate(phases[i].state) if c in 'Gg' and k in links}) for i in greens]
            self.tls[t.getID()] = dict(greens=greens, n_phases=len(phases), serve=serve, lanes=sorted({l for s in serve for l in s}))


class LightRLK:
    def __init__(self, info: NetInfoK, policy, record=False):
        self.info, self.policy, self.record = info, policy, record; self.prev = {}; self.trans = []; self.ids = list(info.tls)

    def obs(self, tid):
        ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
        if ph not in d['greens']:
            return None, 0, -1
        cur = d['greens'].index(ph); k = len(d['greens']); nxt = (cur + 1) % k
        h = lambda s: sum(ls.lane.getLastStepHaltingNumber(l) for l in s); n = lambda s: sum(ls.lane.getLastStepVehicleNumber(l) for l in s)
        o = np.array([h(d['serve'][cur]) / 10, h(d['serve'][nxt]) / 10, n(d['serve'][cur]) / 20, n(d['serve'][nxt]) / 20, cur / max(1, k - 1),
                      ls.trafficlight.getSpentDuration(tid) / 60, float(nxt == 0)], np.float32)
        return o, sum(h(s) for s in d['serve']), cur

    def step(self, t):
        if int(t) % DT_L:
            return
        ls = CE.ls; todo, O, R = [], [], []
        for tid in self.ids:
            o, halt, cur = self.obs(tid)
            if cur < 0:
                continue
            if ls.trafficlight.getSpentDuration(tid) < MIN_G:
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            todo.append((tid, cur)); O.append(o); R.append(-halt / 10)
        if not todo:
            return
        A = np.asarray(self.policy(np.stack(O)))
        for (tid, cur), o, r, a in zip(todo, O, R, A):
            if self.record:
                if tid in self.prev:
                    po, pa = self.prev[tid]; self.trans.append((po, pa, r, o, 0.0))
                self.prev[tid] = (o, int(a))
            d = self.info.tls[tid]
            if a == 1:
                ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
            else:
                ls.trafficlight.setPhaseDuration(tid, 1e5)
