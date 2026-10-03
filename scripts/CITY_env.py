#!/usr/bin/env python3
"""Two-population city environment on SUMO (libsumo) for the C1 experiment (02/10/2026 18:2x EDT; direction
research/papers/audits/CITY_TWO_POPULATION_NOVELTY_20261002.md; protocol research/city_sim/PROTOCOL_CITY_C1_20261002.md, written
before any C1 run).

LIGHTS (one controller per traffic light with at least two green phases):
  'fixed'     the net's own static program (no control);
  'actuated'  the net's own actuated program (use the actuated net file; no control);
  LightRL     learned keep/switch decision every DT_L s in a green phase once MIN_G s have passed; the switch goes through the
              program's yellow; optional MAX_G (compatible mode: a forced switch, which keeps time-in-phase inside a range).
              Observation per light (7): for each of the two green phases, halting and vehicle counts on the lanes it serves
              (/10, /20); the current green one-hot; time in phase / 60.  Reward: −(halting on incoming lanes)/10 at the decision.
CARS: every vehicle is human (SUMO Krauss) unless it is drawn into the agent share rho (seeded per vehicle id).  An AGENT car
  within ZONE m upstream of its next signalised stop line sets its speed every second: v ← clip(v + a, 0, v_max), a ∈ ACC, with
  SUMO's safety checks kept (it cannot run a red or hit its leader).  Observation (6): distance / ZONE, v / 14, green, yellow,
  time in phase / 60, leader gap / 100 (1 if none within 100 m).  Stage cost: 1 + 0.05 a² + IDLE·[v' < 0.1]; an approach ends
  when the car passes the stop line (terminal).
Everything a controller reads is legal at deployment (own lane, own signal head, own leader); no future signal times.
"""
from __future__ import annotations
import math
import numpy as np
import sumolib
import libsumo as ls
import traci.constants as tc

ACC = np.array([-3.0, -2.0, -1.0, 0.0, 1.0, 2.0]); NA_CAR = len(ACC)
ZONE, IDLE = 200.0, 1.0
DT_L, MIN_G, YELLOW = 5, 5, 3


class NetInfo:
    """Green phases and the lanes each serves, per traffic light (from the net file's program)."""

    def __init__(self, net_file):
        net = sumolib.net.readNet(net_file, withPrograms=True); self.tls = {}
        for t in net.getTrafficLights():
            prog = list(t.getPrograms().values())[0]; phases = prog.getPhases()
            links = {}
            for in_lane, _o, idx in t.getConnections():
                links.setdefault(idx, in_lane.getID())
            greens = [i for i, p in enumerate(phases) if ('G' in p.state or 'g' in p.state) and 'y' not in p.state.lower()]
            if len(greens) < 2:
                continue
            serve = [sorted({links[k] for k, c in enumerate(phases[i].state) if c in 'Gg' and k in links}) for i in greens[:2]]
            lanes = sorted({l for s in serve for l in s})
            self.tls[t.getID()] = dict(greens=greens[:2], n_phases=len(phases), serve=serve, lanes=lanes)


class LightRL:
    """Keep / switch controller for every light; `policy(obs batch) -> actions` (0 keep, 1 switch); records transitions."""

    def __init__(self, info: NetInfo, policy, max_g=None, record=False):
        self.info, self.policy, self.max_g, self.record = info, policy, max_g, record
        self.prev = {}; self.trans = []; self.ids = list(info.tls)

    def obs(self, tid):
        d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
        h = [sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve']]
        n = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve']]
        cur = d['greens'].index(ph) if ph in d['greens'] else -1
        return np.array([h[0] / 10, h[1] / 10, n[0] / 20, n[1] / 20, cur == 0, cur == 1, ls.trafficlight.getSpentDuration(tid) / 60],
                        np.float32), sum(h), cur

    def step(self, t):
        if int(t) % DT_L:
            return
        todo, O, R = [], [], []
        for tid in self.ids:
            o, halt, cur = self.obs(tid)
            if cur < 0:                                       # in yellow: no decision
                continue
            spent = ls.trafficlight.getSpentDuration(tid)
            if spent < MIN_G:
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            todo.append((tid, cur, spent)); O.append(o); R.append(-halt / 10)
        if not todo:
            return
        A = np.asarray(self.policy(np.stack(O)))
        for (tid, cur, spent), o, r, a in zip(todo, O, R, A):
            if self.max_g is not None and spent >= self.max_g:
                a = 1                                         # compatible mode: forced switch at the training range's edge
            if self.record:
                if tid in self.prev:
                    po, pa = self.prev[tid]; self.trans.append((po, pa, r, o, 0.0))
                self.prev[tid] = (o, int(a))
            if a == 1:
                d = self.info.tls[tid]; ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
            else:
                ls.trafficlight.setPhaseDuration(tid, 1e5)


class CarRL:
    """Agent cars: speed choice inside the approach zone; `policy(obs batch) -> action indices`."""

    def __init__(self, policy, rho, seed, record=False):
        self.policy, self.rho, self.seed, self.record = policy, rho, seed, record
        self.agents, self.state, self.trans = set(), {}, []
        self.oos_log = []                                     # (green, time in phase) at every agent decision

    def is_agent(self, vid):
        return _stable_u(self.seed, vid) < self.rho

    def step(self, t):
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v); ls.vehicle.setColor(v, (210, 168, 255, 255))
        for v in ls.simulation.getArrivedIDList():
            if v in self.agents:
                self._end(v); self.agents.discard(v)
        ids, O, meta = [], [], []
        for v in list(self.agents):
            try:                                              # a teleporting vehicle is temporarily off the network
                nt = ls.vehicle.getNextTLS(v)
                if not nt:
                    self._end(v); continue
                tid, _li, dist, st = nt[0]
                if dist > ZONE:
                    self._end(v); continue
                prev = self.state.get(v)
                if prev is not None and prev[3] != tid:       # passed the previous stop line: that approach is over
                    self._end(v); prev = None
                sp = ls.vehicle.getSpeed(v); lead = ls.vehicle.getLeader(v, 100.0)
            except Exception:
                continue
            gap = (lead[1] / 100.0) if lead else 1.0
            o = np.array([dist / ZONE, sp / 14.0, st in 'Gg', st in 'yY', ls.trafficlight.getSpentDuration(tid) / 60.0, gap], np.float32)
            ids.append(v); O.append(o); meta.append((tid, sp))
        if not ids:
            return
        A = np.asarray(self.policy(np.stack(O)))
        for v, o, (tid, sp), a in zip(ids, O, meta, A):
            prev = self.state.get(v)
            if self.record and prev is not None:
                po, pa, pc, _ = prev; self.trans.append((po, pa, -pc, o, 0.0))
            try:
                vmax = ls.vehicle.getAllowedSpeed(v); nv = float(min(max(sp + ACC[a], 0.0), vmax)); ls.vehicle.setSpeed(v, nv)
            except Exception:
                continue
            cost = 1.0 + 0.05 * ACC[a] ** 2 + IDLE * (nv < 0.1)
            self.state[v] = (o, int(a), cost, tid); self.oos_log.append((o[2], o[4] * 60.0))

    def _end(self, v):
        prev = self.state.pop(v, None)
        if prev is not None:
            try:
                ls.vehicle.setSpeed(v, -1)                    # hand the car back to SUMO's driver model
            except Exception:
                pass                                          # already arrived
            if self.record:
                po, pa, pc, _ = prev; self.trans.append((po, pa, -pc, po, 1.0))


def _stable_u(seed, vid):
    """Deterministic U[0,1) from (seed, vehicle id), independent of Python's hash randomisation."""
    h = 2166136261
    for ch in f'{seed}:{vid}'.encode():
        h = ((h ^ ch) * 16777619) & 0xFFFFFFFF
    return h / 2 ** 32


def run_episode(net_file, route_file, seed, light=None, cars=None, end=3600, tripinfo=None, extra=()):
    """One SUMO run.  light: None (net program) or a LightRL; cars: None (all human) or a CarRL.  Returns summary metrics."""
    cmd = [sumolib.checkBinary('sumo'), '-n', net_file, '-r', route_file, '--seed', str(seed), '--no-step-log', '--no-warnings',
           '--time-to-teleport', '300', '--step-length', '1', '--device.emissions.probability', '1', *extra]
    if tripinfo:
        cmd += ['--tripinfo-output', tripinfo, '--tripinfo-output.write-unfinished']
    ls.start(cmd); teleports = 0
    try:
        while ls.simulation.getTime() < end and (ls.simulation.getMinExpectedNumber() > 0 or ls.simulation.getTime() < 10):
            ls.simulationStep(); t = ls.simulation.getTime(); teleports += ls.simulation.getStartingTeleportNumber()
            if light is not None:
                light.step(t)
            if cars is not None:
                cars.step(t)
    finally:
        ls.close()
    return dict(teleports=teleports)


def read_tripinfo(path, agents=None):
    """Per-vehicle duration, waiting time, time loss, fuel (mg) and whether it finished; split by agent / human."""
    rows = []
    for ti in sumolib.xml.parse(path, 'tripinfo'):
        em = ti.emissions[0] if ti.hasChild('emissions') else None
        rows.append(dict(id=ti.id, duration=float(ti.duration), waiting=float(ti.waitingTime), timeloss=float(ti.timeLoss),
                         fuel=float(em.fuel_abs) if em is not None else math.nan, finished=float(ti.arrival) >= 0 if ti.arrival else False,
                         agent=(ti.id in agents) if agents is not None else False))
    return rows


def make_controllers(_ls, net_file, signals, vehicles, seed):
    """Hook for scripts/CITY_live_viewer.py: 'rl:<ckpt>' / 'rlcompat:<ckpt>:<maxg>' lights, 'cav:<ckpt>:<rho>' cars."""
    import torch
    torch.set_grad_enabled(False)                                 # inference only in the viewer
    out = []
    if signals.startswith('rl'):
        parts = signals.split(':'); net = torch.load(parts[1], weights_only=False)['net']; net.eval()
        maxg = float(parts[2]) if parts[0] == 'rlcompat' else None
        out.append(LightRL(NetInfo(net_file), lambda O, n=net: n(torch.as_tensor(O)).argmax(1).numpy(), max_g=maxg))   # bind n now (was late-bound)
    if vehicles.startswith('cav'):
        parts = vehicles.split(':'); net = torch.load(parts[1], weights_only=False)['net']; net.eval()
        out.append(CarRL(lambda O, n=net: n(torch.as_tensor(O)).argmax(1).numpy(), float(parts[2]), seed))
    return out
