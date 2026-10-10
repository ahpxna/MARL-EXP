#!/usr/bin/env python3
"""Unified two-population evaluator, VERSION 4 (04/10/2026 05:4x, wake 4): CITY_eval3.py plus fleets whose checkpoint declares
`actions` = release (ACC + release-to-SUMO) or residual (delta added to SUMO's own next speed): scripts/CITY_fleet_train_v4.py, the B6
policy-class diagnostic.  Fleets without the field behave exactly as in eval3.
(eval3) Unified two-population evaluator, VERSION 3 (04/10/2026 05:1x, wake 3): CITY_eval2.py plus the user's pre-launch audit
(Documents/.../TWO_POPULATION_PROGRAM_PRELAUNCH_AUDIT_20261004.md, Addendum W-A..W-E): per-window COUNT and SUM of time loss (agent / human),
cohorts at the reference time (departing after it; present on the road at it), optional system delay increments over time (--delay-trace),
guards `always` (always released: the always-SUMO baseline) and `random:P` (released at random with probability P: matched-rate control),
per-second phase AND spentDuration trace plus an action digest (for the replay trace check), censored start-ups counted, teleport exits
separated from crossings, and a phase / spent / remaining-time trace around a hot swap.
CITY_eval2.py is kept unchanged (smoke version).  Original header follows.
(eval2) Unified two-population evaluator (04/10/2026 wake 3; program research/papers/audits/TWO_POPULATION_EXPERIMENT_PROGRAM_20261004.md).
One (light, fleet) configuration over evaluation seeds per call.  Run with PYTHONHASHSEED=0 (and OMP_NUM_THREADS=1).
LIGHT  --light  ACT | FT | ACTP | MP | RL-H:t | RL-J:t | RL-C50:t | <ARM>:k
         ACTP  grid4.net.xml + research/city_sim/net/grid4_act_program.add.xml, the actuated program "act" loaded last, hence active
               (ACT on the static net, so that a learned light can take over mid-run; SELF-CHECK: = ACT on grid4_actuated.net.xml)
         MP    max pressure (Varaiya 2013, as in RESCO / sumo-rl): every 5 s after min green, keep or switch to the green phase with the
               larger sum over its green links of (vehicles on the incoming lane - vehicles on the outgoing lane)
       --light-obs  raw | q:A:B | norm:FILE | affine:FILE   input adapter in front of a FROZEN learned light (its two halting features):
               q: halting (v<0.1) + A*count(0.1<=v<2) + B*count(2<=v<5) on the same served lanes (raw = q:0:0); norm: per-feature moment
               matching o' = (o - mu1)/sd1*sd0 + mu0 (FILE json mu0 sd0 mu1 sd1, 7 each); affine: o' = o*exp(s) + b (FILE json s b, 7 each;
               the DC-Ada-style transform tuned by CITY_dcada_tune.py)
       --light-fallback none | box:FILE   when the (adapted) observation leaves the light's training box (FILE json lo hi, 7 each), the
               decision is taken by a rule instead of the policy: switch iff the other green serves more vehicles or spent >= 50 s
FLEET  --fleet  human | L-ACT:t | L-FT:t | L-RLH:t | <ARM>:k | U:<name> (research/city_sim/fleet_upgrade_20261004/<name>_fleet.pt)
       --guard  none | fallback | clip | green | green+oos | discharge:D    (none issues exactly CarRL's calls)
OPEN LOOP  --record FILE  saves every light's phase each second;  --replay FILE  replays it (all lights forced, no controller; net NET_S)
HANDOFF    --swap-at T [--swap-light SPEC] [--swap-fleet SPEC]   replaces the light and/or fleet policy at time T, keeping the physical
           state, phase timers and approach states
METRICS  city / agent / human time loss, fuel (mg per trip), waiting, unfinished, teleports; mean halting on served lanes every 5 s (the
         light reward's quantity); green durations; with --discharge: vehicles leaving served incoming lanes during green (agent / human)
         per green second and start-up delay after green onset when vehicles were waiting."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, tempfile, time
import sumolib
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode, read_tripinfo, ACC, ZONE, IDLE, DT_L, MIN_G  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); RES_DELTA = np.array([-3.0, -2.0, -1.0, 0.0, 1.0]); FINE_ACC = np.array([-1.5, -1.0, -0.5, 0.0, 0.5, 1.0])
ACT_ADD = str(ROOT / 'research/city_sim/net/grid4_act_program.add.xml'); FU = ROOT / 'research/city_sim/fleet_upgrade_20261004'


# ----------------------------------------------------------------------------------------------------------------------------- lights
class LightRLX(LightRL):
    """LightRL with an optional input adapter and an optional out-of-box rule fallback (counted)."""

    def __init__(self, info, policy, max_g=None, adapter='raw', box=None):
        self.adapter = adapter; self.box = box; self.fb = 0; self.dec = 0; self.inner = policy
        kind = adapter.split(':')[0]
        if kind == 'q':
            self.qa, self.qb = float(adapter.split(':')[1]), float(adapter.split(':')[2])
        elif kind in ('norm', 'affine'):
            self.par = {k: np.asarray(v, np.float32) for k, v in json.loads(Path(adapter.split(':', 1)[1]).read_text()).items()}
        super().__init__(info, self._policy, max_g=max_g)

    def _policy(self, O):
        a = np.asarray(self.inner(O)); self.dec += len(O)
        if self.box is not None:
            out = ((O < self.box[0] - 1e-6) | (O > self.box[1] + 1e-6)).any(1)
            if out.any():
                n_cur = np.where(O[:, 4] > 0.5, O[:, 2], O[:, 3]); n_oth = np.where(O[:, 4] > 0.5, O[:, 3], O[:, 2])
                rule = ((n_oth > n_cur) | (O[:, 6] * 60.0 >= 50.0)).astype(a.dtype)
                a = np.where(out, rule, a); self.fb += int(out.sum())
        return a

    def obs(self, tid):
        o, halt, cur = super().obs(tid)
        kind = self.adapter.split(':')[0]
        if kind == 'q' and (self.qa or self.qb):
            ls = CE.ls; d = self.info.tls[tid]; q = []
            for s in d['serve']:
                h = m1 = m2 = 0
                for l in s:
                    for v in ls.lane.getLastStepVehicleIDs(l):
                        sp = ls.vehicle.getSpeed(v); h += sp < 0.1; m1 += 0.1 <= sp < 2.0; m2 += 2.0 <= sp < 5.0
                q.append(h + self.qa * m1 + self.qb * m2)
            o = o.copy(); o[0], o[1] = q[0] / 10, q[1] / 10
        elif kind == 'norm':
            P = self.par; sd1 = np.where(P['sd1'] > 1e-9, P['sd1'], 1.0); o = np.where(P['sd1'] > 1e-9, (o - P['mu1']) / sd1 * P['sd0'] + P['mu0'], o).astype(np.float32)
        elif kind == 'affine':
            o = (o * np.exp(self.par['s']) + self.par['b']).astype(np.float32)
        return o, halt, cur


class MaxPressure:
    def __init__(self, info):
        self.info = info; self.links = {}; self.states = {}

    def step(self, t):
        if int(t) % DT_L:
            return
        ls = CE.ls
        for tid, d in self.info.tls.items():
            ph = ls.trafficlight.getPhase(tid)
            if ph not in d['greens']:
                continue
            cur = d['greens'].index(ph); spent = ls.trafficlight.getSpentDuration(tid)
            if spent < MIN_G:
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            if tid not in self.links:
                self.links[tid] = ls.trafficlight.getControlledLinks(tid)
                self.states[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
            pr = []
            for g in d['greens']:
                st = self.states[tid][g]; p = 0
                for k, lk in enumerate(self.links[tid]):
                    if k < len(st) and st[k] in 'Gg' and lk:
                        i, o_, _ = lk[0]; p += ls.lane.getLastStepVehicleNumber(i) - ls.lane.getLastStepVehicleNumber(o_)
                pr.append(p)
            if pr[1 - cur] > pr[cur]:
                ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
            else:
                ls.trafficlight.setPhaseDuration(tid, 1e5)


class Replay:
    """Open-loop replay of recorded phases.  Only the light's own decisions are forced (green -> yellow, or any mismatch); yellows advance
    on the program's timer inside the simulation step exactly as when recorded, and greens are held (duration 1e5) as LightRL holds them.
    SELF-CHECK in the protocols: replaying a run with the same fleet reproduces it."""

    def __init__(self, rec, info):
        self.ids = list(rec['ids']); self.P = rec['phases']; self.greens = {tid: set(d['greens']) for tid, d in info.tls.items()}

    def step(self, t):
        ls = CE.ls; k = min(max(int(t) - 1, 0), len(self.P) - 1)        # P[i] = the phase logged at time i + 1, after that second's light action
        for j, tid in enumerate(self.ids):
            p = int(self.P[k][j])
            if ls.trafficlight.getPhase(tid) != p:
                ls.trafficlight.setPhase(tid, p)
            if p in self.greens.get(tid, ()):
                ls.trafficlight.setPhaseDuration(tid, 1e5)


def build_light(spec, info, adapter, box):
    """-> (net, controller or None, extra sumo args, init hook)"""
    if spec == 'ACTP':                                          # the program loaded last ("act", from the additional file) is active
        return Q7.NET_S, None, ['-a', ACT_ADD], None
    if spec == 'MP':
        return Q7.NET_S, MaxPressure(info), [], None
    net, lck, mg = X2.light_spec(spec)
    if lck is None:
        return net, None, [], None
    return net, LightRLX(info, Q7.load_policy(lck), max_g=mg, adapter=adapter, box=box), [], None


# ----------------------------------------------------------------------------------------------------------------------------- fleets
def fleet_path(spec):
    if spec.startswith('U:'):
        return FU / f'{spec[2:]}_fleet.pt'
    return X2.fleet_ckpt(spec)


class CarRLG(CarRL):
    """CarRL.step plus a per-decision guard verdict: None (act), 'release' (SUMO drives this second), 'clip' (tau clipped to support)."""

    def __init__(self, policy, rho, seed, tm, guard, record=True):
        super().__init__(policy, rho, seed, record); self.tm, self.guard = tm, guard; self.fired = 0; self.decisions = 0
        self.D = float(guard.split(':')[1]) if guard.startswith('discharge') else None
        self.P = float(guard.split(':')[1]) if guard.startswith('random') else None; self.rng = np.random.default_rng(seed + 7919)
        self.digest = hashlib.sha256(); self.actions = 'acc'

    def verdict(self, o):
        g = self.guard; tau = o[4] * 60.0; green = o[2] > 0.5; lim = self.tm[1] if green else self.tm[0]
        if g == 'none':
            return None
        if g == 'always':
            return 'release'
        if self.P is not None:
            return 'release' if self.rng.random() < self.P else None
        if g in ('fallback', 'clip'):
            return (('release' if g == 'fallback' else 'clip') if tau > lim else None)
        if g == 'green':
            return 'release' if green else None
        if g == 'green+oos':
            return 'release' if (green or tau > lim) else None
        if self.D is not None:
            return 'release' if (green and o[0] * ZONE <= self.D) else None
        raise ValueError(g)

    def step(self, t):
        ls = CE.ls
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v); ls.vehicle.setColor(v, (210, 168, 255, 255))
        for v in ls.simulation.getArrivedIDList():
            if v in self.agents:
                self._end(v); self.agents.discard(v)
        ids, O, meta, rel = [], [], [], []
        for v in list(self.agents):
            try:
                nt = ls.vehicle.getNextTLS(v)
                if not nt:
                    self._end(v); continue
                tid, _li, dist, st = nt[0]
                if dist > ZONE:
                    self._end(v); continue
                prev = self.state.get(v)
                if prev is not None and prev[3] != tid:
                    self._end(v); prev = None
                sp = ls.vehicle.getSpeed(v); lead = ls.vehicle.getLeader(v, 100.0)
            except Exception:
                continue
            gap = (lead[1] / 100.0) if lead else 1.0
            o = np.array([dist / ZONE, sp / 14.0, st in 'Gg', st in 'yY', ls.trafficlight.getSpentDuration(tid) / 60.0, gap], np.float32)
            self.decisions += 1; vd = self.verdict(o)
            if vd is not None:
                self.fired += 1
                if vd == 'release':
                    rel.append((v, o, tid, sp)); continue
                o = o.copy(); o[4] = np.float32((self.tm[1] if o[2] > 0.5 else self.tm[0]) / 60.0)
            ids.append(v); O.append(o); meta.append((tid, sp))
        for v, o, tid, sp in rel:
            prev = self.state.get(v)
            if self.record and prev is not None:
                po, pa, pc, _ = prev; self.trans.append((po, pa, -pc, o, 0.0))
            try:
                ls.vehicle.setSpeed(v, -1)
            except Exception:
                continue
            self.state[v] = (o, -1, 1.0 + IDLE * (sp < 0.1), tid); self.oos_log.append((o[2], o[4] * 60.0))
        if not ids:
            if rel:
                self.digest.update(f'{t}|R|{sorted(v for v, *_ in rel)}'.encode())
            return
        A = np.asarray(self.policy(np.stack(O)))
        self.digest.update(f'{t}|{sorted(zip(ids, (int(x) for x in A)))}|R|{sorted(v for v, *_ in rel)}'.encode())
        for v, o, (tid, sp), a in zip(ids, O, meta, A):
            prev = self.state.get(v)
            if self.record and prev is not None:
                po, pa, pc, _ = prev; self.trans.append((po, pa, -pc, o, 0.0))
            try:
                vmax = ls.vehicle.getAllowedSpeed(v)
                if self.actions == 'release' and a == len(ACC):
                    ls.vehicle.setSpeed(v, -1); nv = sp; self.fired += 1; acc_ = 0.0
                elif self.actions == 'residual':
                    nv = float(min(max(ls.vehicle.getSpeedWithoutTraCI(v) + RES_DELTA[a], 0.0), vmax)); ls.vehicle.setSpeed(v, nv); acc_ = nv - sp
                elif self.actions == 'fine':
                    nv = float(min(max(sp + FINE_ACC[a], 0.0), vmax)); ls.vehicle.setSpeed(v, nv); acc_ = FINE_ACC[a]
                else:
                    nv = float(min(max(sp + ACC[a], 0.0), vmax)); ls.vehicle.setSpeed(v, nv); acc_ = ACC[a]
            except Exception:
                continue
            cost = 1.0 + 0.05 * acc_ ** 2 + IDLE * (nv < 0.1)
            self.state[v] = (o, int(a), cost, tid); self.oos_log.append((o[2], o[4] * 60.0))


def load_fleet(spec, seed, guard):
    p = fleet_path(spec); d = torch.load(p, weights_only=False); tm = d.get('tmax_late') or d['tmax']
    c = CarRLG(Q7.load_policy(p), Q7.RHO, seed, tm, guard); c.actions = d.get('actions', 'acc')
    return c, p


# ----------------------------------------------------------------------------------------------------------------------------- logger
class Logger:
    def __init__(self, info, cars, record, discharge, delay_trace=False):
        self.info, self.cars, self.discharge = info, cars, discharge; self.rec = [] if record else None; self.spent = [] if record else None
        self.halt = []; self.green_start = {}; self.green_durs = []; self.prev_on = {}; self.cross = {'a': 0, 'h': 0}; self.green_sec = 0
        self.wait_at_onset = {}; self.first_cross = {}; self.startup = []; self.ids = None; self.censored = 0; self.tele_exit = 0
        self.delay_trace = delay_trace; self.delay = {}

    def step(self, t):
        ls = CE.ls
        if self.rec is not None:
            if self.ids is None:
                self.ids = list(ls.trafficlight.getIDList())
            self.rec.append([ls.trafficlight.getPhase(tid) for tid in self.ids]); self.spent.append([ls.trafficlight.getSpentDuration(tid) for tid in self.ids])
        if self.delay_trace:                                        # time-loss increment of every vehicle present during this second
            w = str(int((t - 1) // 900) * 900); acc = self.delay.setdefault(w, [0.0, 0.0])
            for v in ls.vehicle.getIDList():
                vm = ls.vehicle.getAllowedSpeed(v); dl = max(0.0, 1.0 - ls.vehicle.getSpeed(v) / vm) if vm > 0 else 1.0
                acc[0 if (self.cars is not None and self.cars.is_agent(v)) else 1] += dl
        for tid, d in self.info.tls.items():
            ph = ls.trafficlight.getPhase(tid); g = ph in d['greens']
            if g and tid not in self.green_start:
                self.green_start[tid] = t
                if self.discharge:
                    s = d['serve'][d['greens'].index(ph)]
                    self.wait_at_onset[tid] = sum(ls.lane.getLastStepHaltingNumber(l) for l in s); self.first_cross.pop(tid, None)
            elif not g and tid in self.green_start:
                self.green_durs.append(t - self.green_start.pop(tid))
                if self.discharge and self.wait_at_onset.get(tid, 0) > 0:
                    if tid in self.first_cross:
                        self.startup.append(self.first_cross[tid])
                    else:
                        self.censored += 1                          # a queued green that discharged nobody: censored start-up
            if self.discharge and g:
                self.green_sec += 1; s = d['serve'][d['greens'].index(ph)]
                on = {v for l in s for v in ls.lane.getLastStepVehicleIDs(l)}; prev = self.prev_on.get((tid, ph), set())
                for v in prev - on:
                    try:
                        ln = ls.vehicle.getLaneID(v)
                    except Exception:
                        continue                                    # arrived (left the network)
                    if ln in s:
                        continue
                    if ln == '':
                        self.tele_exit += 1; continue               # teleporting, not a crossing
                    self.cross['a' if (self.cars is not None and self.cars.is_agent(v)) else 'h'] += 1
                    if tid not in self.first_cross and tid in self.green_start:
                        self.first_cross[tid] = t - self.green_start[tid]
                self.prev_on[(tid, ph)] = on
            elif self.discharge:
                self.prev_on = {k: v for k, v in self.prev_on.items() if k[0] != tid}
        if int(t) % DT_L == 0:
            self.halt.append(sum(ls.lane.getLastStepHaltingNumber(l) for d in self.info.tls.values() for s in d['serve'] for l in s))


# ----------------------------------------------------------------------------------------------------------------------------- run
def run(a, seed, end):
    info = NetInfo(Q7.NET_S); box = None
    if a.light_fallback.startswith('box:'):
        B = json.loads(Path(a.light_fallback[4:]).read_text()); box = (np.asarray(B['lo'], np.float32), np.asarray(B['hi'], np.float32))
    if a.replay:
        rec = np.load(a.replay, allow_pickle=True); light, net, extra, init = Replay(rec, info), Q7.NET_S, [], None
    else:
        net, light, extra, init = build_light(a.light, info, a.light_obs, box)
    cars = None; fp = None
    if a.fleet != 'human':
        cars, fp = load_fleet(a.fleet, seed, a.guard)
    log = Logger(info, cars, bool(a.record), a.discharge, a.delay_trace)
    state = dict(light=light, cars=cars, swapped=False)

    class Multi:
        def step(self, t):
            if init is not None and not state.get('init'):
                init(); state['init'] = True
            if a.swap_at is not None and not state['swapped'] and t >= a.swap_at:
                state['swapped'] = True
                if a.swap_light:
                    _, nl, _, _ = build_light(a.swap_light, info, a.light_obs, box); state['light'] = nl
                    if a.light == 'ACTP':                           # PHASE-BOUNDARY handoff (setProgram resets phase / timer: swap trace 05:2x)
                        nl.ids = []; state['pending'] = set(CE.ls.trafficlight.getIDList()); state['swap_log'] = []
                if a.swap_fleet and state['cars'] is not None:
                    p = fleet_path(a.swap_fleet); d = torch.load(p, weights_only=False)
                    state['cars'].policy = Q7.load_policy(p); state['cars'].tm = d.get('tmax_late') or d['tmax']
            if state.get('pending'):                              # switch each light just before its own next phase change
                for tid in sorted(state['pending']):
                    ls_ = CE.ls; ph = ls_.trafficlight.getPhase(tid)
                    if ls_.trafficlight.getNextSwitch(tid) - t <= 1.0 + 1e-9:
                        n = len(ls_.trafficlight.getAllProgramLogics(tid)[0].phases); nxt = (ph + 1) % n
                        ls_.trafficlight.setProgram(tid, '0'); ls_.trafficlight.setPhase(tid, nxt)
                        state['swap_log'].append((t, tid, nxt, ls_.trafficlight.getPhase(tid), ls_.trafficlight.getSpentDuration(tid)))
                        state['pending'].discard(tid)
                        if tid in info.tls:
                            state['light'].ids.append(tid)
            for c in (state['light'], state['cars'], log):
                if c is not None:
                    c.step(t)
    fd, ti = tempfile.mkstemp(suffix='.xml', prefix='eval2_', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
    m = run_episode(net, Q7.ROU.format(seed), seed, Multi(), None, end=end, tripinfo=str(ti), extra=tuple(extra))
    rows = read_tripinfo(ti)
    da = {x.id: (float(x.depart), float(x.arrival)) for x in sumolib.xml.parse(str(ti), 'tripinfo')}; os.remove(ti)
    isa0 = (lambda v: cars.is_agent(v)) if cars is not None else (lambda v: False)
    win = {}; Tref = a.swap_at if a.swap_at is not None else 1800.0
    coh = {k: [0, 0.0, 0, 0.0] for k in ('after', 'present')}       # [n_agent, sum_agent, n_human, sum_human]
    for r in rows:                                                  # COUNT and SUM of time loss per departure window (agent / human)
        dep, arr = da.get(r['id'], (0.0, -1.0)); g = 0 if isa0(r['id']) else 2
        w = win.setdefault(str(int(dep // 900) * 900), [0, 0.0, 0, 0.0]); w[g] += 1; w[g + 1] += r['timeloss']
        k = 'after' if dep >= Tref else ('present' if (arr < 0 or arr >= Tref) else None)
        if k:
            coh[k][g] += 1; coh[k][g + 1] += r['timeloss']
    isa = (lambda v: cars.is_agent(v)) if cars is not None else (lambda v: False)
    ag = [r for r in rows if isa(r['id'])]; hu = [r for r in rows if not isa(r['id'])]
    mean = lambda xs, k: float(np.nanmean([x[k] for x in xs])) if xs else float('nan')
    L = state['light']; gd = np.array(log.green_durs) if log.green_durs else np.zeros(1)
    out = dict(light=a.light, light_obs=a.light_obs, light_fallback=a.light_fallback, fleet=a.fleet, guard=a.guard, swap=[a.swap_at, a.swap_light, a.swap_fleet],
               replay=a.replay, seed=seed, timeloss=mean(rows, 'timeloss'), timeloss_agent=mean(ag, 'timeloss'), timeloss_human=mean(hu, 'timeloss'),
               fuel=mean(rows, 'fuel'), fuel_agent=mean(ag, 'fuel'), fuel_human=mean(hu, 'fuel'), waiting=mean(rows, 'waiting'), n=len(rows),
               unfinished=int(sum(not r['finished'] for r in rows)), teleports=m['teleports'], mean_halting=float(np.mean(log.halt)) if log.halt else float('nan'),
               green_mean=float(gd.mean()), green_p90=float(np.percentile(gd, 90)), green_share_gt50=float((gd > 50).mean()),
               light_fallback_share=(L.fb / max(1, L.dec)) if isinstance(L, LightRLX) else None,
               guard_share=(cars.fired / max(1, cars.decisions)) if cars is not None else None,
               window_counts_sums=win, ref_time=Tref, cohort_counts_sums=coh, delay_by_window=log.delay if a.delay_trace else None,
               action_digest=cars.digest.hexdigest() if cars is not None else None,
               swap_trace=(dict(n=len(state['swap_log']), phase_kept=sum(x[2] == x[3] for x in state['swap_log']), spent_zero=sum(x[4] == 0.0 for x in state['swap_log']),
                                last_switch=max((x[0] for x in state['swap_log']), default=None), never_switched=len(state.get('pending') or ())) if 'swap_log' in state else None))
    if a.discharge:
        out.update(cross_agent=log.cross['a'], cross_human=log.cross['h'], green_seconds=log.green_sec,
                   per_green_second=(log.cross['a'] + log.cross['h']) / max(1, log.green_sec),
                   startup_mean=float(np.mean(log.startup)) if log.startup else float('nan'), startup_n=len(log.startup), startup_censored=log.censored,
                   teleport_exits=log.tele_exit)
    if a.record:
        rp = Path(a.record.replace('{seed}', str(seed))); rp.parent.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(rp, ids=np.array(log.ids), phases=np.array(log.rec, np.int16), spent=np.array(log.spent, np.float64))
    return out


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    tag = a.tag or '_'.join(x for x in [a.light, a.light_obs if a.light_obs != 'raw' else '', Path(a.light_fallback).stem if a.light_fallback != 'none' else '',
                                         a.fleet, a.guard if a.guard != 'none' else '', f'swap{a.swap_at}' if a.swap_at is not None else ''] if x)
    tag = tag.replace(':', '-').replace('+', 'P').replace('/', '_')
    fn = out / f'{tag}.json'
    if fn.exists() and json.loads(fn.read_text()).get('status') == 'COMPLETE':
        print('skip', tag); return
    rows = []; t0 = time.perf_counter()
    for s in a.seeds:
        if a.replay_dir:
            a.replay = str(Path(a.replay_dir) / f'phases_s{s}.npz')
        r = run(a, s, 600 if a.smoke else 5400); rows.append(r)
        print(f"[{time.perf_counter() - t0:.0f}s] {tag} s{s}: TL {r['timeloss']:.2f} (agent {r['timeloss_agent']:.2f} human {r['timeloss_human']:.2f}) fuel {r['fuel']:.0f} "
              f"halt {r['mean_halting']:.1f} green {r['green_mean']:.1f}/{r['green_p90']:.0f} lfb {r['light_fallback_share']} guard {r['guard_share']} tele {r['teleports']}"
              + (f" cross/gs {r['per_green_second']:.3f} startup {r['startup_mean']:.2f}" if a.discharge else ''), flush=True)
    fn.write_text(json.dumps(dict(status='COMPLETE', rows=rows, args=vars(a), source_sha256=SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED'),
                                  env_sha256=hashlib.sha256((ROOT / 'scripts/CITY_env.py').read_bytes()).hexdigest()), indent=1, default=str))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    main(p.parse_args())
