#!/usr/bin/env python3
"""W20 (PROTOCOL_CITY_WAVE20_20261009): benchmark signal representations and the human-twin sensing layer (TSI-G).
Extends scripts/CITY_w19_obs.py in place (FAMS / DIM / family_obs / reward_quantity) with four families trained by the RL-H recipe (W19
trainer, DQN seed shared by slot), whose observation and training reward are re-implementations of the two most used SUMO RL libraries:
  SRL  84  sumo-rl default: green one-hot, min-green flag, per incoming lane density n/cap and queue h/cap (cap = length / 7.5 m) (19);
           reward diff-waiting-time (W_prev - W) / 100, W = sum of SUMO accumulated waiting times on the incoming lanes, between decisions
  RDQ  89  RESCO drq_norm (IDQN / IPPO state): per lane [served by the current green, approaching/28, wait/28, queued/28, avg-speed sum/20/28]
           (40); reward RESCO wait_norm clip(-total wait / 224, -4, 4)
  RMP  94  RESCO mplight (MPLight / MaxPressure state): [current green index, pressure per green = queued on its in-lanes - queued on its
           out-lanes that enter another signal] (3); reward RESCO pressure -(queued in - queued out)
  RWV  99  RESCO wave (threshold-free control): per green (queued + approaching)/28 = vehicles/28, green one-hot (4); reward wait_norm
RESCO semantics (traffic_signal.py): a vehicle is 'queued' from its first second below 0.1 m/s on the lane until it leaves the lane (sticky);
its wait grows by 1 s every second while queued; approaching = vehicles - queued.  The per-second Tracker reproduces this.
Deviation: drq's phase flag marks lanes served by the current green (RESCO flags lane index == phase index).
TSI-G (adapter 'bis'): every vehicle of the SPaT-following fleet (membership u(seed, id) < rho, known to the infrastructure by V2X) is
replaced, for sensing only, by a human twin (Tracker._twins): from its lane entry it follows the free trajectory at its allowed speed
(lane limit x speed factor) delayed by the braking time vf / (2 decel), one (length + minGap) behind the vehicle ahead; on red, after
reaching the queue tail it rolls CREEP s and halts; on green it starts tau after the queue member ahead started (tau after green onset if
none); a fleet vehicle that really halts is halted.  Driver parameters come from the vehicle type; CREEP is the one site parameter,
calibrated on all-human logs (scripts/CITY_w20_twin_calib.py) so that twins reproduce the human halting time.  Halting counts and RESCO
queued / wait / average speed are computed on the twin state; non-fleet vehicles are unchanged.  No reward-based search."""
import os
import numpy as np
import scripts.CITY_env as CE
import scripts.CITY_q7_cross_version as Q7
import scripts.CITY_w19_obs as W

NEWF = {'SRL': (84, 'SRL', 'DWT', 10), 'RDQ': (89, 'RDQ', 'WAITN', 10), 'RMP': (94, 'RMP', 'PRESS', 10), 'RWV': (99, 'RWV', 'WAITN', 10)}
W.FAMS.update(NEWF); W.DIM.update({'SRL': 19, 'RDQ': 40, 'RMP': 3, 'RWV': 4})
NEWK = ('SRL', 'RDQ', 'RMP', 'RWV'); VEH_SPACE = 7.5
CREEP = float(os.environ['W20_CREEP']) if os.environ.get('W20_CREEP') else None   # s a twin rolls at the tail; site calibration (CITY_w20_twin_calib.py)
FORCE_REAL = True  # a fleet vehicle that really halts is halted (deployment); False only for the pure-model calibration


class Tracker:
    def __init__(self):
        self.seed = None; self.bis = False; self.rho = Q7.RHO; self.need_acc = False; self.info = None; self.reset()

    def reset(self):
        self.t_last = -1.0; self.veh = {}; self.wlast = {}; self.bylane = {}

    def setup(self, info):
        if self.info is info:
            return
        ls = CE.ls; self.info = info; self.lmap = {}; self.len = {}; self.out = {}
        for tid, d in info.tls.items():
            for g, s in enumerate(d['serve']):
                for l in s:
                    self.lmap[l] = (tid, g); self.len[l] = ls.lane.getLength(l)
        for tid, d in info.tls.items():
            links = ls.trafficlight.getControlledLinks(tid); outs = [set(), set()]
            for lk in links:
                for i_l, o_l, _v in lk:
                    for g in (0, 1):
                        if i_l in d['serve'][g] and o_l in self.lmap:
                            outs[g].add(o_l)
            self.out[tid] = [sorted(o) for o in outs]
        self.lanes = sorted(self.lmap)

    def active(self):
        return W.obs_kind() in NEWK or self.bis or self.need_acc

    def update(self, info, t):
        if not self.active() or t == self.t_last:
            return
        if t < self.t_last:
            self.reset()
        self.setup(info); ls = CE.ls; dt = (t - self.t_last) if self.t_last >= 0 else 1.0; self.t_last = t; seen = set(); self.bylane = {}
        green = {tid: ls.trafficlight.getPhase(tid) for tid in info.tls}
        for l in self.lanes:
            tid, g = self.lmap[l]; gr = green[tid] == info.tls[tid]['greens'][g]; recs = []
            for v in ls.lane.getLastStepVehicleIDs(l):
                sp = ls.vehicle.getSpeed(v); x = ls.vehicle.getLanePosition(v); r = self.veh.get(v)
                if r is None or r['lane'] != l:
                    r = dict(lane=l, t_in=t, x_in=x, q=False, w=0.0, vs=0.0, n=0, fleet=(self.bis and self.seed is not None and CE._stable_u(self.seed, v) < self.rho),
                             vf=ls.vehicle.getAllowedSpeed(v), sp_gap=ls.vehicle.getLength(v) + ls.vehicle.getMinGap(v),
                             td=ls.vehicle.getAllowedSpeed(v) / (2 * ls.vehicle.getDecel(v)), tau=ls.vehicle.getTau(v), hend=None, wash=False,
                             tw=dict(s='free', q=False, w=0.0, vs=0.0, v=0.0, tg=None, rank=0, ah=0.0))
                    self.veh[v] = r
                seen.add(v); r['v'] = sp; r['x'] = x; r['n'] += 1; r['vs'] += sp
                if sp < 0.1:
                    r['q'] = True; r['wash'] = True
                elif r['wash']:
                    r['wash'] = False; r['hend'] = t
                if r['q']:
                    r['w'] += dt
                if self.need_acc:
                    r['acc'] = ls.vehicle.getAccumulatedWaitingTime(v)
                recs.append(r)
            self.bylane[l] = recs
            if self.bis:
                self._twins(l, sorted(recs, key=lambda r: -r['x']), gr, t, dt)
        for v in [v for v in self.veh if v not in seen]:
            del self.veh[v]

    def _twins(self, l, recs, gr, t, dt):
        """Front to back.  A twin follows its free trajectory delayed by the braking time vf / (2 decel) and stays one (length + minGap)
        behind the vehicle ahead (real, or that vehicle's twin); on red it halts on reaching the queue tail; on green it starts tau after
        the queue member ahead started (or tau after green onset if none); a fleet vehicle that really halts is halted."""
        assert CREEP is not None, 'TSI-G needs the calibrated CREEP (env W20_CREEP)'
        L = self.len[l]; occ = 0.0; ahead_x = None; ahead_h = False; ahead_start = None
        for r in recs:
            tw = r['tw']
            if not r['fleet']:
                h = r['v'] < 0.1; x = r['x']
                if h:
                    occ += r['sp_gap']
            else:
                x_free = min(L, r['x_in'] + r['vf'] * max(0.0, t - r['t_in'] - r['td']))
                x = x_free if ahead_x is None else min(x_free, ahead_x - r['sp_gap'])
                if FORCE_REAL and r['v'] < 0.1:
                    if tw['s'] != 'halt':
                        tw['s'] = 'halt'
                elif tw['s'] == 'free':
                    if not gr and x >= L - occ - r['sp_gap']:
                        if tw.get('treach') is None:
                            tw['treach'] = t
                        if t >= tw['treach'] + CREEP:
                            tw['s'] = 'halt'
                    else:
                        tw['treach'] = None
                if tw['s'] == 'halt' and gr and (r['v'] >= 0.1 or not FORCE_REAL):
                    t0 = (tw['tg'] if ahead_start is None else ahead_start) if not ahead_h else None
                    if tw['tg'] is None:
                        tw['tg'] = t
                    if t0 is not None and t >= max(t0, tw['tg']) + r['tau']:
                        tw['s'] = 'rel'; tw['hend'] = t
                if not gr:
                    tw['tg'] = None
                h = tw['s'] == 'halt'
                if h:
                    occ += r['sp_gap']; tw['q'] = True; tw['ah'] += dt
                    x = L - occ + r['sp_gap']
                tw['v'] = 0.0 if h else r['vf']; tw['vs'] += tw['v']
                if tw['q']:
                    tw['w'] += dt
            ahead_x = x; ahead_h = h
            ahead_start = (tw.get('hend') if r['fleet'] else r.get('hend')) if not h else None

    # ------------------------------------------------------------------ per-vehicle views (real, or the twin for fleet vehicles under TSI-G)
    def lane_view(self, l):
        out = []
        for r in self.bylane.get(l, ()):
            if r['fleet']:
                tw = r['tw']; out.append((tw['s'] == 'halt', tw['q'], tw['w'], tw['vs'] / max(1, r['n']), r.get('acc', 0.0)))
            else:
                out.append((r['v'] < 0.1, r['q'], r['w'], r['vs'] / max(1, r['n']), r.get('acc', 0.0)))
        return out


TRACK = Tracker()


def _lane_stats(l):
    V = TRACK.lane_view(l); n = len(V)
    return dict(n=n, h=sum(v[0] for v in V), q=sum(v[1] for v in V), w=sum(v[2] for v in V), s=sum(v[3] for v in V), acc=sum(v[4] for v in V))


_PREV_FAMILY_OBS = W.family_obs


def family_obs(self, tid):
    k = W.obs_kind(); ls = CE.ls
    if k not in NEWK and not (TRACK.bis and k == 'A'):
        return _PREV_FAMILY_OBS(self, tid)
    TRACK.update(self.info, ls.simulation.getTime())
    d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid); cur = d['greens'].index(ph) if ph in d['greens'] else -1
    spent = ls.trafficlight.getSpentDuration(tid); lanes = list(d['serve'][0]) + list(d['serve'][1]); S = {l: _lane_stats(l) for l in lanes}
    halt = sum(sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve'])
    if k == 'A':                                                   # RL-H's inputs on the twin state (TSI-G on an AH light)
        h = [sum(S[l]['h'] for l in s) for s in d['serve']]; n = [sum(S[l]['n'] for l in s) for s in d['serve']]
        o = [h[0] / 10, h[1] / 10, n[0] / 20, n[1] / 20, cur == 0, cur == 1, spent / 60]
    elif k == 'SRL':
        cap = {l: TRACK.len[l] / VEH_SPACE for l in lanes}
        o = [cur == 0, cur == 1, float(spent >= CE.MIN_G)] + [S[l]['n'] / cap[l] for l in lanes] + [S[l]['h'] / cap[l] for l in lanes]
    elif k == 'RDQ':
        o = []
        for g, s in enumerate(d['serve']):
            for l in s:
                st = S[l]; o += [float(cur == g), (st['n'] - st['q']) / 28, st['w'] / 28, st['q'] / 28, st['s'] / 20 / 28]
    elif k == 'RMP':
        p = []
        for g in (0, 1):
            p.append(sum(S[l]['q'] for l in d['serve'][g]) - sum(_lane_stats(l)['q'] for l in TRACK.out[tid][g]))
        o = [float(max(cur, 0)), p[0], p[1]]
    else:                                                          # RWV
        o = [sum(S[l]['n'] for l in d['serve'][0]) / 28, sum(S[l]['n'] for l in d['serve'][1]) / 28, cur == 0, cur == 1]
    return np.array(o, np.float32), halt, cur


_PREV_RQ = W.reward_quantity


def reward_quantity(info, tid, rk):
    """Q with training reward -Q / div (div 10 for W20 families): Q = -10 r."""
    if rk not in ('DWT', 'WAITN', 'PRESS'):
        return _PREV_RQ(info, tid, rk)
    ls = CE.ls; TRACK.update(info, ls.simulation.getTime()); d = info.tls[tid]; lanes = list(d['serve'][0]) + list(d['serve'][1])
    if rk == 'DWT':
        Wn = sum(_lane_stats(l)['acc'] for l in lanes); ph = ls.trafficlight.getPhase(tid)
        decision = ph in d['greens'] and ls.trafficlight.getSpentDuration(tid) >= CE.MIN_G
        r = (TRACK.wlast.get(tid, Wn) - Wn) / 100.0
        if decision:
            TRACK.wlast[tid] = Wn
        return -10.0 * r
    if rk == 'WAITN':
        return -10.0 * float(np.clip(-sum(_lane_stats(l)['w'] for l in lanes) / 224, -4, 4))
    qin = sum(_lane_stats(l)['q'] for l in lanes); qout = sum(_lane_stats(l)['q'] for g in (0, 1) for l in TRACK.out[tid][g])
    return -10.0 * float(-(qin - qout))


W.family_obs = family_obs; W.reward_quantity = reward_quantity; CE.LightRL.obs = family_obs
_step = CE.LightRL.step


def step(self, t):
    TRACK.update(self.info, t); return _step(self, t)


CE.LightRL.step = step
