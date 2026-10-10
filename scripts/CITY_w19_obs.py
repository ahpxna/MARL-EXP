#!/usr/bin/env python3
"""W19 (PROTOCOL_CITY_WAVE19_20261008): learned keep / switch signals that differ from RL-H ONLY in the observation, the training reward or
a scale constant.  Same DQN (Q7: din -> 64 -> 64 -> 2, double DQN, Huber loss with kappa 1, gamma 0.9, Adam 1e-3, batch 256, 200 steps per
episode, Polyak 0.99, grad clip 5), same 120 episodes on TRAIN seeds 0-7, same epsilon schedule, same 5-s decision, 5-s minimum green.
Families (light index k = first + j, j = 0..4; DQN seed 11 + 100 (34 + j), shared by slot j across families):
  AH   34  obs A  (RL-H: h/10, n/20 per green, green one-hot, tau/60)                   reward -H/10   (H = halting count, v < 0.1 m/s)
  B1H  39  obs B1 (A + per green the counts with 0.1 <= v < 2 and 2 <= v < 5 m/s, /10)  reward -H/10
  B2H  44  obs B2 (per green the counts at 0-25, 25-50, 50-100, >= 100 m from the stop
                   line, /10, at any speed; green one-hot, tau/60; no halting, no speed)  reward -H/10
  AD   49  obs A                                                                        reward -D/10   (D = sum over vehicles of max(0, 1 - v / v_lane))
  B1D  54  obs B1                                                                       reward -D/10
  B2D  59  obs B2                                                                       reward -D/10
  S05  64  obs A with every denominator halved   (h/5,  n/10, tau/30)                    reward -H/10
  S2   69  obs A with every denominator doubled  (h/20, n/40, tau/120)                   reward -H/10
  R1   74  obs A                                                                        reward -H/1
  R100 79  obs A                                                                        reward -H/100
H and D are summed over the served lanes of both greens, as RL-H's reward; D counts a halted vehicle as at least 0.993 (same unit as H).
The reward is used in TRAINING only (the trainer's LightT); deployed lights (evaluators) only see the observation.
Installing this module patches scripts.CITY_env.LightRL.obs: the original method for obs-A families and for every light outside 34-83
(the current family is set by set_family, called by the W19 light_spec patch before a light is built; one family per process)."""
import numpy as np
import scripts.CITY_env as CE

FAMS = {'AH': (34, 'A', 'H', 10), 'B1H': (39, 'B1', 'H', 10), 'B2H': (44, 'B2', 'H', 10), 'AD': (49, 'A', 'D', 10), 'B1D': (54, 'B1', 'D', 10),
        'B2D': (59, 'B2', 'D', 10), 'S05': (64, 'S05', 'H', 10), 'S2': (69, 'S2', 'H', 10), 'R1': (74, 'A', 'H', 1), 'R100': (79, 'A', 'H', 100)}
DIM = {'A': 7, 'B1': 11, 'B2': 11, 'S05': 7, 'S2': 7}
SCALE = {'S05': np.array([2, 2, 2, 2, 1, 1, 2], np.float32), 'S2': np.array([0.5, 0.5, 0.5, 0.5, 1, 1, 0.5], np.float32)}
DBINS = (25.0, 50.0, 100.0)
CUR = dict(fam=None)
_ORIG_OBS = CE.LightRL.obs
_LEN = {}; _VMAX = {}


def fam_of(k):
    for f, (k0, *_r) in FAMS.items():
        if k0 <= k < k0 + 5:
            return f
    return None


def dqn_seed(k):
    return 11 + 100 * (34 + (k - FAMS[fam_of(k)][0]))


def set_family(f):
    assert f in FAMS, f
    if CUR['fam'] not in (None, f):
        raise RuntimeError(f'W19: two families in one process ({CUR["fam"]}, {f})')
    CUR['fam'] = f


def obs_kind():
    return FAMS[CUR['fam']][1] if CUR['fam'] else 'A'


def _speed_bins(lanes):
    ls = CE.ls; a = b = 0
    for l in lanes:
        for v in ls.lane.getLastStepVehicleIDs(l):
            sp = ls.vehicle.getSpeed(v); a += 0.1 <= sp < 2.0; b += 2.0 <= sp < 5.0
    return a, b


def _dist_bins(lanes):
    ls = CE.ls; c = [0, 0, 0, 0]
    for l in lanes:
        L = _LEN.get(l)
        if L is None:
            L = _LEN[l] = ls.lane.getLength(l)
        for v in ls.lane.getLastStepVehicleIDs(l):
            d = L - ls.vehicle.getLanePosition(v); i = 0
            while i < 3 and d >= DBINS[i]:
                i += 1
            c[i] += 1
    return c


def family_obs(self, tid):
    """(o, sum of halting counts, current green index) for the current family's observation kind."""
    k = obs_kind()
    if k == 'A':
        return _ORIG_OBS(self, tid)
    if k in SCALE:
        o, halt, cur = _ORIG_OBS(self, tid); return (o * SCALE[k]).astype(np.float32), halt, cur
    ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
    h = [sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve']]
    cur = d['greens'].index(ph) if ph in d['greens'] else -1
    if k == 'B1':
        o7, halt, cur = _ORIG_OBS(self, tid); ab = [_speed_bins(s) for s in d['serve']]
        return np.concatenate([o7, np.array([ab[0][0] / 10, ab[1][0] / 10, ab[0][1] / 10, ab[1][1] / 10], np.float32)]), halt, cur
    if k == 'B2':
        c = [_dist_bins(s) for s in d['serve']]
        o = [x / 10 for x in c[0]] + [x / 10 for x in c[1]] + [cur == 0, cur == 1, ls.trafficlight.getSpentDuration(tid) / 60]
        return np.array(o, np.float32), sum(h), cur
    raise ValueError(k)


def reward_quantity(info, tid, rk):
    """H (halting count) or D (sum of max(0, 1 - v / v_lane)) over the served lanes of both greens (lanes counted per green, as RL-H)."""
    ls = CE.ls; d = info.tls[tid]
    if rk == 'H':
        return sum(sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve'])
    tot = 0.0
    for s in d['serve']:
        for l in s:
            vm = _VMAX.get(l)
            if vm is None:
                vm = _VMAX[l] = ls.lane.getMaxSpeed(l)
            for v in ls.lane.getLastStepVehicleIDs(l):
                tot += max(0.0, 1.0 - ls.vehicle.getSpeed(v) / vm)
    return tot


CE.LightRL.obs = family_obs
