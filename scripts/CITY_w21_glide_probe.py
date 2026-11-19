#!/usr/bin/env python3
"""W21-I / W21-J wrapper (PROTOCOL_CITY_WAVE21_20261015): run between DEMO_midtown.py and the rest of the chain.  No file is edited.
  W21_REL=none | short:<m> | long:<m> | random:<p>
      a fleet speed command more than 0.5 m/s below the vehicle's allowed speed (a glide, as W10-3) is replaced by release to the base
      driver (setSpeed(v, -1)) when the agent's current edge is shorter than <m> (short), at least <m> long (long), or a deterministic hash
      of (traffic seed, vehicle, second) falls below <p> (random, the matched-rate control).  Counters: w21_glide_s, w21_released_s.
  W21_PROBE=1
      read-only per-second probe by edge-length bin [0, 50), [50, 100), [100, 200), >= 200 m over every vehicle on a normal edge:
      agent / human time-loss seconds sum max(0, 1 - v / v_allowed), agent / human halted seconds (v < 0.1), human-seconds within 50 m behind
      a gliding agent, lane spillback-seconds (a halted vehicle within 7.5 m of its lane's start; each lane once per second).
Rows get w21_rel, w21_probe.   Usage: DEMO_midtown.py scripts/CITY_w21_glide_probe.py scripts/<next> ..."""
import hashlib, os, runpy, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
REL = os.environ.get('W21_REL', 'none'); KIND, _, PAR = REL.partition(':'); assert KIND in ('none', 'short', 'long', 'random'), REL
PAR = float(PAR) if PAR else 0.0; PROBE = os.environ.get('W21_PROBE') == '1'
BINS = (50.0, 100.0, 200.0); NB = len(BINS) + 1
ST = dict(cars=None, seed=0, glide=0, rel=0); ELEN = {}; CMD = {}
_ss = CE.ls.vehicle.setSpeed


def _bin(x):
    return int(np.searchsorted(BINS, x, side='right'))


def _elen(e):
    if e not in ELEN:
        ELEN[e] = CE.ls.lane.getLength(f'{e}_0')
    return ELEN[e]


def U(seed, v, t):
    return int.from_bytes(hashlib.sha256(f'{seed}|{v}|{t}'.encode()).digest()[:8], 'big') / 2 ** 64


def _setspeed(v, s):
    c = ST['cars']
    if s >= 0 and c is not None and c.is_agent(v):
        ls = CE.ls
        if ls.vehicle.getAllowedSpeed(v) - s > 0.5:                     # a glide command
            ST['glide'] += 1; rel = False
            if KIND in ('short', 'long'):
                e = ls.vehicle.getRoadID(v)
                if e and not e.startswith(':'):
                    short = _elen(e) < PAR; rel = short if KIND == 'short' else not short
            elif KIND == 'random':
                rel = U(ST['seed'], v, int(ls.simulation.getTime())) < PAR
            if rel:
                ST['rel'] += 1; CMD[v] = -1.0; return _ss(v, -1)
        CMD[v] = float(s)
    elif c is not None and c.is_agent(v):
        CMD[v] = float(s)
    return _ss(v, s)


if isinstance(CE.ls.vehicle.__dict__.get('setSpeed'), staticmethod):
    CE.ls.vehicle.setSpeed = staticmethod(_setspeed)
else:
    CE.ls.vehicle.setSpeed = _setspeed
P = {}


def _preset():
    for k in ('tl_a', 'tl_h', 'halt_a', 'halt_h', 'held_h', 'spill', 'vs_a', 'vs_h'):
        P[k] = np.zeros(NB)


_rep = E4.run_episode


def run_episode(net, rou, seed, light=None, cars=None, **kw):
    inner = light

    class Probe:
        def step(self, t):
            if inner is not None:
                inner.step(t)
            if not PROBE:
                return
            ls = CE.ls; c = ST['cars']; spilled = set()
            for v in ls.vehicle.getIDList():
                e = ls.vehicle.getRoadID(v)
                if not e or e.startswith(':'):
                    continue
                b = _bin(_elen(e)); sp = ls.vehicle.getSpeed(v); va = ls.vehicle.getAllowedSpeed(v); ag = c is not None and c.is_agent(v)
                k = 'a' if ag else 'h'; P[f'vs_{k}'][b] += 1; P[f'tl_{k}'][b] += max(0.0, 1.0 - sp / va) if va > 0 else 0.0
                if sp < 0.1:
                    P[f'halt_{k}'][b] += 1
                    ln = ls.vehicle.getLaneID(v)
                    if ln not in spilled and ls.vehicle.getLanePosition(v) < 7.5:
                        spilled.add(ln); P['spill'][b] += 1
                if ag and CMD.get(v, -1.0) >= 0 and va - CMD[v] > 0.5:
                    fl = ls.vehicle.getFollower(v, 50.0)
                    if fl and fl[0] and not c.is_agent(fl[0]):
                        P['held_h'][b] += 1
    return _rep(net, rou, seed, Probe(), cars, **kw)


E4.run_episode = run_episode
_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    c, p = _lf(spec, seed, guard); ST['cars'] = c; return c, p


E4.load_fleet = load_fleet
_run = E4.run


def run(a, seed, end):
    ST.update(cars=None, seed=int(seed), glide=0, rel=0); CMD.clear(); _preset()
    lf0 = E4.load_fleet                                                 # rebind at run time (CITY_eval6_v11 rebinds load_fleet at import)

    def lf(spec, seed_, guard):
        c, p = lf0(spec, seed_, guard); ST['cars'] = c; return c, p
    E4.load_fleet = lf
    try:
        out = _run(a, seed, end)
    finally:
        E4.load_fleet = lf0
    out.update(w21_rel=REL, w21_glide_s=ST['glide'], w21_released_s=ST['rel'])
    if PROBE:
        out['w21_probe'] = {k: v.tolist() for k, v in P.items()} | dict(bins=list(BINS))
    return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w21glide:{REL}:{int(PROBE)}"
print(f'W21 glide/probe wrapper: release {REL}, probe {PROBE}', flush=True)
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
