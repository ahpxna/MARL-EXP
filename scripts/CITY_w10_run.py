#!/usr/bin/env python3
"""W10 diagnostic runner (PROTOCOL_CITY_WAVE10_20261005, W10-2 / W10-3), installed at run time; no evaluator is edited.
  modes:  serve    log every SPaT answer the fleet receives (the 'spat' attribute of every loaded fleet module is wrapped)
          shadow   call and log the provider, but give the fleet valid = False (it drives as sigma*)
          plain    log only (for the FT exactness self-check with the fleet's own program SPaT)
  Each run writes <W10_LOG>/<tag>_served_s<seed>.npz (t, light index, link, ttg, ttr, valid, module) and adds to the row
  held_* counters (W10-3): every second, each agent whose last setSpeed command is below its allowed speed by > 0.5 m/s (getSpeedWithoutTraCI is
  not usable: it equals getSpeed in this SUMO build, checked 20:1x) and whose follower within
  50 m is a human vehicle counts one held human-second (+ the follower's deficit to its allowed speed); agent_lanes_multi = share of those
  commanded agent-seconds on edges with more than one lane.  Phase traces come from the evaluator's own --record.
Usage: W10_LOG=<dir> CITY_w10_run.py <mode> [--net spider] scripts/<x>.py <args>"""
import os, runpy, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
MODE = sys.argv[1]; assert MODE in ('serve', 'shadow', 'plain'), MODE
ARGS = sys.argv[2:]
if ARGS and ARGS[0] == '--net':
    net = ARGS[1]; ARGS = ARGS[2:]
    if net == 'spider':
        import scripts.CITY_m4s_run  # noqa: F401  (spider net patch, as the spider evaluators)
    elif net == 'rand3':
        import scripts.CITY_n3_run  # noqa: F401  (rand3 net patch and lights RL-H 21..25, W10-2b)
    else:
        raise SystemExit(f'unknown net {net}')
else:
    import scripts.CITY_w8_run  # noqa: F401  (grid4 light_spec patch RL-H 4..18)
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
LOG = Path(os.environ['W10_LOG']); LOG.mkdir(parents=True, exist_ok=True)
ST = dict(q=[], cars=None, ids={}, held=0, held_def=0.0, cmd=0, multi=0, seen=0, maxd=0.0, nocars=0)
CMD = {}                                                               # last commanded speed per vehicle (-1 = released to SUMO)
_ss = CE.ls.vehicle.setSpeed


def _setspeed(v, s):
    CMD[v] = float(s); return _ss(v, s)


if isinstance(CE.ls.vehicle.__dict__.get('setSpeed'), staticmethod):
    CE.ls.vehicle.setSpeed = staticmethod(_setspeed)
else:
    CE.ls.vehicle.setSpeed = _setspeed


def _wrap(mname, f):
    def spat(tid, link):
        s = f(tid, link); t = float(CE.ls.simulation.getTime()); j = ST['ids'].setdefault(tid, len(ST['ids']))
        ST['q'].append((t, j, int(link), float(s.get('ttg', 0.0)), float(s.get('ttr', 0.0)), bool(s.get('valid')), mname))
        if MODE == 'shadow':
            return dict(ttg=0.0, ttr=0.0, valid=False, source='w10-shadow')
        return s
    spat._w10 = True
    return spat


def _install_spat():
    for mn, m in list(sys.modules.items()):
        if mn.startswith('scripts.CITY_') and mn not in ('scripts.CITY_spat_feature',) and callable(getattr(m, 'spat', None)) and not getattr(m.spat, '_w10', False):
            m.spat = _wrap(mn.split('.')[-1], m.spat)


_lf = E4.load_fleet


def load_fleet(spec, seed, guard):
    c, p = _lf(spec, seed, guard); ST['cars'] = c; return c, p


E4.load_fleet = load_fleet
_rep = E4.run_episode


def run_episode(net, rou, seed, light, cars, **kw):
    inner = light

    class Probe:
        def step(self, t):
            if inner is not None:
                inner.step(t)
            c = ST['cars']
            if c is None:
                ST['nocars'] += 1; return
            ls = CE.ls
            for v in ls.vehicle.getIDList():
                if not c.is_agent(v):
                    continue
                cm = CMD.get(v, -1.0); ST['seen'] += 1
                dd = ls.vehicle.getAllowedSpeed(v) - cm if cm >= 0 else 0.0; ST['maxd'] = max(ST['maxd'], dd)
                if dd <= 0.5:                                          # held = commanded below its allowed speed by more than 0.5 m/s
                    continue
                ST['cmd'] += 1; e = ls.vehicle.getRoadID(v)
                if e and not e.startswith(':') and ls.edge.getLaneNumber(e) > 1:
                    ST['multi'] += 1
                fl = ls.vehicle.getFollower(v, 50.0)
                if fl and fl[0] and not c.is_agent(fl[0]):
                    ST['held'] += 1; ST['held_def'] += max(0.0, ls.vehicle.getAllowedSpeed(fl[0]) - ls.vehicle.getSpeed(fl[0]))
    return _rep(net, rou, seed, Probe(), cars, **kw)


E4.run_episode = run_episode
_run = E4.run


def run(a, seed, end):
    CMD.clear(); _install_spat(); ST.update(q=[], cars=None, ids={}, held=0, held_def=0.0, cmd=0, multi=0, seen=0, maxd=0.0, nocars=0)
    lf0 = E4.load_fleet                                                 # wrap the final load_fleet chain at run time (CITY_eval6_v11 rebinds it at import)

    def lf(spec, seed_, guard):
        c, p = lf0(spec, seed_, guard); ST['cars'] = c; return c, p
    E4.load_fleet = lf
    try:
        out = _run(a, seed, end)
    finally:
        E4.load_fleet = lf0
    q = ST['q']; tag = a.tag or 'run'
    mods = sorted({x[6] for x in q}); mi = {m: k for k, m in enumerate(mods)}
    np.savez_compressed(LOG / f'{tag}_served_s{seed}.npz', t=np.array([x[0] for x in q], np.float64), j=np.array([x[1] for x in q], np.int16),
                        link=np.array([x[2] for x in q], np.int16), ttg=np.array([x[3] for x in q], np.float64), ttr=np.array([x[4] for x in q], np.float64),
                        valid=np.array([x[5] for x in q], bool), mod=np.array([mi[x[6]] for x in q], np.int8), mods=np.array(mods),
                        ids=np.array(sorted(ST['ids'], key=ST['ids'].get)))
    out.update(w10_mode=MODE, w10_queries=len(q), held_human_s=ST['held'], held_deficit_sum=ST['held_def'], commanded_agent_s=ST['cmd'],
               commanded_multi_lane_s=ST['multi'], probe_agent_s=ST['seen'], probe_max_diff=ST['maxd'], probe_steps_without_fleet=ST['nocars'])
    return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w10:{MODE}"
if __name__ == '__main__':
    target = ARGS[0]; sys.argv = [target] + ARGS[1:]; runpy.run_path(str(ROOT / target), run_name='__main__')
