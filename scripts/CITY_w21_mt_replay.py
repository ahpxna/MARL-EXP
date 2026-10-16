#!/usr/bin/env python3
"""W21-G / W21-H wrapper (PROTOCOL_CITY_WAVE21_20261015): run between DEMO_midtown.py and the rest of the chain.
  (1) Replay on the actrest base: CITY_eval4.run's --replay branch bypasses build_light, so DEMO_midtown's MT_BASE=actrest additional file
      (the 56 multi-phase junctions on actuated programs) is not loaded and the replay cannot reproduce a recorded run (W21-C KH-1).  While a
      CITY_eval4.Replay light is active, this wrapper appends ['-a', midtown_full_act_rest.add.xml] to the SUMO command (run_episode extra).
  (2) MT_SPAT_CAP=<s> (W21-H): the fleet's SPaT answers are bounded by a known maximum green: on a green serving the link, ttr <= cap - time in
      green; during the other green, ttg <= (cap - time in green) + 3 (yellow) + 1 (offset).  Wraps CITY_spat_forecast_n4.make_spat_n4 (as
      installed by DEMO_midtown).  No file is edited.   Usage: DEMO_midtown.py scripts/CITY_w21_mt_replay.py scripts/<next> ..."""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_spat_forecast_n4 as N4  # noqa: E402
ADD = ROOT / 'research/city_sim/net/midtown_full_act_rest.add.xml'; ST = dict(replay=False, added=0)
assert os.environ.get('MT_BASE') == 'actrest' and ADD.exists(), 'W21-G/H wrapper expects MT_BASE=actrest'
_init = E4.Replay.__init__


def _rinit(self, rec, info):
    _init(self, rec, info); ST['replay'] = True


E4.Replay.__init__ = _rinit
_rep = E4.run_episode


def run_episode(net, rou, seed, light=None, cars=None, **kw):
    if ST['replay']:
        ex = list(kw.get('extra', ()))
        if str(ADD) not in ex:
            ex += ['-a', str(ADD)]; ST['added'] += 1
        kw['extra'] = tuple(ex)
    return _rep(net, rou, seed, light, cars, **kw)


E4.run_episode = run_episode
CAP = float(os.environ['MT_SPAT_CAP']) if os.environ.get('MT_SPAT_CAP') else None
if CAP is not None:
    _mk = N4.make_spat_n4

    def make_capped(model_path, q, info, tracker, gate):
        f = _mk(model_path, q, info, tracker, gate)

        def spat(tid, link):
            s = f(tid, link)
            if not s.get('valid') or tid not in info.tls or s.get('ttr', 0.0) >= 900:   # 999 = served by every green (never red)
                return s
            ls = CE.ls; ph = ls.trafficlight.getPhase(tid); gs = list(info.tls[tid]['greens'])
            if ph not in gs:
                return s
            rem = max(0.0, CAP - float(ls.trafficlight.getSpentDuration(tid))); s = dict(s)
            if s.get('ttr', 0.0) > 0 and s.get('ttg', 0.0) == 0.0:
                s['ttr'] = min(s['ttr'], rem)
            elif s.get('ttg', 0.0) > 0:
                s['ttg'] = min(s['ttg'], rem + 3.0 + 1.0)
            return s
        spat.stats = getattr(f, 'stats', {})
        return spat
    N4.make_spat_n4 = make_capped
_run = E4.run


def run(a, seed, end):
    ST['replay'] = False
    out = _run(a, seed, end); out.update(w21_replay_actrest=ST['replay'], w21_spat_cap=CAP); return out


E4.run = run
print(f'W21 Midtown wrapper: replay on actrest base, spat cap {CAP}', flush=True)
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
