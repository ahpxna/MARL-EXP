#!/usr/bin/env python3
"""W20 runner (PROTOCOL_CITY_WAVE20_20261009): the W19 runner's patches (imported, not run) plus scripts/CITY_w20_bench.py, the W20 lights
RL-H:84..103 = <W20_LIGHTS or research/city_sim/w20_20261009/lights>/RL-H_t<k>.pt, the TSI-G adapter `--light-obs bis` (any family), a
per-run tracker reset with the run's seed (fleet membership u(seed, id) < rho), and the per-second tracker update in the closed-loop prep
light (CITY_m3_core.LightE).  Then runs the target as __main__.   Usage: CITY_w20_run.py scripts/<x>.py <args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w19_run as R19  # noqa: E402  (W8 + W19 patches)
import scripts.CITY_w20_bench as B  # noqa: E402
import scripts.CITY_w19_obs as W  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_m3_core as M  # noqa: E402

W20L = Path(os.environ['W20_LIGHTS']) if os.environ.get('W20_LIGHTS') else ROOT / 'research/city_sim/w20_20261009/lights'
_prev = X2.light_spec


def light_spec(s):
    k, _, t = s.partition(':')
    if k == 'RL-H' and t and W.fam_of(int(t)) in B.NEWF:
        W.set_family(W.fam_of(int(t))); return X2.Q7.NET_S, W20L / f'RL-H_t{int(t)}.pt', None
    return _prev(s)


X2.light_spec = light_spec
_Base = E4.LightRLX


class LightRLG(_Base):
    def __init__(self, info, policy, max_g=None, adapter='raw', box=None):
        bis = adapter == 'bis'
        super().__init__(info, policy, max_g=max_g, adapter='raw' if bis else adapter, box=box)
        if not bis and W.obs_kind() in B.NEWK and adapter != 'raw':
            raise ValueError(f'W20: adapter {adapter} undefined for {W.obs_kind()}')
        self.adapter = adapter; B.TRACK.bis = bis


E4.LightRLX = LightRLG
_run = E4.run


def run(a, seed, end):
    B.TRACK.reset(); B.TRACK.seed = int(seed); B.TRACK.bis = False; B.TRACK.info = None
    out = _run(a, seed, end); out['w20_bis'] = B.TRACK.bis; return out


E4.run = run
_estep = M.LightE.step


def estep(self, t):
    B.TRACK.update(self.info, t); return _estep(self, t)


M.LightE.step = estep
if __name__ == '__main__':
    print('W20 runner: lights 84..103 from', W20L, flush=True)
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
