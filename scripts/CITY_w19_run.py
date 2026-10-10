#!/usr/bin/env python3
"""W19 runner (PROTOCOL_CITY_WAVE19_20261008): the W8 light_spec patch (RL-H 4..18, imported unchanged) extended to the W19 lights
RL-H:34..83 = <W19_LIGHTS or research/city_sim/w19_20261008/lights>/RL-H_t<k>.pt, each tagged with its family (scripts/CITY_w19_obs.py);
building one sets the process's family, so CITY_env.LightRL.obs, CITY_eval4.LightRLX (input adapter) and CITY_m3_core.LightE.obs7 (the
closed-loop prep light) all compute that family's observation.  Adapter rules: q:A:B rescales the two halting features to the family's
denominator (S05 h/5, S2 h/20); B2 (no halting feature) refuses any adapter.  Then runs the target as __main__ (chains like CITY_w15_run).
Usage: CITY_w19_run.py scripts/<x>.py <args>"""
import os, runpy, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w8_run  # noqa: E402,F401  (4..18)
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_m3_core as M  # noqa: E402
import scripts.CITY_w19_obs as W  # noqa: E402

W19L = Path(os.environ['W19_LIGHTS']) if os.environ.get('W19_LIGHTS') else ROOT / 'research/city_sim/w19_20261008/lights'
_prev = X2.light_spec; ACTIVE = True


def light_spec(s):
    k, _, t = s.partition(':')
    if k == 'RL-H' and t and W.fam_of(int(t)):
        W.set_family(W.fam_of(int(t))); return X2.Q7.NET_S, W19L / f'RL-H_t{int(t)}.pt', None
    return _prev(s)


X2.light_spec = light_spec
_Base = E4.LightRLX


class LightRLF(_Base):
    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        kind = self.adapter.split(':')[0]
        if W.obs_kind() != 'A' and kind not in ('raw', 'q'):
            raise ValueError(f'W19: adapter {self.adapter} undefined for obs {W.obs_kind()}')
        if W.obs_kind() == 'B2' and kind == 'q' and (self.qa or self.qb):
            raise ValueError('W19: B2 has no halting feature; the q adapter is undefined')

    def obs(self, tid):
        o, halt, cur = super().obs(tid)
        ok = W.obs_kind()
        if ok in W.SCALE and self.adapter.split(':')[0] == 'q' and (self.qa or self.qb):
            o = o.copy(); o[0] *= W.SCALE[ok][0]; o[1] *= W.SCALE[ok][1]
        return o, halt, cur


E4.LightRLX = LightRLF
_obs7 = M.LightE.obs7


def obs7(self, tid):
    if W.obs_kind() == 'A':
        return _obs7(self, tid)
    o, halt, cur = W.family_obs(self, tid); return o, cur, halt


M.LightE.obs7 = obs7
if __name__ == '__main__':
    print('W19 runner: lights 34..83 from', W19L, flush=True)
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
