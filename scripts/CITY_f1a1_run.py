#!/usr/bin/env python3
"""F1-A1 runner (PROTOCOL_CITY_F1_ADAPTED_FLEET_20261004 Amendment F1-A1): a call-time patch of CITY_xplay2.light_spec so that RL-H:4..8 are
the five new independent lights research/city_sim/m3_lights_20261004/RL-H_t<k>.pt (RL-H:0..3 unchanged), then run any script as __main__.
Every caller reaches light_spec as X2.light_spec at call time (checked: no module imports the name).  Usage: CITY_f1a1_run.py scripts/<x>.py <args>"""
import runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_xplay2 as X2  # noqa: E402
M3L = ROOT / 'research/city_sim/m3_lights_20261004'; NEW = (4, 5, 6, 7, 8)
_ls = X2.light_spec


def light_spec(s):
    k, _, t = s.partition(':')
    if k == 'RL-H' and t and int(t) in NEW:
        return X2.Q7.NET_S, M3L / f'RL-H_t{int(t)}.pt', None
    return _ls(s)


X2.light_spec = light_spec
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
