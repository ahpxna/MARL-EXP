#!/usr/bin/env python3
"""W8 runner (PROTOCOL_CITY_WAVE8_20261005): the W7 light_spec patch (RL-H:4..8 F1-A1, RL-H:9..13 W7-1; scripts/CITY_w7_run.py, imported
unchanged) extended to the second fresh-policy set RL-H:14..18 = research/city_sim/w8_20261005/fresh2/lights/RL-H_t<k>.pt (env W8_LIGHTS
overrides the directory, smoke only); then run any script as __main__.  Usage: CITY_w8_run.py scripts/<x>.py <args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w7_run  # noqa: E402,F401  (4..13)
import scripts.CITY_xplay2 as X2  # noqa: E402
W8L = Path(os.environ['W8_LIGHTS']) if os.environ.get('W8_LIGHTS') else ROOT / 'research/city_sim/w8_20261005/fresh2/lights'; NEW = (14, 15, 16, 17, 18)
_prev = X2.light_spec


def light_spec(s):
    k, _, t = s.partition(':')
    if k == 'RL-H' and t and int(t) in NEW:
        return X2.Q7.NET_S, W8L / f'RL-H_t{int(t)}.pt', None
    return _prev(s)


X2.light_spec = light_spec
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
