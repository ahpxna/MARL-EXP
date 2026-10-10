#!/usr/bin/env python3
"""W15 runner (PROTOCOL_CITY_WAVE15_20261007): the W8 light_spec patch (RL-H 4..18; scripts/CITY_w8_run.py, imported unchanged) extended to
the third fresh-policy set RL-H:19..23 = research/city_sim/w15_20261007/fresh3/lights/RL-H_t<k>.pt (env W15_LIGHTS overrides the directory);
then run any script as __main__ (chains with CITY_w9_run / CITY_w13_modes / CITY_w13_idm).  Usage: CITY_w15_run.py scripts/<x>.py <args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w8_run  # noqa: E402,F401  (4..18)
import scripts.CITY_xplay2 as X2  # noqa: E402
W15L = Path(os.environ['W15_LIGHTS']) if os.environ.get('W15_LIGHTS') else ROOT / 'research/city_sim/w15_20261007/fresh3/lights'; NEW = (19, 20, 21, 22, 23)
_prev = X2.light_spec


def light_spec(s):
    k, _, t = s.partition(':')
    if k == 'RL-H' and t and int(t) in NEW:
        return X2.Q7.NET_S, W15L / f'RL-H_t{int(t)}.pt', None
    return _prev(s)


X2.light_spec = light_spec
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
