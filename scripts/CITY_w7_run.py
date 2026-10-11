#!/usr/bin/env python3
"""W7-1 runner (PROTOCOL_CITY_WAVE7_20261005): the F1-A1 call-time light_spec patch (RL-H:4..8, scripts/CITY_f1a1_run.py, imported unchanged)
extended to the five NEW lights RL-H:9..13 = research/city_sim/w7_20261005/fpr/lights/RL-H_t<k>.pt; then run any script as __main__.
Usage: CITY_w7_run.py scripts/<x>.py <args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_f1a1_run as F1  # noqa: E402  (applies the 4..8 patch)
import scripts.CITY_xplay2 as X2  # noqa: E402
W7L = Path(os.environ['W7_LIGHTS']) if os.environ.get('W7_LIGHTS') else ROOT / 'research/city_sim/w7_20261005/fpr/lights'; NEW = (9, 10, 11, 12, 13)
_prev = X2.light_spec


def light_spec(s):
    k, _, t = s.partition(':')
    if k == 'RL-H' and t and int(t) in NEW:
        return X2.Q7.NET_S, W7L / f'RL-H_t{int(t)}.pt', None
    return _prev(s)


X2.light_spec = light_spec
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
