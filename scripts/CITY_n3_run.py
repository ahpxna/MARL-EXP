#!/usr/bin/env python3
"""W8-4 NET3 runner (PROTOCOL_CITY_WAVE8_20261005): point the grid4 stack at the rand3 network (as CITY_m4s_run does for spider) and map the
NEW rand3 lights RL-H:21..25 = research/city_sim/w8_20261005/net3/lights/RL-H_t<k>.pt; then run any script as __main__.
Patches (call-time attributes): Q7.NET_S = Q7.NET_A = rand3.net.xml, Q7.ROU = demand/rand3/rou_s{}.xml (env N3_ROU overrides, used only to
choose the demand period), Q7.TRAIN_SEEDS = 0..7.  Usage: CITY_n3_run.py scripts/<script>.py <its arguments>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
Q7.NET_S = Q7.NET_A = str(ROOT / 'research/city_sim/net/rand3.net.xml')
Q7.ROU = os.environ.get('N3_ROU') or str(ROOT / 'research/city_sim/demand/rand3/rou_s{}.xml'); Q7.TRAIN_SEEDS = list(range(8))
import scripts.CITY_xplay2 as X2  # noqa: E402
N3L = Path(os.environ['N3_LIGHTS']) if os.environ.get('N3_LIGHTS') else ROOT / 'research/city_sim/w8_20261005/net3/lights'; NEW = (21, 22, 23, 24, 25)
_prev = X2.light_spec


def light_spec(s):
    k, _, t = s.partition(':')
    if k == 'RL-H' and t and int(t) in NEW:
        return Q7.NET_S, N3L / f'RL-H_t{int(t)}.pt', None
    return _prev(s)


X2.light_spec = light_spec
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
