#!/usr/bin/env python3
"""M4 spider runner (M4 stage 2+): point the grid4 stack at the spider net and run any script as __main__ on it.
Patches (call-time attributes, verified: no module captures them at import): Q7.NET_S = Q7.NET_A = spider.net.xml,
Q7.ROU = demand/spider/p2.0/rou_s{}.xml, Q7.TRAIN_SEEDS = 0..7.  Usage: CITY_m4s_run.py scripts/<script>.py <its arguments>"""
import runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
Q7.NET_S = Q7.NET_A = str(ROOT / 'research/city_sim/net/spider.net.xml'); Q7.ROU = str(ROOT / 'research/city_sim/demand/spider/p2.0/rou_s{}.xml')
Q7.TRAIN_SEEDS = list(range(8))
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
