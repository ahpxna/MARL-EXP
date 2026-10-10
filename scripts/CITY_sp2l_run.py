#!/usr/bin/env python3
"""W10-4 spider-2L runner (PROTOCOL_CITY_WAVE10_20261005, Amendment A2): CITY_m4s_run's spider patch (imported first, so later imports of it
are no-ops), re-pointed at research/city_sim/net/spider2l.net.xml and demand/spider2l/p2.0/rou_s{}.xml; then any script as __main__.
Usage: CITY_sp2l_run.py scripts/<x>.py <args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_m4s_run  # noqa: E402,F401
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
Q7.NET_S = Q7.NET_A = str(ROOT / 'research/city_sim/net/spider2l.net.xml'); Q7.ROU = os.environ.get('W10_SP2L_ROU', str(ROOT / 'research/city_sim/demand/spider2l/p2.0/rou_s{}.xml'))   # smoke: its own directory
Q7.TRAIN_SEEDS = list(range(8))
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
