#!/usr/bin/env python3
"""F1 Salt Lake runner (PROTOCOL_CITY_F1_SALTLAKE_20261008): CITY_m4s_run's multi-green patches (imported first), re-pointed at
research/city_sim/net/saltlake_<SL_SITE>.net.xml and demand/saltlake/<SL_SITE>/rou_s{}.xml (seed = day of year 2023); TRAIN_SEEDS = the
protocol's TRAIN days.  Env SL_SITE in {400sX200w, stateXuniversity}.  Usage: SL_SITE=<site> CITY_sl_run.py scripts/<x>.py <args>"""
import os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_m4s_run  # noqa: E402,F401
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
from scripts.CITY_sl_build import days  # noqa: E402
SITE = os.environ['SL_SITE']; assert SITE in ('400sX200w', 'stateXuniversity'), SITE
Q7.NET_S = Q7.NET_A = str(ROOT / f'research/city_sim/net/saltlake_{SITE}.net.xml')
Q7.ROU = str(ROOT / f'research/city_sim/demand/saltlake/{SITE}/rou_s{{}}.xml')
Q7.TRAIN_SEEDS = [d.timetuple().tm_yday for d in days(SITE, 'train')]
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
