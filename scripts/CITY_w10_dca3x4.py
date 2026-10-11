#!/usr/bin/env python3
"""W10-1 secondary arm (PROTOCOL_CITY_WAVE10_20261005): the corrected DC-Ada tuner CITY_w7_dca3_tune.py (unchanged, imported) with four times
TSI's light-side budget (704 truncated rollouts = 176 x 5400 s).  Usage: CITY_w10_dca3x4.py <t> <out dir>   (DCA3_SMOKE=1: budget 9)"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w7_dca3_tune as T  # noqa: E402
if __name__ == '__main__':
    if os.environ.get('DCA3_SMOKE') != '1':
        T.BUDGET = 4 * 176
    T.main(int(sys.argv[1]), sys.argv[2])
