#!/usr/bin/env python3
"""F1-A1 closed-loop provider prep for a new light RL-H:k (k in 4..8): CITY_m3_train_E.prep UNCHANGED (8 TRAIN episodes, dev fleet L11_s13 on
the open-loop M2b table at q 0.5, then CITY_spat_forecast.fit), with the light_spec patch of CITY_f1a1_run and the open-loop table read from
research/city_sim/f1a1_20261004/m2b/forecast_rlh<k>.json (TE.P points at the F1-A1 directory; TE.DEV_FLEET was bound at import, unchanged).
Usage: CITY_f1a1_prep.py <k> <out dir>"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_f1a1_run  # noqa: E402,F401  (light_spec patch)
import scripts.CITY_m3_train_E as TE  # noqa: E402
import torch  # noqa: E402
if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1)
    TE.P = ROOT / 'research/city_sim/f1a1_20261004'; k = int(sys.argv[1]); assert k in (4, 5, 6, 7, 8)
    print('DEV_FLEET', TE.DEV_FLEET, 'open-loop table', TE.P / f'm2b/forecast_rlh{k}.json', flush=True)
    TE.prep(k, sys.argv[2], 8, 3600)
