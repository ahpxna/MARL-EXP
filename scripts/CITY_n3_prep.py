#!/usr/bin/env python3
"""W8-4 closed-loop c2 prep for a rand3 light RL-H:k (k in 21..25): CITY_f1b_prep.py's procedure unchanged (CITY_m3_train_E.prep: 8 TRAIN
episodes, dev fleet on provider c2 at q 0.5, then CITY_spat_forecast.fit) on the rand3 network, with the rand3 DEVELOPMENT fleet N3_s13 in place of
the grid4 L11_s13, and the open-loop table read from <net3 dir>/m2b/forecast_rlh<k>.json.  Usage: CITY_n3_prep.py <k> <out dir>"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_n3_run  # noqa: E402,F401  (rand3 network + light patch; imported first)
import scripts.CITY_f1b_prep as FB  # noqa: E402
import scripts.CITY_m3_train_E as TE  # noqa: E402
import torch  # noqa: E402
if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1); N = Path(os.environ.get('N3_DIR') or ROOT / 'research/city_sim/w8_20261005/net3')
    TE.P = N; TE.set_provider = FB.set_provider; TE.DEV_FLEET = N / 'fleets/N3_s13_fleet.pt'; k = int(sys.argv[1]); assert k in (21, 22, 23, 24, 25)
    print('NET3 prep: provider c2 q 0.5; DEV_FLEET', TE.DEV_FLEET, 'open-loop table', TE.P / f'm2b/forecast_rlh{k}.json', flush=True)
    TE.prep(k, sys.argv[2], int(os.environ.get('N3_PREP_N', 8)), int(os.environ.get('N3_PREP_END', 3600)))
