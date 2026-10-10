#!/usr/bin/env python3
"""W8-2 closed-loop c2 prep for a NEW light RL-H:k (k in 14..18; copy of CITY_w7_prep.py): CITY_f1b_prep.py's procedure unchanged (CITY_m3_train_E.prep: 8 TRAIN episodes,
dev fleet L11_s13 on provider c2 at q 0.5, then CITY_spat_forecast.fit), with the W7 light_spec patch and the open-loop table read from
research/city_sim/w7_20261005/fpr/m2b/forecast_rlh<k>.json.  Usage: CITY_w7_prep.py <k> <out dir>"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w8_run  # noqa: E402,F401  (light_spec patch 4..18)
import scripts.CITY_f1b_prep as FB  # noqa: E402  (its set_provider: c2 at q 0.5)
import scripts.CITY_m3_train_E as TE  # noqa: E402
import torch  # noqa: E402
if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1)
    TE.P = Path(os.environ['W7_FPR_DIR']) if os.environ.get('W7_FPR_DIR') else ROOT / 'research/city_sim/w8_20261005/fresh2'; TE.set_provider = FB.set_provider; k = int(sys.argv[1]); assert k in (14, 15, 16, 17, 18)
    print('W8 prep: provider c2 q 0.5; DEV_FLEET', TE.DEV_FLEET, 'open-loop table', TE.P / f'm2b/forecast_rlh{k}.json', flush=True)
    TE.prep(k, sys.argv[2], int(os.environ.get('W7_PREP_N', 8)), int(os.environ.get('W7_PREP_END', 3600)))   # smoke only overrides
