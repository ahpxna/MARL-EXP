#!/usr/bin/env python3
"""W15-1 closed-loop c2 prep for the FRESH3 lights RL-H:19..23 (copy of CITY_w8_prep.py with the light range and default directory
changed; the procedure, CITY_m3_train_E.prep with the CITY_f1b_prep provider at q 0.5 and the development fleet L11_s13, is unchanged).
Open-loop table read from <W7_FPR_DIR>/m2b/forecast_rlh<k>.json.  Usage: CITY_w15_prep.py <k> <out dir>"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w15_run  # noqa: E402,F401  (light_spec patch 4..23)
import scripts.CITY_f1b_prep as FB  # noqa: E402
import scripts.CITY_m3_train_E as TE  # noqa: E402
import torch  # noqa: E402
if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1)
    TE.P = Path(os.environ['W7_FPR_DIR']) if os.environ.get('W7_FPR_DIR') else ROOT / 'research/city_sim/w15_20261007/fresh3'; TE.set_provider = FB.set_provider
    k = int(sys.argv[1]); assert k in (19, 20, 21, 22, 23)
    print('W15 prep: provider c2 q 0.5; DEV_FLEET', TE.DEV_FLEET, 'open-loop table', TE.P / f'm2b/forecast_rlh{k}.json', flush=True)
    TE.prep(k, sys.argv[2], int(os.environ.get('W7_PREP_N', 8)), int(os.environ.get('W7_PREP_END', 3600)))
