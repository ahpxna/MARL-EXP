#!/usr/bin/env python3
"""W19 closed-loop c2 prep for the W19 lights RL-H:34..83 (copy of CITY_w15_prep.py with the light range, the default directory and an
assertion that it runs under CITY_w19_run.py, whose LightE.obs7 patch gives the closed-loop light its family's observation; the procedure,
CITY_m3_train_E.prep with the CITY_f1b_prep provider at q 0.5 and the development fleet L11_s13, is unchanged).
Open-loop table read from <W7_FPR_DIR>/m2b/forecast_rlh<k>.json.  Usage: CITY_w19_run.py scripts/CITY_w19_prep.py <k> <out dir>"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_m3_core as M  # noqa: E402
assert M.LightE.obs7.__module__ != 'scripts.CITY_m3_core', 'run through scripts/CITY_w19_run.py'
import scripts.CITY_f1b_prep as FB  # noqa: E402
import scripts.CITY_m3_train_E as TE  # noqa: E402
import scripts.CITY_w19_obs as W  # noqa: E402
import torch  # noqa: E402
if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1)
    TE.P = Path(os.environ['W7_FPR_DIR']) if os.environ.get('W7_FPR_DIR') else ROOT / 'research/city_sim/w19_20261008'; TE.set_provider = FB.set_provider
    k = int(sys.argv[1]); assert W.fam_of(k), k
    print('W19 prep: provider c2 q 0.5; DEV_FLEET', TE.DEV_FLEET, 'open-loop table', TE.P / f'm2b/forecast_rlh{k}.json', 'family', W.fam_of(k), flush=True)
    TE.prep(k, sys.argv[2], int(os.environ.get('W7_PREP_N', 8)), int(os.environ.get('W7_PREP_END', 3600)))
    print('W19 prep family in force', W.CUR['fam'], 'obs', W.obs_kind(), flush=True)
