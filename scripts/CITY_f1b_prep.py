#!/usr/bin/env python3
"""F1-B B2 closed-loop prep for light RL-H:k (k in 4..8): CITY_m3_train_E.prep UNCHANGED (8 TRAIN episodes, dev fleet L11_s13, fit) with ONE
change, the dev fleet's SPaT during prep is provider c2 at q 0.5 (the original prep used the UNcorrected CITY_spat_forecast at q 0.5).  The light
is greedy RL-H (lambda 0; its internal ticket forecast object stays CITY_spat_forecast.Forecast and does not act).  Open-loop table from
f1a1_20261004/m2b (as F1-A1).  Usage: CITY_f1b_prep.py <k> <out dir>"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_f1a1_run  # noqa: E402,F401
import scripts.CITY_m3_train_E as TE  # noqa: E402
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402
import torch  # noqa: E402


def set_provider(table):
    spat_fn = C2.make_spat_c2(table, 0.5)[0]; F = FC.Forecast(table, 0.5)
    for m in (TE.V8, TE.ES, TE.GL, TE.LD, TE.V11):
        m.spat = spat_fn
    return spat_fn, F


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1)
    TE.P = ROOT / 'research/city_sim/f1a1_20261004'; TE.set_provider = set_provider; k = int(sys.argv[1]); assert k in (4, 5, 6, 7, 8)
    print('F1-B prep: provider c2 q 0.5; DEV_FLEET', TE.DEV_FLEET, 'open-loop table', TE.P / f'm2b/forecast_rlh{k}.json', flush=True)
    TE.prep(k, sys.argv[2], 8, 3600)
