#!/usr/bin/env python3
"""The `CITY_spat_forecast.py fit` command, but calling the module's fit (so the Midtown patch of DEMO_midtown.py, MT-A6, applies; the CLI runs
its own copy of fit as __main__).  Same output file and message.  Usage: DEMO_midtown.py ... scripts/MT_spat_fit.py <k> <out.json> <npz files...>"""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_spat_forecast as FC  # noqa: E402
k, out, files = sys.argv[1], sys.argv[2], sys.argv[3:]
T = FC.fit(files); Path(out).write_text(json.dumps(T)); print('fit', k, 'files', T['n_files'], 'lights', len(T['per']), 'via', FC.fit.__module__)
