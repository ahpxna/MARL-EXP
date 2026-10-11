#!/usr/bin/env python3
"""F1 (Amendment A5): fit a forecast-K table (CITY_spat_forecast_k.fit_k) on the current Q7.NET_S (run through CITY_sl_runw4 / CITY_sl_run).
Usage: CITY_sl_runw4.py scripts/CITY_sl_fitk.py <out.json> <trace .npz files ...>"""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
out, files = sys.argv[1], sys.argv[2:]; T = FK.fit_k(files, Q7.NET_S)
Path(out).write_text(json.dumps(T)); print('fit_k', Q7.NET_S, 'files', len(files), 'lights', len(T['per']), {t: len(v) for t, v in T['per'].items()})
