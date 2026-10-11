#!/usr/bin/env python3
"""H5 reference only: F1 unavailable service, horizon matched to training (3600s; smoke 300s).
Trip metrics include arrived and unfinished vehicles at that same horizon; confirmation remains 5400s.
"""
import sys, runpy, hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; sys.path.insert(0,str(ROOT))
import scripts.CITY_eval4 as E4
_run=E4.run
def run(a, seed, end):
    horizon=300 if a.smoke else 3600
    r=_run(a,seed,horizon); r['h5_reference_horizon']=horizon
    return r
E4.run=run
E4.SRC += '+h5_reference:' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
runpy.run_path(str(ROOT/'scripts/CITY_eval_f1.py'),run_name='__main__')
