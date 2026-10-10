#!/usr/bin/env python3
"""M3′ DEV runner (PROTOCOL_CITY_M3P §4): RPC receiver / eta / random (rates from m3p/rate/rates.json) under RL-H:k (k = 0, 1) with dev fleets
s13 / s113 on DEV (SELECT 100-104 + 200-209), plus SHADOW rows for the clean light cost; pool 8; then the report."""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT = Path('/Users/phanan/cig-amf-main'); os.chdir(ROOT); D = 'research/city_sim/m3p_20261004'; E = f'{D}/dev'; P = 'research/city_sim/spat_pilot_20261004'
S = [str(s) for s in [100, 101, 102, 103, 104] + list(range(200, 210))]; env = dict(os.environ, PYTHONHASHSEED='0', OMP_NUM_THREADS='1', XPLAY_TMP=str(ROOT / E / 'tmp'))
RATE = f'{D}/rate/rates.json'; J = []
for k in (0, 1):
    for trig in ('receiver', 'eta', 'random'):
        spec = f'RPC:{k}:{trig}' + (f':{RATE}' if trig == 'random' else '')
        for fl in ('s13', 's113'):
            J.append(('scripts/CITY_eval_m3p.py', spec, f'PL:{P}/fleets_v11/L11_{fl}_fleet.pt', f'RPC_{trig}_k{k}_{fl}'))
            J.append(('scripts/CITY_eval_m3p_shadow.py', spec, f'SHADOW:{P}/fleets_v11/L11_{fl}_fleet.pt', f'RPC_{trig}_k{k}_{fl}_shadow'))


def go(j):
    script, spec, fleet, tag = j
    with open(ROOT / E / 'run.log', 'a') as f:
        r = subprocess.run(['nice', '-n', '5', 'external_envs/city_runtime/bin/python', '-u', script, '--light', spec, '--fleet', fleet, '--seeds', *S, '--tag', tag, '--out', E],
                           env=env, stdout=f, stderr=subprocess.STDOUT)
    return tag, r.returncode


if __name__ == '__main__':
    (ROOT / E / 'tmp').mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(8) as ex:
        res = list(ex.map(go, J))
    bad = [t for t, c in res if c]; print(len(J), 'jobs, failed:', bad, flush=True)
    sys.exit(1 if bad else subprocess.run(['external_envs/city_runtime/bin/python', 'scripts/CITY_m3p_dev_report.py'], env=env).returncode)
