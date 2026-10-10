#!/usr/bin/env python3
"""M3 Addendum A2 runner: every E checkpoint (20) with a SHADOW R10 fleet (dev nets s13, s113) on DEV traffic; pool 4; then the report."""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT = Path('/Users/phanan/cig-amf-main'); os.chdir(ROOT); D = 'research/city_sim/m3_20261004'; E = f'{D}/shadow'; P = 'research/city_sim/spat_pilot_20261004'
S = [str(s) for s in [100, 101, 102, 103, 104] + list(range(200, 210))]; env = dict(os.environ, PYTHONHASHSEED='0', OMP_NUM_THREADS='1', XPLAY_TMP=str(ROOT / E / 'tmp'))
ARMS = ['E_E0q_lam0', 'E_E0p_lam0'] + [f'E_{a}_lam{l}' for a in ('uniform', 'eta', 'active', 'receiver') for l in (1, 4)]
J = [(a, k, fl) for a in ARMS for k in (0, 1) for fl in ('s13', 's113')]


def go(j):
    a, k, fl = j
    with open(ROOT / E / 'run.log', 'a') as f:
        r = subprocess.run(['nice', '-n', '5', 'external_envs/city_runtime/bin/python', '-u', 'scripts/CITY_eval_m3_shadow.py', '--spat-arm', 'deployed',
                            '--light', f'M3E:{D}/train/{a}_k{k}.pt', '--fleet', f'SHADOW:{P}/fleets_v11/L11_{fl}_fleet.pt', '--seeds', *S,
                            '--tag', f'{a}_k{k}_{fl}', '--out', E], env=env, stdout=f, stderr=subprocess.STDOUT)
    return f'{a}_k{k}_{fl}', r.returncode


if __name__ == '__main__':
    with ThreadPoolExecutor(4) as ex:
        res = list(ex.map(go, J))
    bad = [t for t, c in res if c]; print(len(J), 'jobs, failed:', bad, flush=True)
    sys.exit(1 if bad else subprocess.run(['external_envs/city_runtime/bin/python', 'scripts/CITY_m3_shadow_report.py'], env=env).returncode)
