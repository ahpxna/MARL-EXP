#!/usr/bin/env python3
"""F1 D-dir runner (PROTOCOL_CITY_F1 §1): 9 deltas x 4 replayed RL-H schedules (fleet R10 L11_s{213+100k}) x SELECT 100-104; pool 10."""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT = Path('/Users/phanan/cig-amf-main'); os.chdir(ROOT); E = 'research/city_sim/f1_20261004/ddir'; P = 'research/city_sim/spat_pilot_20261004'
env = dict(os.environ, PYTHONHASHSEED='0', OMP_NUM_THREADS='1', XPLAY_TMP=str(ROOT / E / 'tmp'))
J = [(d, k) for d in (-8, -4, -2, -1, 0, 1, 2, 4, 8) for k in range(4)]


def go(j):
    d, k = j; tag = f'F0b_d{d:+d}_k{k}'
    with open(ROOT / E / 'run.log', 'a') as f:
        r = subprocess.run(['nice', '-n', '5', 'external_envs/city_runtime/bin/python', '-u', 'scripts/CITY_f1_ddir.py', str(d), '--light', 'FT',
                            '--replay-dir', f'{P}/m3_headroom/replay_rlh{k}', '--fleet', f'PL:{P}/fleets_v11/L11_s{213 + 100 * k}_fleet.pt',
                            '--seeds', '100', '101', '102', '103', '104', '--tag', tag, '--out', E], env=env, stdout=f, stderr=subprocess.STDOUT)
    return tag, r.returncode


if __name__ == '__main__':
    with ThreadPoolExecutor(10) as ex:
        res = list(ex.map(go, J))
    bad = [t for t, c in res if c]; print(len(J), 'jobs, failed:', bad, flush=True); sys.exit(1 if bad else 0)
