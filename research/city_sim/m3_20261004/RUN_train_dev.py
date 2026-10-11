#!/usr/bin/env python3
"""M3 DEV training wave (Amendment A1 + A1b): 10 arms x 2 DEV light seeds (k = 0, 1), at most 10 at a time."""
import os, subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT = Path('/Users/phanan/cig-amf-main'); os.chdir(ROOT); D = 'research/city_sim/m3_20261004'
env = dict(os.environ, PYTHONHASHSEED='0', OMP_NUM_THREADS='1')
J = [(k, arm, lam) for k in (0, 1) for arm, lam in [('E0q', 0), ('E0p', 0)] + [(a, l) for a in ('uniform', 'eta', 'active', 'receiver') for l in (1, 4)]]


def go(j):
    k, arm, lam = j; name = f'E_{arm}_lam{lam:g}_k{k}'
    with open(ROOT / D / 'train' / f'{name}.out', 'w') as f:
        r = subprocess.run(['nice', '-n', '5', 'external_envs/city_runtime/bin/python', '-u', 'scripts/CITY_m3_train_E.py', 'train', str(k), arm, str(lam),
                            f'{D}/train', '--prep', f'{D}/prep'], env=env, stdout=f, stderr=subprocess.STDOUT)
    return name, r.returncode


if __name__ == '__main__':
    (ROOT / D / 'train').mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(10) as ex:
        res = list(ex.map(go, J))
    bad = [n for n, c in res if c]; print(f'{len(J)} runs, failed: {bad}', flush=True); raise SystemExit(1 if bad else 0)
