#!/usr/bin/env python3
"""F1 DEV evaluation (PROTOCOL_CITY_F1 §3): each trained F1 / F1-scratch fleet under ITS OWN light RL-H:k with the locked provider, DEV traffic;
F0 and R rows come from the §0 provider runs (same producer CITY_eval_f1, same traffic).  Then the DEV report."""
import json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT = Path('/Users/phanan/cig-amf-main'); os.chdir(ROOT); D = 'research/city_sim/f1_20261004'
q = json.loads((ROOT / D / 'prov/locked.json').read_text())['q']; S = [str(s) for s in [100, 101, 102, 103, 104] + list(range(200, 210))]
env = dict(os.environ, PYTHONHASHSEED='0', OMP_NUM_THREADS='1', XPLAY_TMP=str(ROOT / D / 'prov/tmp'))
names = ['F1_s13_k0', 'F1_s113_k1', 'F1_s13_k1', 'F1_s113_k0', 'F1s_s13_k0', 'F1s_s13_k1', 'F1s_s113_k0', 'F1s_s113_k1']
missing = [n for n in names if not (ROOT / D / 'train' / f'{n}_fleet.pt').exists()]
if missing:
    sys.exit(f'missing fleets {missing}')


def go(n):
    k = n.split('_k')[1]
    with open(ROOT / D / 'prov' / 'run.log', 'a') as f:
        r = subprocess.run(['nice', '-n', '5', 'external_envs/city_runtime/bin/python', '-u', 'scripts/CITY_eval_f1.py', '--spat-arm',
                            f'fcc:{q}:research/city_sim/m3_20261004/prep/prov_rlh{k}_cl.json', '--light', f'RL-H:{k}', '--fleet', f'PL:{D}/train/{n}_fleet.pt',
                            '--seeds', *S, '--tag', f'EV_{n}', '--out', f'{D}/prov'], env=env, stdout=f, stderr=subprocess.STDOUT)
    return n, r.returncode


if __name__ == '__main__':
    with ThreadPoolExecutor(8) as ex:
        res = list(ex.map(go, names))
    bad = [n for n, c in res if c]; print('failed:', bad, flush=True)
    sys.exit(1 if bad else subprocess.run(['external_envs/city_runtime/bin/python', 'scripts/CITY_f1_dev_report.py'], env=env).returncode)
