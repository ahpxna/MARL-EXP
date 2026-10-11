#!/usr/bin/env python3
"""F1 DEV training (PROTOCOL_CITY_F1 §2): reads prov/locked.json (q); F1 fine-tunes from L11_s13 / L11_s113 under RL-H:k ((s13,k0), (s113,k1),
(s13,k1), (s113,k0)); F1-scratch from the zero-init residual (seeds 13 / 113 x k 0 / 1); 200 episodes each; provider = prov_rlh<k>_cl.json
(convention-corrected at runtime); 8 runs in parallel."""
import json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT = Path('/Users/phanan/cig-amf-main'); os.chdir(ROOT); D = 'research/city_sim/f1_20261004'; P = 'research/city_sim/spat_pilot_20261004'
q = json.loads((ROOT / D / 'prov/locked.json').read_text())['q']; env = dict(os.environ, PYTHONHASHSEED='0', OMP_NUM_THREADS='1')
J = [(f'F1_s{fl}_k{k}', int(fl), k, f'{P}/fleets_v11/L11_s{fl}_fleet.pt') for fl, k in (('13', 0), ('113', 1), ('13', 1), ('113', 0))]
J += [(f'F1s_s{sd}_k{k}', sd, k, 'scratch') for sd in (13, 113) for k in (0, 1)]


def go(j):
    name, seed, k, init = j
    with open(ROOT / D / 'train' / f'{name}.out', 'w') as f:
        r = subprocess.run(['nice', '-n', '5', 'external_envs/city_runtime/bin/python', '-u', 'scripts/CITY_fleet_train_f1.py', '--seed', str(seed), '--light-k', str(k),
                            '--init', init, '--table', f'research/city_sim/m3_20261004/prep/prov_rlh{k}_cl.json', '--q', str(q), '--episodes', '200',
                            '--name', name, '--out', f'{D}/train'], env=env, stdout=f, stderr=subprocess.STDOUT)
    return name, r.returncode


if __name__ == '__main__':
    (ROOT / D / 'train').mkdir(parents=True, exist_ok=True); print('locked q', q, flush=True)
    with ThreadPoolExecutor(8) as ex:
        res = list(ex.map(go, J))
    bad = [n for n, c in res if c]; print(len(J), 'runs, failed:', bad, flush=True); sys.exit(1 if bad else 0)
