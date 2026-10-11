#!/usr/bin/env python3
"""F1 §0 provider re-selection runner: frozen R10 (dev fleets s13, s113) under RL-H:k (k = 0, 1) with the convention-corrected closed-loop
provider at q in {0.1, 0.2, 0.3, 0.5}, plus R (no SPaT), on DEV (SELECT 100-104 + 200-209); pool 10; then the mechanical selection."""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT = Path('/Users/phanan/cig-amf-main'); os.chdir(ROOT); E = 'research/city_sim/f1_20261004/prov'; P = 'research/city_sim/spat_pilot_20261004'
S = [str(s) for s in [100, 101, 102, 103, 104] + list(range(200, 210))]; env = dict(os.environ, PYTHONHASHSEED='0', OMP_NUM_THREADS='1', XPLAY_TMP=str(ROOT / E / 'tmp'))
J = []
for k in (0, 1):
    tb = f'research/city_sim/m3_20261004/prep/prov_rlh{k}_cl.json'
    for fl in ('s13', 's113'):
        F = f'PL:{P}/fleets_v11/L11_{fl}_fleet.pt'; J.append(('none', k, F, f'R_k{k}_{fl}'))
        for q in ('0.1', '0.2', '0.3', '0.5'):
            J.append((f'fcc:{q}:{tb}', k, F, f'Fc{q}_k{k}_{fl}'))


def go(j):
    arm, k, F, tag = j
    with open(ROOT / E / 'run.log', 'a') as f:
        r = subprocess.run(['nice', '-n', '5', 'external_envs/city_runtime/bin/python', '-u', 'scripts/CITY_eval_f1.py', '--spat-arm', arm, '--light', f'RL-H:{k}',
                            '--fleet', F, '--seeds', *S, '--tag', tag, '--out', E], env=env, stdout=f, stderr=subprocess.STDOUT)
    return tag, r.returncode


if __name__ == '__main__':
    with ThreadPoolExecutor(10) as ex:
        res = list(ex.map(go, J))
    bad = [t for t, c in res if c]; print(len(J), 'jobs, failed:', bad, flush=True); sys.exit(1 if bad else 0)
