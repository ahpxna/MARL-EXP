#!/usr/bin/env python3
"""M2 runner (PROTOCOL_CITY_M2_COMPAT_20261004): 34 evaluation jobs x 20 traffic seeds (470-489), at most 10 at a time, then the report."""
import os, subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; os.chdir(ROOT)
PY = 'external_envs/city_runtime/bin/python'; P = 'research/city_sim/spat_pilot_20261004'; E = f'{P}/m2/eval'; S = [str(s) for s in range(470, 490)]
env = dict(os.environ, PYTHONHASHSEED='0', OMP_NUM_THREADS='1', XPLAY_TMP=str(ROOT / E / 'tmp'))
(ROOT / E / 'tmp').mkdir(parents=True, exist_ok=True)
J = [['scripts/CITY_eval4.py', '--light', 'FT', '--fleet', 'L-ACT:0', '--guard', 'always', '--tag', 'OFF_FT'],
     ['scripts/CITY_eval4_sigma.py', '--sigma', '0.3', '--light', 'FT', '--fleet', 'L-ACT:0', '--guard', 'always', '--tag', 'S03_FT']]
for k in range(4):
    J += [['scripts/CITY_eval6_m2.py', '--spat-label', 'naive', '--light', 'FT', '--fleet', f'ESLD:{P}/lane_d/theta_s{k + 2}.json', '--tag', f'F0a_FT_s{k + 2}'],
          ['scripts/CITY_eval6_m2.py', '--spat-label', 'naive', '--light', 'FT', '--fleet', f'PL:{P}/fleets_v11/L11_s{213 + 100 * k}_fleet.pt', '--tag', f'F0b_FT_s{213 + 100 * k}'],
          ['scripts/CITY_eval4.py', '--light', f'RL-H:{k}', '--fleet', 'L-ACT:0', '--guard', 'always', '--tag', f'OFF_RLH{k}'],
          ['scripts/CITY_eval4_sigma.py', '--sigma', '0.3', '--light', f'RL-H:{k}', '--fleet', 'L-ACT:0', '--guard', 'always', '--tag', f'S03_RLH{k}']]
    for arm in ('naive', 'labelled'):
        J += [['scripts/CITY_eval6_m2.py', '--spat-label', arm, '--light', f'RL-H:{k}', '--fleet', f'ESLD:{P}/lane_d/theta_s{k + 2}.json', '--tag', f'F0a_RLH{k}_{arm}'],
              ['scripts/CITY_eval6_m2.py', '--spat-label', arm, '--light', f'RL-H:{k}', '--fleet', f'PL:{P}/fleets_v11/L11_s{213 + 100 * k}_fleet.pt', '--tag', f'F0b_RLH{k}_{arm}']]


def go(args):
    with open(ROOT / E / 'run.log', 'a') as f:
        r = subprocess.run(['nice', '-n', '5', PY, '-u', *args, '--seeds', *S, '--out', E], env=env, stdout=f, stderr=subprocess.STDOUT)
    return args[-1], r.returncode


if __name__ == '__main__':
    with ThreadPoolExecutor(10) as ex:
        res = list(ex.map(go, J))
    bad = [t for t, c in res if c]; print(f'{len(J)} jobs, failed: {bad}', flush=True)
    subprocess.run([PY, 'scripts/CITY_m2_report.py'], env=env)
