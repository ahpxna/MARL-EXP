#!/usr/bin/env python3
"""M3 DEV evaluation runner (PROTOCOL_CITY_M3 §6 + A1): every E checkpoint and every comparator setting on DEV traffic (SELECT 100-104 +
200-209) with dev fleets L11_s13 / L11_s113, light seeds k = 0, 1; σ* rows for the light-side cost.  At most 10 jobs at a time.  Exits
non-zero if any job fails or any trained checkpoint is missing (S7), then runs the DEV report."""
import os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
ROOT = Path('/Users/phanan/cig-amf-main'); os.chdir(ROOT)
D = 'research/city_sim/m3_20261004'; E = f'{D}/dev'; P = 'research/city_sim/spat_pilot_20261004'; PY = 'external_envs/city_runtime/bin/python'
S = [str(s) for s in [100, 101, 102, 103, 104] + list(range(200, 210))]
FL = {'s13': f'PL:{P}/fleets_v11/L11_s13_fleet.pt', 's113': f'PL:{P}/fleets_v11/L11_s113_fleet.pt'}
SIG = ['--base-sigma', '0.3', '--fleet', 'L-ACT:0', '--guard', 'always']
ARMS_E = ['E_E0q_lam0', 'E_E0p_lam0'] + [f'E_{a}_lam{l}' for a in ('uniform', 'eta', 'active', 'receiver') for l in (1, 4)]
J = []
for k in (0, 1):
    prov = f'{D}/prep/prov_rlh{k}_cl.json'
    missing = [a for a in ARMS_E if not (ROOT / D / 'train' / f'{a}_k{k}.pt').exists()]
    if missing:
        sys.exit(f'S7: missing checkpoints for k{k}: {missing}')
    J.append(('none', f'RL-H:{k}', SIG, f'R_k{k}_sig'))
    for a in ARMS_E:
        J.append(('none', f'M3E:{D}/train/{a}_k{k}.pt', SIG, f'{a}_k{k}_sig'))
    for w in (5, 10, 15):
        J.append(('none', f'M3WC:{k}:{w}', SIG, f'WC{w}_k{k}_sig'))
    for fl, spec in FL.items():
        F = ['--fleet', spec]
        J.append(('none', f'RL-H:{k}', F, f'R_k{k}_{fl}'))
        for a in ARMS_E:
            J.append(('deployed', f'M3E:{D}/train/{a}_k{k}.pt', F, f'{a}_k{k}_{fl}'))
        for q in ('0.1', '0.2', '0.3', '0.5'):
            J.append((f'fc:{q}:{prov}', f'RL-H:{k}', F, f'Fq{q}_k{k}_{fl}'))
        J.append((f'D:{k}:{prov}', f'RL-H:{k}', F, f'D_k{k}_{fl}'))
        for w in (5, 10, 15):
            J.append((f'commit:{prov}', f'M3WC:{k}:{w}', F, f'WC{w}_k{k}_{fl}'))
        for w in (10, 15):
            J.append((f'commit:{prov}', f'M3B:{k}:{w}', F, f'B{w}_k{k}_{fl}'))
for g in (10, 15, 20, 25, 30):
    J.append(('program', f'M3CYC:{g}', SIG, f'CYC{g}_sig'))
    for fl, spec in FL.items():
        J.append(('program', f'M3CYC:{g}', ['--fleet', spec], f'CYC{g}_{fl}'))
env = dict(os.environ, PYTHONHASHSEED='0', OMP_NUM_THREADS='1', XPLAY_TMP=str(ROOT / E / 'tmp'))


def go(j):
    arm, light, fl, tag = j
    with open(ROOT / E / 'run.log', 'a') as f:
        r = subprocess.run(['nice', '-n', '5', PY, '-u', 'scripts/CITY_eval_m3.py', '--spat-arm', arm, '--light', light, *fl, '--seeds', *S, '--tag', tag, '--out', E],
                           env=env, stdout=f, stderr=subprocess.STDOUT)
    return tag, r.returncode


if __name__ == '__main__':
    (ROOT / E / 'tmp').mkdir(parents=True, exist_ok=True); print(len(J), 'jobs', flush=True)
    with ThreadPoolExecutor(10) as ex:
        res = list(ex.map(go, J))
    bad = [t for t, c in res if c]; print('failed:', bad, flush=True)
    if bad:
        sys.exit(1)
    sys.exit(subprocess.run([PY, 'scripts/CITY_m3_dev_report.py'], env=env).returncode)
