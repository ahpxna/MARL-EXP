#!/usr/bin/env python3
"""KF11-2 (PROTOCOL_CITY_WAVE11_FORL_20261005, Amendment A2): forecast-branch self-check of the FoRL SPaT provider.  A CONSISTENT stub policy
(switch at the first decision whose green has run >= SW s; forecast entry i = 1 iff spent + DT_L * i >= SW) replaces the FoRL network, so every
published forecast is honoured; the provider's forecast-branch answers must then equal the realised phase trace exactly (offset c = 0, as for
every provider), as must the yellow branch.  It failed on provider v1 (every ttr answer +1 s) and passes on v2.
Usage: CITY_w11_stubcheck.py <out dir> [SW]      (one 600-s smoke run, fleet L11_s213, seed 660, then CITY_w11_check.py)"""
import os, runpy, subprocess, sys
from pathlib import Path
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
import scripts.CITY_forl as FO  # noqa: E402
D = Path(sys.argv[1]).resolve(); SW = float(sys.argv[2]) if len(sys.argv) > 2 else 15.0; _load = FO.load
for sub in ('served', 'rec'):
    (D / sub).mkdir(parents=True, exist_ok=True)
(D / 'STUB.pt').write_text(f'consistent stub, SW {SW}\n')


class Stub:
    def dist(self, X):
        s = X[:, 6] * 60.0; P = torch.zeros(X.shape[0], FO.L, 2)
        for i in range(FO.L):
            sw = (s + FO.DT_L * i >= SW - 1e-3).float(); P[:, i, 1] = sw; P[:, i, 0] = 1 - sw
        return torch.distributions.Categorical(probs=P)

    def value(self, X):
        return torch.zeros(X.shape[0])


if __name__ == '__main__':
    if not (D / 'served' / 'KF_served_s660.npz').exists():
        FO.load = lambda p: Stub() if p.endswith('STUB.pt') else _load(p)
        os.environ['W10_LOG'] = str(D / 'served')
        sys.argv = ['scripts/CITY_w10_run.py', 'serve', 'scripts/CITY_eval_forl.py', '--forl-spat', 'on', '--light', f'FORL:{D}/STUB.pt', '--fleet',
                    'PL:research/city_sim/spat_pilot_20261004/fleets_v11/L11_s213_fleet.pt', '--seeds', '660', '--smoke', '--record',
                    f'{D}/rec/KF_s{{seed}}.npz', '--tag', 'KF', '--out', str(D)]
        runpy.run_path(str(ROOT / 'scripts/CITY_w10_run.py'), run_name='__main__')
    r = subprocess.run([sys.executable, str(ROOT / 'scripts/CITY_w11_check.py'), str(D / 'served/KF_served_s660.npz'), str(D / 'rec/KF_s660.npz')],
                       capture_output=True, text=True)
    line = r.stdout.strip(); mae = float(line.split('forecast-branch MAE ')[1].split(' ')[0]); ok = r.returncode == 0 and mae == 0.0
    out = f'KF11-2 (stub SW {SW:g} s): {line} -> {"PASS" if ok else "FAIL"}'; (D / 'kf11_2.txt').write_text(out + '\n'); print(out); sys.exit(0 if ok else 1)
