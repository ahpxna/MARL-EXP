#!/usr/bin/env python3
"""F1 self-checks (PROTOCOL_CITY_F1 §5).  Exit 1 on failure.  KF-1: the F1 trainer with 0 episodes saves a fleet whose evaluation equals the
initial checkpoint's (F0) rows under RL-H:0 with the corrected provider (traffic 0, bit-identical).  KF-2: the trainer's light checkpoint hash
equals RL-H:0's file.  KF-3: provider hash recorded == file.  KF-4: trainer seeds TRAIN only (smoke run of 2 short episodes)."""
import hashlib, json, os, subprocess, sys, tempfile
from pathlib import Path
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); PY = sys.executable; P = ROOT / 'research/city_sim/spat_pilot_20261004'
TB = str(ROOT / 'research/city_sim/m3_20261004/prep/prov_rlh0_cl.json'); F0 = str(P / 'fleets_v11/L11_s13_fleet.pt'); bad = []
KEYS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports'); sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()


def ev(fleet, tag, out):
    subprocess.run([PY, '-u', 'scripts/CITY_eval_f1.py', '--spat-arm', f'fcc:0.1:{TB}', '--light', 'RL-H:0', '--fleet', f'PL:{fleet}', '--seeds', '0', '--tag', tag, '--out', out],
                   check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    return json.loads((Path(out) / f'{tag}.json').read_text())['rows'][0]


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; out = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))
    subprocess.run([PY, '-u', 'scripts/CITY_fleet_train_f1.py', '--seed', '13', '--light-k', '0', '--init', F0, '--table', TB, '--q', '0.1', '--episodes', '0',
                    '--name', 'kf1', '--out', out], check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    a, b = ev(f'{out}/kf1_fleet.pt', 'kf1', out), ev(F0, 'f0', out)
    print('KF-1', {k: a[k] for k in KEYS}); print('    ', {k: b[k] for k in KEYS})
    if any(abs(a[k] - b[k]) > 1e-9 for k in KEYS):
        bad.append('KF-1')
    d = torch.load(f'{out}/kf1_fleet.pt', weights_only=False)
    import scripts.CITY_xplay2 as X2
    if d['light_sha256'] != sha(X2.light_spec('RL-H:0')[1]):
        bad.append('KF-2')
    if d['provider_sha256'] != sha(TB):
        bad.append('KF-3')
    subprocess.run([PY, '-u', 'scripts/CITY_fleet_train_f1.py', '--seed', '13', '--light-k', '0', '--init', F0, '--table', TB, '--q', '0.1', '--episodes', '2', '--smoke',
                    '--name', 'kf4', '--out', out], check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    L = json.loads(Path(out, 'kf4.log.json').read_text())
    if not all(r['seed'] in range(8) for r in L) or len(L) != 2:
        bad.append('KF-4')
    print('KF-4 smoke log:', [(r['ep'], r['seed'], r['decisions'], r['teleports']) for r in L])
    print('F1 CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
