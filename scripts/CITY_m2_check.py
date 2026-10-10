#!/usr/bin/env python3
"""M2 checks (PROTOCOL_CITY_M2_COMPAT_20261004).  Exit 1 on failure.  Traffic 0, 5400 s, eval rows (|diff| <= 1e-9):
  KM2-1  FT: F0a (ESLD theta_s2) naive == labelled
  KM2-2  RL-H:0: F0a labelled == the σ* fleet (eval4_sigma 0.3, guard always) -> the fleet never commands without published SPaT
  KM2-3  RL-H:0: the naive arm sees >= 1 valid SPaT (else the mislabelling concern is void; reported, not a failure)"""
import json, os, subprocess, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; PY = sys.executable; TH = 'research/city_sim/spat_pilot_20261004/lane_d/theta_s2.json'
KEYS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports')


def run(args, tag, out, light):
    subprocess.run([PY, '-u', *args, '--light', light, '--seeds', '0', '--tag', tag, '--out', out], check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    return json.loads((Path(out) / f'{tag}.json').read_text())['rows'][0]


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; bad = []; out = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))
    m2 = lambda arm: ['scripts/CITY_eval6_m2.py', '--spat-label', arm, '--fleet', f'ESLD:{TH}']
    a, b = run(m2('naive'), 'ft_naive', out, 'FT'), run(m2('labelled'), 'ft_lab', out, 'FT')
    c = run(m2('labelled'), 'rl_lab', out, 'RL-H:0')
    d = run(['scripts/CITY_eval4_sigma.py', '--sigma', '0.3', '--fleet', 'L-ACT:0', '--guard', 'always'], 'rl_s03', out, 'RL-H:0')
    e = run(m2('naive'), 'rl_naive', out, 'RL-H:0')
    for nm, x, y in (('KM2-1', a, b), ('KM2-2', c, d)):
        print(nm, {k: x[k] for k in KEYS}); print(' ' * len(nm), {k: y[k] for k in KEYS})
        if any(abs(x[k] - y[k]) > 1e-9 for k in KEYS):
            bad.append(f'{nm} identity')
    sp = {t: json.loads((Path(out) / f'{t}_spat.json').read_text()) for t in ('ft_naive', 'rl_lab', 'rl_naive')}
    print('spat counts:', sp)
    print('KM2-3 naive under RL-H:0 valid SPaT calls:', sp['rl_naive']['valid'], '(mislabelling concern', 'REAL' if sp['rl_naive']['valid'] > 0 else 'VOID', ')')
    print('smoke RL-H:0 naive F0a vs σ*: fuel', f"{100 * (e['fuel_agent'] / d['fuel_agent'] - 1):+.2f} %, agent TL {e['timeloss_agent'] - d['timeloss_agent']:+.2f}, human TL {e['timeloss_human'] - d['timeloss_human']:+.2f} (not an endpoint)")
    print('M2 CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
