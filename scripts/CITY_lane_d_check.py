#!/usr/bin/env python3
"""R9 identity checks (Amendment R9; 04/10/2026).  Exit 1 on failure.  Traffic 0, FT, 5400 s, eval rows (|diff| <= 1e-9):
  KLD-1  ESLD theta_L = (0, 0, 200, 200)  == GLOSAL:0.3 (GLOSA-L∘σ*)
  KLD-2  ESLD (0, 0, 200, 0)              == CITY_eval6_sbase --base-sigma 0.3 --fleet GLOSA (GLOSA∘σ*)
  KLD-3  the search module's episode(theta_L) reproduces the KLD-1 eval row (fuel / agent TL / human TL / teleports)"""
import json, os, subprocess, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); PY = sys.executable
KEYS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports')


def run(args, tag, out):
    subprocess.run([PY, '-u', *args, '--light', 'FT', '--seeds', '0', '--tag', tag, '--out', out], check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    return json.loads((Path(out) / f'{tag}.json').read_text())['rows'][0]


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; bad = []; out = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))
    tl, t0 = Path(out) / 'tl.json', Path(out) / 't0.json'
    tl.write_text(json.dumps(dict(theta=[0.0, 0.0, 200.0, 200.0]))); t0.write_text(json.dumps(dict(theta=[0.0, 0.0, 200.0, 0.0])))
    a, b = run(['scripts/CITY_eval6_lane2.py', '--fleet', f'ESLD:{tl}'], 'ld_L', out), run(['scripts/CITY_eval6_lane.py', '--fleet', 'GLOSAL:0.3'], 'gl', out)
    c, d = run(['scripts/CITY_eval6_lane2.py', '--fleet', f'ESLD:{t0}'], 'ld_0', out), run(['scripts/CITY_eval6_sbase.py', '--base-sigma', '0.3', '--fleet', 'GLOSA'], 'gs', out)
    for nm, x, y in (('KLD-1', a, b), ('KLD-2', c, d)):
        print(nm, {k: x[k] for k in KEYS}); print(' ' * len(nm), {k: y[k] for k in KEYS})
        if any(abs(x[k] - y[k]) > 1e-9 for k in KEYS):
            bad.append(f'{nm} identity')
    import scripts.CITY_glosa_lane_d as LD
    os.environ.setdefault('XPLAY_TMP', out); e = LD.episode([0.0, 0.0, 200.0, 200.0], 0)
    print('KLD-3 search episode:', e, ' eval:', (a['fuel_agent'], a['timeloss_agent'], a['timeloss_human'], a['teleports']))
    if any(abs(u - v) > 1e-6 for u, v in zip(e, (a['fuel_agent'], a['timeloss_agent'], a['timeloss_human'], a['teleports']))):
        bad.append('KLD-3 search episode vs eval row')
    print('LANE_D CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
