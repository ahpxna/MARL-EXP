#!/usr/bin/env python3
"""R7 identity checks (Amendment R7; 04/10/2026).  Exit 1 on any failure.
  K7-1: base σ 0.3 + a NEVER-FIRING theta (0, 0, -1) == the σ-family σ 0.3 fleet (CITY_eval4_sigma mechanism) on traffic SEED
  K7-2: base σ 0.5 + GLOSA == plain eval6 GLOSA on traffic SEED (the default Krauss σ is 0.5)
  K7-3: the search module's episode_s(None) and episode_s(theta0) reproduce the K7-1 σ* rows and the K7-1-style GLOSA∘σ* eval row
Each compares city / agent / human time loss, agent fuel and teleports (eval rows), |diff| <= 1e-9."""
import argparse, json, os, subprocess, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
SEED = int(os.environ.get('SBCHECK_SEED', '0')); PY = sys.executable
KEYS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports')


def run(args, tag, out):
    subprocess.run([PY, '-u', *args, '--light', 'FT', '--seeds', str(SEED), '--tag', tag, '--out', out], check=True, cwd=ROOT,
                   stdout=subprocess.DEVNULL)
    return json.loads((Path(out) / f'{tag}.json').read_text())['rows'][0]


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; bad = []
    out = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP')); th = Path(out) / 'never.json'; th.write_text(json.dumps(dict(theta=[0.0, 0.0, -1.0])))
    a = run(['scripts/CITY_eval6_sbase.py', '--base-sigma', '0.3', '--fleet', f'ES:{th}'], 'sb03_never', out)
    b = run(['scripts/CITY_eval4_sigma.py', '--sigma', '0.3', '--fleet', 'L-ACT:0', '--guard', 'always'], 's03', out)
    c = run(['scripts/CITY_eval6_sbase.py', '--base-sigma', '0.5', '--fleet', 'GLOSA'], 'sb05_glosa', out)
    d = run(['scripts/CITY_eval6.py', '--fleet', 'GLOSA'], 'glosa', out)
    g = run(['scripts/CITY_eval6_sbase.py', '--base-sigma', '0.3', '--fleet', 'GLOSA'], 'sb03_glosa', out)
    for nm, x, y in (('K7-1', a, b), ('K7-2', c, d)):
        print(nm, {k: x[k] for k in KEYS}); print(' ' * len(nm), {k: y[k] for k in KEYS})
        if any(abs(x[k] - y[k]) > 1e-9 for k in KEYS):
            bad.append(f'{nm} identity')
    import scripts.CITY_es_glosa_sbase as S
    os.environ.setdefault('XPLAY_TMP', out)
    e0, e1 = S.episode_s(None, SEED), S.episode_s([0.0, 0.0, 200.0], SEED)
    print('K7-3 search σ*:', e0, ' eval:', (b['fuel_agent'], b['timeloss_agent'], b['timeloss_human'], b['teleports']))
    print('K7-3 search θ0:', e1, ' eval:', (g['fuel_agent'], g['timeloss_agent'], g['timeloss_human'], g['teleports']))
    for e, r in ((e0, b), (e1, g)):
        if any(abs(u - v) > 1e-6 for u, v in zip(e, (r['fuel_agent'], r['timeloss_agent'], r['timeloss_human'], r['teleports']))):
            bad.append('K7-3 search episode vs eval row')
    print(f'GLOSA∘σ* vs σ* on traffic {SEED}: fuel {100 * (g["fuel_agent"] / b["fuel_agent"] - 1):+.2f} %, agent TL {g["timeloss_agent"] - b["timeloss_agent"]:+.2f}, '
          f'human TL {g["timeloss_human"] - b["timeloss_human"]:+.2f}  (smoke only; not an endpoint)')
    print('SBASE CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
