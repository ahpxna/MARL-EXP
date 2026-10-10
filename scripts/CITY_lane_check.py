#!/usr/bin/env python3
"""R8 identity check KL (Amendment R8; 04/10/2026).  Exit 1 on failure.  On traffic 0 (FT, 5400 s, eval rows):
  KL-1  GLOSAL0:0.3 (lane condition OFF, σ* base) == CITY_eval6_sbase --base-sigma 0.3 --fleet GLOSA   (GLOSA∘σ*)
  KL-2  GLOSAL0:0.5 (lane condition OFF, default base) == CITY_eval6 --fleet GLOSA
Then (not a pass/fail item) GLOSAL:0.3 on traffic 0 is printed with the lane-release count, as a smoke of the active condition."""
import json, os, subprocess, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; PY = sys.executable
KEYS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports')


def run(args, tag, out):
    subprocess.run([PY, '-u', *args, '--light', 'FT', '--seeds', '0', '--tag', tag, '--out', out], check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    return json.loads((Path(out) / f'{tag}.json').read_text())['rows'][0]


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; bad = []; out = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))
    pairs = (('KL-1', run(['scripts/CITY_eval6_lane.py', '--fleet', 'GLOSAL0:0.3'], 'l0_03', out),
              run(['scripts/CITY_eval6_sbase.py', '--base-sigma', '0.3', '--fleet', 'GLOSA'], 'sb03', out)),
             ('KL-2', run(['scripts/CITY_eval6_lane.py', '--fleet', 'GLOSAL0:0.5'], 'l0_05', out), run(['scripts/CITY_eval6.py', '--fleet', 'GLOSA'], 'g05', out)))
    for nm, x, y in pairs:
        print(nm, {k: x[k] for k in KEYS}); print(' ' * len(nm), {k: y[k] for k in KEYS})
        if any(abs(x[k] - y[k]) > 1e-9 for k in KEYS):
            bad.append(f'{nm} identity')
    z = run(['scripts/CITY_eval6_lane.py', '--fleet', 'GLOSAL:0.3'], 'l1_03', out)
    print('smoke GLOSAL:0.3 traffic 0:', {k: z[k] for k in KEYS}, f'(vs GLOSA∘σ*: fuel {100 * (z["fuel_agent"] / pairs[0][2]["fuel_agent"] - 1):+.2f} %)')
    print('LANE CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
