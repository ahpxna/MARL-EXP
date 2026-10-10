#!/usr/bin/env python3
"""R10 checks (Amendment R10; 04/10/2026).  Exit 1 on failure.
  K10-1 identity: a fresh zero-initialised V9.NetR in CarPPOL, deterministic evaluation, equals GLOSAL:0.3 (GLOSA-L∘σ*) on traffic 0 (eval rows)
  K10-2 training-mode smoke (END s, traffic 0): segments are one vehicle each; stored log-prob == net.dist(obs).log_prob(u); every
        command in [0, v_allowed]; GAE equals the naive recursion; dense credit count > 0; no fleet-caused teleports in the smoke"""
import json, os, subprocess, sys, tempfile
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); PY = sys.executable
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_fleet_v9 as V9  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
from scripts.CITY_v8_check import naive_gae  # noqa: E402
KEYS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports'); END = int(os.environ.get('V11CHECK_END', '900'))


def run(args, tag, out):
    subprocess.run([PY, '-u', *args, '--light', 'FT', '--seeds', '0', '--tag', tag, '--out', out], check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    return json.loads((Path(out) / f'{tag}.json').read_text())['rows'][0]


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1); bad = []; out = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))
    f = Path(out) / 'fresh_fleet.pt'; torch.save(dict(net=V9.NetR(7), kind='ppo_residual_glosaL', spat='on'), f)
    a, b = run(['scripts/CITY_eval6_v11.py', '--fleet', f'PL:{f}'], 'pl0', out), run(['scripts/CITY_eval6_lane.py', '--fleet', 'GLOSAL:0.3'], 'gl', out)
    print('K10-1 PL(delta=0):', {k: a[k] for k in KEYS}); print('K10-1 GLOSAL:0.3 :', {k: b[k] for k in KEYS})
    if any(abs(a[k] - b[k]) > 1e-9 for k in KEYS):
        bad.append('K10-1 identity')
    net = V9.NetR(13); cars = V11.CarPPOL(net, Q7.RHO, 0, deterministic=False, record=True)
    m = CE.run_episode(Q7.NET_S, Q7.ROU.format(0), 0, None, cars, end=END); cars.finish(); segs = [s for s in cars.segments if s['dec']]
    allD = [d for s in segs for d in s['dec']]
    if not allD:
        bad.append('K10-2 no decisions')
    else:
        if any(len({d['vid'] for d in s['dec']}) != 1 for s in segs):
            bad.append('K10-2 segments')
        O = torch.as_tensor(np.stack([d['obs'] for d in allD])); U = torch.as_tensor(np.array([d['u'] for d in allD], np.float32))
        with torch.no_grad():
            lp = net.dist(O).log_prob(U).numpy()
        if np.max(np.abs(lp - np.array([d['logp'] for d in allD]))) > 1e-4:
            bad.append('K10-2 log-prob')
        if any(d['cmd'] < -1e-9 for d in allD):
            bad.append('K10-2 command range')
        g = V8.gae(cars.segments, net); A = np.concatenate([naive_gae(s, net)[0] for s in segs])
        if g is None or np.max(np.abs(g[3] - A)) > 1e-4:
            bad.append('K10-2 GAE')
        if cars.stats['dense_n'] == 0:
            bad.append('K10-2 no dense credit')
    print(f'K10-2: {len(allD)} decisions, {len(segs)} segments, teleports {m["teleports"]}, mean reward/decision {np.mean([d["rew"] for d in allD]):.3f}; stats {cars.stats}')
    if m['teleports'] > 0:
        bad.append('K10-2 fleet teleports in the smoke')
    print('V11 CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
