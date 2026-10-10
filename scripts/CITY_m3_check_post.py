#!/usr/bin/env python3
"""M3 self-checks for evaluation and comparators (Amendment A1): S1, S2, S4, S5, S6, S13.  Exit 1 on failure.  Traffic 0, END s.
  S1   a 0-episode E checkpoint (widened RL-H:k + the closed-loop provider) with spat 'deployed' == RL-H:k with fc:0.5:<same table>
  S2   M3WC:k:0 with commit:<table> == RL-H:k with fc:0.5:<table>;  M3B:k:10 with σ* cars (no fleet requests) == RL-H:k with σ* cars
  S4   CITY_spat_forecast.fit on the M2b TRAIN traces reproduces m2b/forecast_rlh<k>.json exactly
  S5   M3WC:k:10: commitments > 0 and violations == 0 (promised green end == observed)
  S6   online (phase, spent) read by a probe inside an M3E evaluation == the recorded trace at the same seconds (no future access)
  S13  every trained checkpoint present: table_sha256 == sha of its saved table; rlh / fleet hashes match the files; training seeds TRAIN only"""
import hashlib, json, os, subprocess, sys, tempfile
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); PY = sys.executable
D = ROOT / 'research/city_sim/m3_20261004'; P = ROOT / 'research/city_sim/spat_pilot_20261004'; K = 0; END = os.environ.get('M3CHECK_END', '1800')
FL = f'PL:{P}/fleets_v11/L11_s13_fleet.pt'; KEYS = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports'); bad = []
PROV = str(D / f'prep/prov_rlh{K}_cl.json')


def run(args, tag, out, seed=0, extra=()):
    env = dict(os.environ, M3_END=END)
    subprocess.run([PY, '-u', 'scripts/CITY_eval_m3.py', *args, '--seeds', str(seed), '--tag', tag, '--out', out, *extra], check=True, cwd=ROOT, stdout=subprocess.DEVNULL, env=env)
    return json.loads((Path(out) / f'{tag}.json').read_text())['rows'][0], json.loads((Path(out) / f'{tag}_m3.json').read_text())


def same(nm, x, y):
    print(nm, {k: x[k] for k in KEYS}); print(' ' * len(nm), {k: y[k] for k in KEYS})
    if any(abs(x[k] - y[k]) > 1e-9 for k in KEYS):
        bad.append(f'{nm} identity')


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; out = tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))
    # S1
    subprocess.run([PY, '-u', 'scripts/CITY_m3_train_E.py', 'train', str(K), 'E0p', '0', out, '--prep', str(D / 'prep'), '--episodes', '0'], check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    ck0 = Path(out) / f'E_E0p_lam0_k{K}.pt'
    a, _ = run(['--spat-arm', 'deployed', '--light', f'M3E:{ck0}', '--fleet', FL], 's1_e', out)
    b, _ = run(['--spat-arm', f'fc:0.5:{PROV}', '--light', f'RL-H:{K}', '--fleet', FL], 's1_r', out)
    same('S1', a, b)
    # S2
    c, _ = run(['--spat-arm', f'commit:{PROV}', '--light', f'M3WC:{K}:0', '--fleet', FL], 's2_wc0', out); same('S2a', c, b)
    s3 = ['--fleet', 'human']                                        # protocol S2: B-ETA with NO fleet (σ* cars are fleet members and do request)
    d, _ = run(['--spat-arm', 'none', '--light', f'M3B:{K}:10', *s3], 's2_b', out); e, _ = run(['--spat-arm', 'none', '--light', f'RL-H:{K}', *s3], 's2_r', out)
    same('S2b', d, e)
    # S4
    import scripts.CITY_spat_forecast as FC
    T = FC.fit([str(P / f'm2b/traces/rlh{K}_s{s}.npz') for s in range(8)]); ref = json.loads((P / f'm2b/forecast_rlh{K}.json').read_text())
    if json.dumps(T, sort_keys=True) != json.dumps(ref, sort_keys=True):
        bad.append('S4 refit != M2b table')
    print('S4 refit reproduces the M2b table:', json.dumps(T, sort_keys=True) == json.dumps(ref, sort_keys=True))
    # S5
    _, sc = run(['--spat-arm', f'commit:{PROV}', '--light', f'M3WC:{K}:10', '--fleet', FL], 's5_wc10', out)
    ps = sc['per_seed']['0']; print('S5 commitments', ps['commits'], 'violations', ps['violations'], 'censored', ps.get('censored'), 'forecast/commit query MAE', ps.get('mae'))
    if ps['commits'] == 0 or ps['violations'] != 0:
        bad.append('S5 commitment violations')
    # S6: probe inside an M3E evaluation vs its own --record trace
    rec = Path(out) / 's6_s{seed}.npz'
    probe = ('import scripts.CITY_eval_m3 as W, scripts.CITY_eval4 as E4, scripts.CITY_env as CE, json, sys\n'
             'seen=[]\n_s=W.M.LightE.step\n'
             'def st(self,t):\n    _s(self,t)\n    ls=CE.ls\n    if int(t)%7==0: seen.extend((int(t),x,ls.trafficlight.getPhase(x),ls.trafficlight.getSpentDuration(x)) for x in ls.trafficlight.getIDList())\n'
             'W.M.LightE.step=st\nimport argparse\n'
             f'a=argparse.Namespace(light="M3E:{ck0}",light_obs="raw",light_fallback="none",fleet="{FL}",guard="none",record="{rec}",replay=None,replay_dir=None,discharge=False,delay_trace=False,swap_at=None,swap_light=None,swap_fleet=None,seeds=[0],smoke=False,tag="s6",out="{out}")\n'
             f'E4.run(a,0,{END})\njson.dump(seen,open("{out}/s6_seen.json","w"))\n')
    subprocess.run([PY, '-c', probe, '--spat-arm', 'deployed'], check=True, cwd=ROOT, stdout=subprocess.DEVNULL)
    seen = json.load(open(f'{out}/s6_seen.json')); z = np.load(str(rec).replace('{seed}', '0'), allow_pickle=True); ids = [str(x) for x in z['ids']]
    mism = sum(1 for t, tid, ph, sp in seen if t - 1 < len(z['phases']) and (int(z['phases'][t - 1, ids.index(tid)]) != ph or abs(float(z['spent'][t - 1, ids.index(tid)]) - sp) > 1e-9))
    print(f'S6 {len(seen)} reads, {mism} mismatches')
    if mism or not seen:
        bad.append('S6 online vs recorded')
    # S13
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    import torch
    for f in sorted((D / 'train').glob('E_*.pt')):
        d = torch.load(f, weights_only=False); log = json.loads((D / 'train' / (f.stem + '.log.json')).read_text())
        ok = (hashlib.sha256(json.dumps(d['table'], sort_keys=True).encode()).hexdigest() == d['table_sha256'] and sha(d['rlh_ckpt']) == d['rlh_sha256']
              and sha(d['fleet_ckpt']) == d['fleet_sha256'] and all(r['seed'] in range(8) for r in log) and len(log) == d['episodes'])
        print('S13', f.name, 'OK' if ok else 'FAIL')
        if not ok:
            bad.append(f'S13 {f.name}')
    print('M3 POST CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
