#!/usr/bin/env python3
"""W6-5 M2-L helpers (PROTOCOL_CITY_WAVE6_20261005).
  stage0 <dir>          L1 family choice on DEV 600-605 with SUMO cars: rows <dir>/S0_<family>_<i>.json and S0_RLH_t<k>.json; lowest mean
                        city TL wins; 'upgrade' iff (L1 - RL-H) city TL one-sided 95 % upper < 0 (light seeds resampled per family, traffic
                        paired); writes <dir>/stage0.json with the family, its light specs and tags.
  fit <featdir> <out>   forecast table of one L1 light from its 8 TRAIN feature logs (CITY_spat_forecast.fit; c2 augmentation is applied
                        by make_spat_c2 at use)."""
import json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
FAM = {'RL-J': [f'RL-J:{t}' for t in range(4)], 'SIM-delay': [f'SIM-delay:{k}' for k in range(4)], 'SIM-halt': [f'SIM-halt:{k}' for k in range(4)],
       'ALT-halt': [f'ALT-halt:{k}' for k in range(4)]}
import os  # noqa: E402
S0 = [int(x) for x in os.environ['W6_S0'].split(',')] if os.environ.get('W6_S0') else list(range(600, 606)); B = 2000


def stage0(d):
    from scripts.CITY_w6_validation import rows, require_panel
    d = Path(d); Rt = rows(d)
    keys = [f'S0_RLH_t{k}' for k in (4,5,6,7,8)] + [f'S0_{fam}_{i}' for fam,sp in FAM.items() for i in range(len(sp))]
    require_panel(Rt,keys,S0,metrics=('timeloss',))
    ref = np.array([[Rt[f'S0_RLH_t{k}'][s]['timeloss'] for s in S0] for k in (4, 5, 6, 7, 8)])
    rng = np.random.default_rng(0); res = {}
    for fam, specs in FAM.items():
        X = np.array([[Rt[f'S0_{fam}_{i}'][s]['timeloss'] for s in S0] for i in range(len(specs))])
        v = []
        for _ in range(B):
            ia = rng.integers(0, len(X), len(X)); ib = rng.integers(0, len(ref), len(ref)); js = rng.integers(0, len(S0), len(S0))
            v.append(X[np.ix_(ia, js)].mean() - ref[np.ix_(ib, js)].mean())
        res[fam] = dict(mean_city_tl=float(X.mean()), diff_vs_rlh=float(X.mean() - ref.mean()), up95=float(np.percentile(v, 95)), lo2=float(np.percentile(v, 2.5)), hi2=float(np.percentile(v, 97.5)))
    fam = min(res, key=lambda f: res[f]['mean_city_tl']); up = res[fam]['up95'] < 0
    out = dict(family=fam, specs=FAM[fam], lights=[f'j{i}' for i in range(len(FAM[fam]))], label='DEV-selected candidate (upgrade must be checked on confirmation)' if up else 'learned-light replacement (not an upgrade)',
               rlh_mean_city_tl=float(ref.mean()), families=res)
    (d / 'stage0.json').write_text(json.dumps(out, indent=1)); print(json.dumps(out, indent=1))


def fit(featdir, out):
    import scripts.CITY_spat_forecast as FC
    files = sorted(str(p) for p in Path(featdir).glob('feat_s*.npz')); assert {Path(p).stem for p in files} == {f'feat_s{s}' for s in ([0] if os.environ.get('SMOKE') == '1' else range(8))}, (featdir,files)
    T = FC.fit(files); Path(out).write_text(json.dumps(T)); print('table', out, 'files', len(files), 'lights', len(T['per']))


if __name__ == '__main__':
    stage0(sys.argv[2]) if sys.argv[1] == 'stage0' else fit(sys.argv[2], sys.argv[3])
