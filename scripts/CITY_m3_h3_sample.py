#!/usr/bin/env python3
"""M3-H3 situation sampling (registered): from the scans m3h3_20261004/scan/scan_k<k>_s<seed>_h3.json, per (k, seed) draw 6 receiver-eligible
and 6 random decision ticks (t in [600, 3000], distinct (t, light)), RNG seed 20261004 + 100 k + seed.  Writes m3h3_20261004/situations.json."""
import json, sys
from pathlib import Path
import numpy as np
D = Path(__file__).resolve().parents[1] / 'research/city_sim/m3h3_20261004'
if __name__ == '__main__':
    out = []
    for f in sorted((D / 'scan').glob('scan_k*_s*_h3.json')):
        k, s = int(f.stem.split('_')[1][1:]), int(f.stem.split('_')[2][1:]); sc = json.loads(f.read_text())['per_seed'][str(s)]['scan']
        rng = np.random.default_rng(20261004 + 100 * k + s); el = [x for x in sc if x[4]]; al = sc
        pick = [el[i] for i in rng.choice(len(el), min(6, len(el)), replace=False)] if el else []
        taken = {(x[0], x[1]) for x in pick}; rest = [x for x in al if (x[0], x[1]) not in taken]
        pick += [rest[i] for i in rng.choice(len(rest), 6, replace=False)]
        for i, x in enumerate(pick):
            out.append(dict(k=k, seed=s, t=int(x[0]), light=x[1], rl_action=x[2], qgap=x[3], eligible=x[4], near=x[5], hD=x[6], group='eligible' if i < min(6, len(el)) else 'random'))
        print(f'k{k} s{s}: {len(sc)} decision ticks, {len(el)} eligible ({100 * len(el) / max(1, len(sc)):.1f} %), sampled {len(pick)}')
    (D / 'situations.json').write_text(json.dumps(out, indent=1)); print('situations', len(out))
