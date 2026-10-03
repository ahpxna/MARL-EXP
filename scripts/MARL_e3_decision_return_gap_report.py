#!/usr/bin/env python3
"""Report of PROTOCOL_E3_DECISION_RETURN_GAP_20261001.md (EXPLORATORY): E1-E4."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_decision_return_gap_20261001'


def summ(d):
    r = json.loads((d / 'records.json').read_text())
    rel = [x for e in r for x in e['relay']]; zo = [x for e in r for x in e['z_own']]
    f = lambda xs, k: float(np.mean([x[k] for x in xs]))
    qr = np.array([e['q_relay'] for e in r]); qz = np.array([e['q_z'] for e in r])
    return dict(acc_R_on_R=f(rel, 'protoS'), acc_Z_on_R=f(rel, 'zok'), acc_Z_on_Z=f(zo, 'zok_own'), reg_R_on_R=f(rel, 'rreg'),
                reg_Z_on_R=f(rel, 'zreg'), reg_Z_on_Z=f(zo, 'zreg_own'), gain=float(-(qr.sum() / qz.sum() - 1) * 100),
                gap_by_third=[float((qr[:, a:b].sum() - qz[:, a:b].sum()) / qz.sum() * 100) for a, b in ((0, 9), (9, 18), (18, 26))])


def main():
    L = ['cell | acc R on R | acc Z on R | acc Z on Z | regret R on R | regret Z on R | regret Z on Z | gain (dev 8 eps) | queue gap relay-Z by thirds (% of Z total)']
    out = {}
    for tag in ['g4_s0_const1', 'g4_s0_const2', 'g4_s0_iid'] + [f'g3_s{s}_const1' for s in range(10)]:
        d = P / tag
        if not (d / 'manifest.json').exists():
            L.append(f'{tag}: missing'); continue
        x = summ(d); out[tag] = x
        L.append(f'{tag} | {x["acc_R_on_R"]:.3f} | {x["acc_Z_on_R"]:.3f} | {x["acc_Z_on_Z"]:.3f} | {x["reg_R_on_R"]:.3f} | {x["reg_Z_on_R"]:.3f} | '
                 f'{x["reg_Z_on_Z"]:.3f} | {x["gain"]:+.2f} % | ' + ' '.join(f'{v:+.2f}' for v in x['gap_by_third']))
    g3 = [out[f'g3_s{s}_const1'] for s in range(10) if f'g3_s{s}_const1' in out]
    if g3:
        L.append('3x3 K=1 mean over seeds: ' + ' '.join(f'{k} {np.mean([x[k] for x in g3]):.3f}' for k in ('acc_R_on_R', 'acc_Z_on_R', 'acc_Z_on_Z', 'reg_R_on_R', 'reg_Z_on_R', 'reg_Z_on_Z')))
    zr = P / 'g4_s0_Zmore/rows.json'; rr = P / 'g4_s0_Rmore/rows.json'
    if zr.exists() and rr.exists() and (P / 'g4_s0_Zmore/manifest.json').exists() and (P / 'g4_s0_Rmore/manifest.json').exists():
        z = {x['episode']: x['queue_sum'] for x in json.loads(zr.read_text()) if x['rule'] == 'none'}
        r = {x['episode']: x['queue_sum'] for x in json.loads(rr.read_text())}
        L0 = M / 'e3_g4_s0_devlook_20261001'
        z.update({x['episode']: x['queue_sum'] for x in json.loads((L0 / 'Zdev/rows.json').read_text()) if x['rule'] == 'none'})
        r.update({x['episode']: x['queue_sum'] for x in json.loads((L0 / 'R_K1/rows.json').read_text())})
        eps = sorted(set(z) & set(r)); g = -(sum(r[e] for e in eps) / sum(z[e] for e in eps) - 1) * 100
        per = [-(r[e] / z[e] - 1) * 100 for e in eps]
        L.append(f'E4 4x4 seed 0 K=1 gain over {len(eps)} development episodes: {g:+.2f} % (episodes with relay worse: {sum(p < 0 for p in per)}/{len(eps)})')
        out['E4'] = dict(gain=g, n=len(eps))
    text = '\n'.join(L); print(text)
    (M / 'e3_decision_return_gap_report_20261001.json').write_text(json.dumps(out, indent=1))
    (M / 'e3_decision_return_gap_report_20261001.txt').write_text('EXPLORATORY\n' + text + '\n')


if __name__ == '__main__':
    main()
