#!/usr/bin/env python3
"""PERF report (PROTOCOL_CITY_PERF_20261005): performative sensitivity (pub - shadow) with vs without the light adapter q:2:0."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as RR  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; S = list(range(600, 612)); K = (0, 1); FL = ('s13', 's113')


def sc(d, tag):
    r = {x['seed']: x for x in json.load(open(CS / d / f'{tag}_n3.json'))['runs']}; out = {}
    for s in S:
        g = r[s]['ttg']; n = max(1, g['n']); bh = g['by_h']
        out[s] = dict(mae=g['mae'], gt30=bh['30-1e+09'][0] / n, b1530=bh['15-30'][0] / n)
    return out


if __name__ == '__main__':
    out = ['== PERF: publication sensitivity of the forecast target, with vs without the light adapter q:2:0 (DEV 600-611)']
    for key in ('mae', 'gt30', 'b1530'):
        A = lambda p, k, f: sc('perf_20261005/dev', f'{p}_k{k}_{f}'); N = lambda p, k, f: sc('n3_20261005/dev', f'{p}_k{k}_{f}')
        cw = np.array([[[A('Apub', k, f)[s][key] - A('Ash', k, f)[s][key] for s in S] for f in FL] for k in K])
        cn = np.array([[[N('N3pub', k, f)[s][key] - N('N3sh', k, f)[s][key] for s in S] for f in FL] for k in K])
        dd = cw - cn; pw, cwi, _ = RR.crossed(cw, RR.draws(cw.shape)); pn, cni, _ = RR.crossed(cn, RR.draws(cn.shape)); pd, cdi, ud = RR.crossed(dd, RR.draws(dd.shape))
        out.append(f'  {key}: pub-shadow WITH adapter {pw:+.4f} [{cwi[0]:+.4f}, {cwi[1]:+.4f}] | WITHOUT {pn:+.4f} [{cni[0]:+.4f}, {cni[1]:+.4f}] | difference {pd:+.4f} [{cdi[0]:+.4f}, {cdi[1]:+.4f}] (up {ud:+.4f})')
        if key == 'mae':
            out.append(f'  SENSITIVITY REDUCED VERDICT: {"SUPPORTED" if ud < 0 else "NOT SUPPORTED"}')
    t = '\n'.join(out) + '\n'; (CS / 'perf_20261005/report_perf.txt').write_text(t); print(t)
