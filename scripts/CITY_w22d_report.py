#!/usr/bin/env python3
"""W22-D report (PROTOCOL_CITY_WAVE22_20261017, Amendment W22-D): alternating network switchbacks.  <dir>: <TAG>_t<k>_s<f> rows (w22.nsw);
ground truth R / SV rows.  bias = (treated - control windows' trips, fleet time loss) - (SV - R agent time loss); crossed bootstrap 95 %.
Usage: CITY_w22d_report.py <dir> "<FAM:k0-k1:src ...>" "<fleets>" "<days>" "<tags>" """
import json, os, sys
from pathlib import Path
import numpy as np
D = Path(sys.argv[1]); FAMS = [x.split(':') for x in sys.argv[2].split()]; FS = [int(x) for x in sys.argv[3].split()]; DAYS = [int(x) for x in sys.argv[4].split()]
TAGS = sys.argv[5].split(); SM = os.environ.get('W22_SMOKE') == '1'; SFX = '_smoke' if SM else ''
SRC = {'w19': Path('research/city_sim/w19_20261008/conf'), 'w20': Path('research/city_sim/w20_20261009/conf')}
rng = np.random.default_rng(0)


def L(p):
    d = json.loads(Path(p).read_text())
    if d.get('status') != 'COMPLETE':
        sys.exit(f'INCOMPLETE {p}')
    return {r['seed']: r for r in d['rows']}


def boot(M):
    bs = [np.nanmean(M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]), rng.integers(0, M.shape[2], M.shape[2]))]) for _ in range(2000)]
    return float(np.nanmean(M)), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


fmt = lambda v: f'{v[0]:+.2f} [{v[1]:+.2f}, {v[2]:+.2f}]'  # noqa: E731
out = [f'== W22-D: alternating network switchbacks {TAGS}; fleets {FS}; days {DAYS}']; res = {}
for fam, kr, src in FAMS:
    k0, k1 = (int(x) for x in kr.split('-')); ks = list(range(k0, k1 + 1)); G = SRC[src] if src in SRC else Path(src)
    R = {(k, s): L(G / f'R_t{k}_s{s}.json') for k in ks for s in FS}; V = {(k, s): L(G / f'SV_t{k}_s{s}.json') for k in ks for s in FS}
    shape = (len(ks), len(FS), len(DAYS)); GTE = np.array([[[V[k, s][d]['timeloss_agent'] - R[k, s][d]['timeloss_agent'] for d in DAYS] for s in FS] for k in ks])
    e = dict(GTE=boot(GTE)); out.append(f'-- {fam} (t{k0}-t{k1}); GTE {fmt(e["GTE"])} s/veh')
    for tag in TAGS:
        X = {(k, s): L(D / f'{tag}_t{k}_s{s}.json') for k in ks for s in FS}
        NS = np.array([[[X[k, s][d]['w22']['nsw']['tl_T'] - X[k, s][d]['w22']['nsw']['tl_C'] for d in DAYS] for s in FS] for k in ks])
        b = boot(NS - GTE); e[tag] = dict(est=boot(NS), bias=b, n_T=int(sum(X[k, s][d]['w22']['nsw']['n_T'] for k in ks for s in FS for d in DAYS)),
                                          n_C=int(sum(X[k, s][d]['w22']['nsw']['n_C'] for k in ks for s in FS for d in DAYS)))
        v = ('UNDERSTATES' if b[2] < 0 else 'OVERSTATES') if (b[2] < 0 or b[1] > 0) else 'no bias shown'
        out.append(f'  {tag}: estimate {fmt(e[tag]["est"])}; bias {fmt(b)} -> {v} (trips {e[tag]["n_T"]} treated / {e[tag]["n_C"]} control)')
    res[fam] = e
if SM:
    out.append('(smoke: truncated runs against full-length ground truth; numbers meaningless, pipeline check only)')
(D / f'report_w22d{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w22d{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
