#!/usr/bin/env python3
"""W22-B report (PROTOCOL_CITY_WAVE22_20261017, Amendment W22-B): per-vehicle A/B bias as a function of the treated share, and the
network-wide switchback.  <dir>: MIXp<pp>_t<k>_s<f> and NSW_t<k>_s<f> rows; <W22 dir>: MIX_t<k>_s<f> rows (p 0.5).  Ground truth R / SV rows.
  bias(p) = (treated - control fleet time loss) - (SV - R agent time loss); NSW bias = (treated - control windows' trips) - (SV - R);
  crossed bootstrap 95 % over lights x fleets x days (2 000 draws, seed 0).
Usage: CITY_w22b_report.py <dir> <W22 dir> "<FAM:k0-k1:src ...>" "<fleets>" "<days>" "<p levels, e.g. 10 30 70 90>" """
import json, os, sys
from pathlib import Path
import numpy as np
D, D0 = Path(sys.argv[1]), Path(sys.argv[2]); FAMS = [x.split(':') for x in sys.argv[3].split()]; FS = [int(x) for x in sys.argv[4].split()]
DAYS = [int(x) for x in sys.argv[5].split()]; PL = [int(x) for x in sys.argv[6].split()]; SM = os.environ.get('W22_SMOKE') == '1'; SFX = '_smoke' if SM else ''
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
verdict = lambda b: ('UNDERSTATES' if b[2] < 0 else 'OVERSTATES') if (b[2] < 0 or b[1] > 0) else 'no bias shown'  # noqa: E731
out = [f'== W22-B: per-vehicle A/B bias by treated share {PL} (+ 50 from W22) and the network-wide switchback; fleets {FS}; days {DAYS}']; res = {}
for fam, kr, src in FAMS:
    k0, k1 = (int(x) for x in kr.split('-')); ks = list(range(k0, k1 + 1)); G = SRC[src] if src in SRC else Path(src)
    R = {(k, s): L(G / f'R_t{k}_s{s}.json') for k in ks for s in FS}; V = {(k, s): L(G / f'SV_t{k}_s{s}.json') for k in ks for s in FS}
    shape = (len(ks), len(FS), len(DAYS)); GTE = np.zeros(shape)
    for i, k in enumerate(ks):
        for j, s in enumerate(FS):
            for n, d in enumerate(DAYS):
                GTE[i, j, n] = V[k, s][d]['timeloss_agent'] - R[k, s][d]['timeloss_agent']
    e = dict(GTE=boot(GTE)); out.append(f'-- {fam} (t{k0}-t{k1}); GTE = SV - R agent TL {fmt(e["GTE"])} s/veh')
    for p in sorted(PL + ([50] if not SM else [])):
        src_dir, tag = (D0, 'MIX') if p == 50 else (D, f'MIXp{p}')
        X = {(k, s): L(src_dir / f'{tag}_t{k}_s{s}.json') for k in ks for s in FS}
        DM, SC, ST = np.zeros(shape), np.zeros(shape), np.zeros(shape)
        for i, k in enumerate(ks):
            for j, s in enumerate(FS):
                for n, d in enumerate(DAYS):
                    w = X[k, s][d]['w22']; DM[i, j, n] = w['tl_T'] - w['tl_C']
                    SC[i, j, n] = w['tl_C'] - R[k, s][d]['timeloss_agent']; ST[i, j, n] = w['tl_T'] - V[k, s][d]['timeloss_agent']
        b = boot(DM - GTE); e[f'p{p}'] = dict(DM=boot(DM), bias=b, spill_C=boot(SC), spill_T=boot(ST))
        out.append(f'  MIX p {p / 100:.1f}: DM {fmt(e[f"p{p}"]["DM"])}; bias {fmt(b)} -> {verdict(b)}; control TL_C - R {fmt(e[f"p{p}"]["spill_C"])}; '
                   f'treated TL_T - SV {fmt(e[f"p{p}"]["spill_T"])}')
    X = {(k, s): L(D / f'NSW_t{k}_s{s}.json') for k in ks for s in FS}; NS = np.zeros(shape)
    for i, k in enumerate(ks):
        for j, s in enumerate(FS):
            for n, d in enumerate(DAYS):
                w = X[k, s][d]['w22']['nsw']; NS[i, j, n] = w['tl_T'] - w['tl_C']
    b = boot(NS - GTE); e['NSW'] = dict(est=boot(NS), bias=b)
    out.append(f'  NSW (600 s, burn-in 120 s): estimate {fmt(e["NSW"]["est"])}; bias {fmt(b)} -> {verdict(b)}')
    res[fam] = e
if SM:
    out.append('(smoke: truncated runs against full-length ground truth; numbers meaningless, pipeline check only)')
(D / f'report_w22b{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w22b{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
