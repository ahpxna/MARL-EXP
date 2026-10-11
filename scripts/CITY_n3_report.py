#!/usr/bin/env python3
"""N3 report (PROTOCOL_CITY_N3_FEEDBACK_20261005; written before the panel).  Rows: n3_20261005/dev (N3pub, N3sh, N3ref, N3refsh) + sidecars
<tag>_n3.json (query errors per seed); R from n1_20261005/g4; N2q05 from n2_20261005/dev.  Crossed bootstrap over [k, fleet, traffic]."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_n2_report as N  # noqa: E402
import scripts.CITY_n2m_report as M  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'n3_20261005'; F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports')


def err(tag, kind='ttg', key='mae'):
    r = {x['seed']: x for x in json.load(open(D / 'dev' / f'{tag}_n3.json'))['runs']}; return {s: r[s][kind][key] for s in r}


def ecube(A, B, kind='ttg', key='mae'):
    return np.array([[[err(A(k, f), kind, key)[s] - err(B(k, f), kind, key)[s] for s in N.S] for f in N.FL] for k in N.K])


if __name__ == '__main__':
    Rt = {**rows(CS / 'n1_20261005/g4'), **rows(CS / 'n2_20261005/dev'), **rows(D / 'dev')}; out = ['== N3 publication feedback']
    k1 = all(Rt[f'N3pub_k{k}_{f}'][s][q] == Rt[f'N2q05_k{k}_{f}'][s][q] for k in N.K for f in N.FL for s in N.S for q in F)
    out.append(f'  KN3-1 pub == N2q05 rows: {"PASS" if k1 else "FAIL"}')
    nm = lambda p: (lambda k, f: f'{p}_k{k}_{f}')
    for kind in ('ttg', 'ttr'):
        for p in ('N3pub', 'N3sh', 'N3ref', 'N3refsh'):
            m = np.mean([err(f'{p}_k{k}_{f}', kind)[s] for k in N.K for f in N.FL for s in N.S]); b = np.mean([err(f'{p}_k{k}_{f}', kind, 'bias')[s] for k in N.K for f in N.FL for s in N.S])
            out.append(f'  {kind} {p:8s}: MAE {m:6.2f} bias {b:+6.2f}')
    bh = {}
    for p in ('N3pub', 'N3sh'):
        acc = {}
        for k in N.K:
            for f in N.FL:
                for x in json.load(open(D / 'dev' / f'{p}_k{k}_{f}_n3.json'))['runs']:
                    for bk, (n, m) in x['ttg']['by_h'].items():
                        if m is not None:
                            a = acc.setdefault(bk, [0, 0.0]); a[0] += n; a[1] += n * m
        bh[p] = {bk: (a[0], round(a[1] / max(1, a[0]), 2)) for bk, a in acc.items()}
    out.append(f'  ttg MAE by realized horizon (n, MAE): pub {bh["N3pub"]} | shadow {bh["N3sh"]}')
    c = ecube(nm('N3pub'), nm('N3sh')); dr = N.R.draws(c.shape); pt, ci, up = N.R.crossed(c, dr)
    fb = 'DEGRADES' if ci[0] > 0 else ('IMPROVES' if ci[1] < 0 else 'NOT DETECTED')
    out.append(f'  (a) ttg MAE pub - shadow: {pt:+.2f} [{ci[0]:+.2f}, {ci[1]:+.2f}] -> FEEDBACK {fb} ACCURACY')
    c = ecube(nm('N3ref'), nm('N3pub')); pt2, ci2, _ = N.R.crossed(c, N.R.draws(c.shape)); out.append(f'  (b) ttg MAE refit - one-shot (both published): {pt2:+.2f} [{ci2[0]:+.2f}, {ci2[1]:+.2f}]')
    res = {}
    for a, b in (('N3ref', 'N3pub'), ('N3ref', 'R'), ('N3pub', 'R'), ('N3sh', 'R')):
        res[(a, b)] = M.full(Rt, nm(a), nm(b)); out.append(M.line(f'{a} - {b}', res[(a, b)]))
    r = res[('N3ref', 'N3pub')]; ok = (r['fuel_agent'][2] < 0 and r['timeloss_agent'][0] <= 0.5) or (r['timeloss_agent'][2] < 0 and r['fuel_agent'][0] <= 0.5)
    v = res[('N3ref', 'R')]; cand = v['fuel_agent'][2] < 0 and all(v[q][2] < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human'))
    out += [f'  (b) CALIBRATION UNDER SERVICE: {"HELPS" if ok else "NOT SHOWN"}', f'  refit vs R all M3 limits (candidate): {cand}']
    t = '\n'.join(out) + '\n'; (D / 'report_n3.txt').write_text(t); print(t)
