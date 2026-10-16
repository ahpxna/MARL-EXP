#!/usr/bin/env python3
"""W21-I / W21-J / W21-K report (PROTOCOL_CITY_WAVE21_20261015).  <dir>: PRB_R / PRB_SV (probe), RELs / RELl / RELr (release by block
length / matched random), BIS (TSI-G, AH); <W21-C dir>: SHADOWg (= R) and SERVEg (= SV) for the same fleet (s1413) and days.
  KW21-J1 / J2  PRB_R = SHADOWg and PRB_SV = SERVEg (time losses, fuel, counts, action digest): the probe changes nothing
  I   RELs / RELl / RELr - R against SV - R (agent / human time loss, agent fuel); released share of glide-seconds
  J   PRB_SV - PRB_R per edge-length bin: agent / human time-loss seconds, halted seconds, held human-seconds, lane spillback-seconds (per run)
  K   BIS - R against SV - R (AH)
Descriptive, 95 % bootstrap over lights x days (2 000 draws, seed 0).  Usage: CITY_w21ijk_report.py <dir> <W21-C dir> "<AH>" "<B2D>" "<days>" """
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_w6_validation import rows  # noqa: E402
D, C = Path(sys.argv[1]), Path(sys.argv[2]); LA, LB, DAYS = ([int(x) for x in a.split()] for a in sys.argv[3:6])
SM = os.environ.get('W21_SMOKE') == '1'; SFX = '_smoke' if SM else ''
R = rows(D); R.update({k: v for k, v in rows(C).items() if k.startswith(('SHADOWg_t', 'SERVEg_t'))})
F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports', 'unfinished', 'action_digest')
BL = ['<50 m', '50-100 m', '100-200 m', '>=200 m']; rng = np.random.default_rng(0)
out = [f'== W21-I / J / K: Midtown, fleet s1413, days {DAYS}; AH {LA}, B2D {LB}']; res = {}
for a, b, lab in (('PRB_R', 'SHADOWg', 'KW21-J1 PRB_R = SHADOWg'), ('PRB_SV', 'SERVEg', 'KW21-J2 PRB_SV = SERVEg')):
    n = tot = 0
    for k in LA + LB:
        for d in DAYS:
            tot += 1; n += all(R[f'{a}_t{k}'][d][f] == R[f'{b}_t{k}'][d][f] for f in F)
    out.append(f'{lab}: {n} of {tot} light-days identical'); res[lab.split()[0]] = [n, tot]


def diff(a, b, ks, m, pct=False):
    M = np.array([[100 * (R[f'{a}_t{k}'][d][m] / R[f'{b}_t{k}'][d][m] - 1) if pct else R[f'{a}_t{k}'][d][m] - R[f'{b}_t{k}'][d][m] for d in DAYS] for k in ks])
    bs = [M[np.ix_(rng.integers(0, M.shape[0], M.shape[0]), rng.integers(0, M.shape[1], M.shape[1]))].mean() for _ in range(2000)]
    return float(M.mean()), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


fmt = lambda v: f'{v[0]:+.2f} [{v[1]:+.2f}, {v[2]:+.2f}]'  # noqa: E731


def blk(a, ks):
    r = {m: diff(a, 'SHADOWg', ks, m, m == 'fuel_agent') for m in ('timeloss_agent', 'timeloss_human', 'fuel_agent')}
    return r, f'agent TL {fmt(r["timeloss_agent"])} s/veh, human TL {fmt(r["timeloss_human"])}, agent fuel {fmt(r["fuel_agent"])} %'


share = (D / 'matched_share.txt').read_text().strip() if (D / 'matched_share.txt').exists() else ''
out.append(share)
for fam, ks in (('AH', LA), ('B2D', LB)):
    e = {}; out.append(f'-- {fam} (lights {ks})')
    for a, lab in (('SERVEg', 'SV (forecast, no release)'), ('RELs', 'RELs (release on edges < 100 m)'), ('RELl', 'RELl (release on edges >= 100 m)'),
                   ('RELr', 'RELr (random release, matched share)'), ('BIS', 'BIS (TSI-G)')):
        if all(f'{a}_t{k}' in R for k in ks):
            r, s = blk(a, ks); e[a] = r
            rel = ''
            if a.startswith('REL'):
                g = sum(R[f'{a}_t{k}'][d]['w21_glide_s'] for k in ks for d in DAYS); rr = sum(R[f'{a}_t{k}'][d]['w21_released_s'] for k in ks for d in DAYS)
                rel = f' | released {rr / max(1, g):.3f} of {g} glide-s'
            out.append(f'  {lab} - R: {s}{rel}')
    sv = e['SERVEg']['timeloss_agent'][0]
    if 'RELs' in e and 'RELr' in e:
        a, r_ = e['RELs']['timeloss_agent'][0], e['RELr']['timeloss_agent'][0]
        out.append(f'  I reading: RELs {a:+.2f} vs SV {sv:+.2f} and RELr {r_:+.2f} -> '
                   + ('short blocks carry the cost (RELs < half of SV and < RELr)' if a < 0.5 * sv and a < r_ else 'not supported for this family'))
    if 'BIS' in e:
        b = e['BIS']['timeloss_agent'][0]
        out.append(f'  K reading: BIS {b:+.2f} vs SV {sv:+.2f} -> ' + ('TSI-G helps on the map (below half of SV)' if b < 0.5 * sv else 'TSI-G does not halve the cost'))
    # J: per-bin probe differences (per run)
    if all(f'PRB_{x}_t{k}' in R for x in ('R', 'SV') for k in ks):
        P = {x: {m: np.array([[R[f'PRB_{x}_t{k}'][d]['w21_probe'][m] for d in DAYS] for k in ks]) for m in ('tl_a', 'tl_h', 'halt_a', 'halt_h', 'held_h', 'spill', 'vs_a', 'vs_h')} for x in ('R', 'SV')}
        out.append('  J per run, PRB_SV - PRB_R by edge-length bin ' + str(BL) + ' (vehicle-seconds):')
        for m, lab in (('tl_a', 'agent time-loss s'), ('tl_h', 'human time-loss s'), ('halt_h', 'human halted s'), ('held_h', 'human-s behind a glider'), ('spill', 'lane spillback-s')):
            dlt = (P['SV'][m] - P['R'][m]).mean(axis=(0, 1)); tot = dlt.sum()
            out.append(f'    {lab:24s} ' + '  '.join(f'{x:+10.0f}' for x in dlt) + f'   total {tot:+.0f}' + ('   shares ' + ' '.join(f'{x / tot:.2f}' for x in dlt) if abs(tot) > 0 else ''))
        vs = (P['R']['vs_a'] + P['R']['vs_h']).mean(axis=(0, 1)); out.append('    share of vehicle-seconds (R)  ' + ' '.join(f'{x / vs.sum():.2f}' for x in vs))
        e['J'] = {m: (P['SV'][m] - P['R'][m]).mean(axis=(0, 1)).tolist() for m in ('tl_a', 'tl_h', 'halt_h', 'held_h', 'spill')}
    res[fam] = e
(D / f'report_w21ijk{SFX}.txt').write_text('\n'.join(out) + '\n'); (D / f'w21ijk{SFX}.json').write_text(json.dumps(res, indent=1, default=float)); print('\n'.join(out))
