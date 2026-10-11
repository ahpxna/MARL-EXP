#!/usr/bin/env python3
"""W18 reports (PROTOCOL_CITY_WAVE18_20261008).  Rows (tags <ARM>[P5]_t0_<f>) in <dir>/screen (TUNE) and <dir>/conf (fresh):
  OFF / OFF75 / OFF100 / OFFP4 (all human at share 0.5 / 0.75 / 1.0 / off-peak; fleet column 'h'), BASE (W17 fleets s2213-s2513),
  D1 (off-peak fleets s3613 / s3713), D2a (queue-aware rule, 'r'), D2b (queue-aware PPO s3213 / s3313), D3 (PHEMlight5-trained s3413 / s3513),
  D4a / D4b (W17 fleets at share 0.75 / 1.0), D5g10 / D5g15 / D5g20 (gentle departures, 'g').
  screen <dir>   per family, candidate = best max(fuel H4, fuel P5) among variants with city / agent / human time-loss mean <= +0.5 (TUNE)
                 -> <dir>/screen/candidates.json, report_screen.txt
  confirm <dir>  each family's candidate vs its OFF on fresh traffic; decision (alpha 0.01, one-sided 99 %): agent fuel upper < -3 % under
                 HBEFA4 and PHEMlight5, every time-loss upper < +0.5, teleports <= OFF + 0.1 -> report_conf.txt.  Network fuel reported.
W18_SMOKE=1: one seed."""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
cmd, D = sys.argv[1], Path(sys.argv[2]); SM = os.environ.get('W18_SMOKE') == '1'
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
FAM = {'D1': [('D1', 'OFFP4', ('s3613', 's3713'))],
       'D2': [('D2a', 'OFF', ('r',)), ('D2b', 'OFF', ('s3213', 's3313'))],
       'D3': [('D3', 'OFF', ('s3413', 's3513'))],
       'D4': [('D4a', 'OFF75', ('s2213', 's2313', 's2413', 's2513')), ('D4b', 'OFF100', ('s2213', 's2313', 's2413', 's2513'))],
       'D5': [('D5g10', 'OFF', ('g',)), ('D5g15', 'OFF', ('g',)), ('D5g20', 'OFF', ('g',))],
       'BASE': [('BASE', 'OFF', ('s2213', 's2313', 's2413', 's2513'))]}
if SM:
    FAM = {k: [(a, o, f[:1]) for a, o, f in v] for k, v in FAM.items()}


def alias(Rt):
    import math
    for k, v in Rt.items():                                            # share 1.0 (D4b, OFF100): no humans -> human metrics set to 0 (documented)
        if k.startswith(('D4b', 'OFF100')):
            for s, row in v.items():
                for m in ('timeloss_human', 'fuel_human'):
                    if m in row and not math.isfinite(row[m]):
                        row[m] = 0.0
    for fam in FAM.values():
        for a, off, fl in fam:
            for x in ('', 'P5'):
                for f in fl:
                    if f'{off}{x}_t0_h' in Rt:
                        Rt[f'{off}{x}_t0_{f}'] = Rt[f'{off}{x}_t0_h']


def seeds(Rt, key):
    return sorted(Rt[key])


def cmp(Rt, a, off, fl, q):
    S = seeds(Rt, f'{a}_t0_{fl[0]}')
    r = V.paired(Rt, K(a), K(off), (0,), fl, S, q=q); r5 = V.paired(Rt, K(a + 'P5'), K(off + 'P5'), (0,), fl, S, q=q)
    tl = (V.tele(Rt, K(a), (0,), fl, S), V.tele(Rt, K(off), (0,), fl, S))
    net = {x: 100 * (sum(Rt[f'{a}{x}_t0_{f}'][s]['fuel'] * Rt[f'{a}{x}_t0_{f}'][s]['n'] for f in fl for s in S)
                     / sum(Rt[f'{off}{x}_t0_{f}'][s]['fuel'] * Rt[f'{off}{x}_t0_{f}'][s]['n'] for f in fl for s in S) - 1) for x in ('', 'P5')}
    return r, r5, tl, net, S


TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
if cmd == 'screen':
    Rt = rows(D / 'screen'); alias(Rt); out = ['== W18-1 screen (TUNE; field-matched world; FT)']; cand = {}
    for fam, vs in FAM.items():
        best = None
        for a, off, fl in vs:
            if f'{a}_t0_{fl[0]}' not in Rt:
                out.append(f'{fam} {a}: rows missing'); continue
            r, r5, tl, net, S = cmp(Rt, a, off, fl, 95.0)
            ok = all(r[k]['point'] <= 0.5 for k in ('timeloss', 'timeloss_agent', 'timeloss_human')); score = max(r['fuel_agent']['point'], r5['fuel_agent']['point'])
            out.append(f'{fam} {a} vs {off}: agent fuel H4 {r["fuel_agent"]["point"]:+.2f} P5 {r5["fuel_agent"]["point"]:+.2f}; network fuel H4 {net[""]:+.2f} P5 {net["P5"]:+.2f}; '
                       f'TL city {r["timeloss"]["point"]:+.2f} agent {r["timeloss_agent"]["point"]:+.2f} human {r["timeloss_human"]["point"]:+.2f}; tele {tl[0][0]:.2f} vs {tl[1][0]:.2f}'
                       + ('' if ok else '  (time > +0.5: not eligible)'))
            if ok and (best is None or score < best[0]):
                best = (score, a, off, list(fl))
        cand[fam] = None if best is None else dict(arm=best[1], off=best[2], fleets=best[3], score=best[0])
        out.append(f'  -> candidate {fam}: {cand[fam]}')
        if fam == 'D5':                                                # Amendment A1: trade-off candidate (best fuel, time ignored)
            tb = None
            for a, off, fl in vs:
                if f'{a}_t0_{fl[0]}' in Rt:
                    r, r5, tl, net, S = cmp(Rt, a, off, fl, 95.0); sc = max(r['fuel_agent']['point'], r5['fuel_agent']['point'])
                    if tb is None or sc < tb[0]:
                        tb = (sc, a, off, list(fl))
            cand['D5_tradeoff'] = None if tb is None else dict(arm=tb[1], off=tb[2], fleets=tb[3], score=tb[0], tradeoff=True)
            out.append(f'  -> trade-off candidate D5 (descriptive, A1): {cand["D5_tradeoff"]}')
    (D / 'screen' / 'candidates.json').write_text(json.dumps(cand, indent=1)); (D / 'screen' / 'report_screen.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
else:
    Rt = rows(D / 'conf'); alias(Rt); C = json.loads((D / 'screen' / 'candidates.json').read_text())
    out = ['== W18-2 confirmation (fresh; field-matched world; FT; alpha 0.01 per family, one-sided 99 %; material = agent fuel upper < -3 % under both models)']
    for fam, c in C.items():
        if c is None:
            out.append(f'{fam}: no eligible candidate on the screen'); continue
        a, off, fl = c['arm'], c['off'], tuple(c['fleets'])
        for s in seeds(Rt, f'{a}_t0_{fl[0]}'):
            for f in fl:
                h, p = Rt[f'{a}_t0_{f}'][s], Rt[f'{a}P5_t0_{f}'][s]
                if any(h[t] != p[t] for t in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                    print('KM13-1a/1b FAIL', a, f, s); sys.exit(1)
        r, r5, tl, net, S = cmp(Rt, a, off, fl, 99.0)
        mat = (r['fuel_agent']['up'] < -3 and r5['fuel_agent']['up'] < -3 and all(r[k]['up'] < 0.5 for k in ('timeloss', 'timeloss_agent', 'timeloss_human'))
               and tl[0][0] <= tl[1][0] + 0.1)
        lab = (f'  {fam} (A1, descriptive) trade-off: fuel upper < -3 % under both models {"YES" if r["fuel_agent"]["up"] < -3 and r5["fuel_agent"]["up"] < -3 else "NO"}; '
               f'time not non-inferior by design' if c.get('tradeoff') else f'  {fam} VERDICT: material benefit {"SHOWN" if mat else "NOT SHOWN"}')
        out += [f'-- {fam}: {a} vs {off} ({len(fl)} fleet(s) x {len(S)} seeds {S[0]}-{S[-1]})', V.line('  H4', r), V.line('  P5', r5),
                f'  network fuel H4 {net[""]:+.2f} P5 {net["P5"]:+.2f}; teleports/run {tl[0][0]:.2f} vs {tl[1][0]:.2f}', lab]
    (D / 'conf' / 'report_conf.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
