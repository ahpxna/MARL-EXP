#!/usr/bin/env python3
"""Wave-10 repair reports (PROTOCOL_CITY_WAVE10_20261005, Amendment A3).  Usage: CITY_w10_report2.py sp4 | n3b   (W10_SMOKE=<dir> W10_SEED=<s>)"""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W10_SMOKE')); W = Path(os.environ['W10_SMOKE']) if SM else ROOT / 'research/city_sim/w10_20261005'


def arm(Rt, K, a, b, L, F, S, out, q):
    r = V.paired(Rt, K(a), K(b), L, F, S, q=q); ok, tl = V.limits(r, V.tele(Rt, K(a), L, F, S), V.tele(Rt, K(b), L, F, S))
    out += [V.line(f'{a} - {b}', r), f'  {a}: all M3 limits vs {b} (incl. teleports, unfinished; one-sided {q:g} %): {ok}; {tl}']
    return ok


def sp4():
    D = W / 'sp4'; S = [int(os.environ.get('W10_SEED', 1170))] if SM else list(range(1170, 1190)); L = (11,) if SM else (11, 111); F = ('rule',)
    Rt = rows(D / 'conf'); K = lambda a: (lambda l, f: f'{a}_{l}')  # noqa: E731
    out = ['== W10-5 spider attempt 4: N2K refit on logs collected with TSIK published (one repeated-retraining iteration); adapter as attempt 1; '
           'fresh spider traffic 1170-1189; alpha 0.00625 (fourth attempt; chain bound 0.09375)']
    ok = arm(Rt, K, 'TSIK1', 'R', L, F, S, out, 99.375); arm(Rt, K, 'HYBK1', 'R', L, F, S, out, 99.375)
    g = lambda a: sum(Rt[f'{a}_{l}'][s]['green_mean'] for l in L for s in S) / (len(L) * len(S))  # noqa: E731
    out.append('  mean green (s): ' + '; '.join(f'{a} {g(a):.1f}' for a in ('R', 'HYBK1', 'TSIK1')))
    out.append(f'  W10-5 SPIDER ATTEMPT 4 VERDICT: {"PASS" if ok else "FAIL"}')
    (D / 'report_sp4.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


def n3b():
    D = W / 'n3b'; S = [int(os.environ.get('W10_SEED', 720))] if SM else list(range(720, 740)); L = (21,) if SM else (21, 22, 23, 24, 25)
    F = ('s213',) if SM else ('s213', 's313', 's413', 's513'); Rt = rows(D / 'conf'); K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
    ch = json.loads((D / 'tune' / 'choice.json').read_text())
    out = ['== W10-6 rand3 attempt 2: extended adapter grid A in {2,3,4,6} x B in {0.5,1,2}; NET3 lights / fleets / providers; fresh rand3 720-739; alpha 0.025',
           '  per-light (A, B): ' + ', '.join(f't{l} ({ch[str(l)]["choice"]}, qualified {len(ch[str(l)]["qualified"])})' for l in L)]
    ok = arm(Rt, K, 'TSIX', 'R', L, F, S, out, 97.5)
    out.append(f'  W10-6 RAND3 ATTEMPT 2 VERDICT: {"PASS" if ok else "FAIL"}')
    (D / 'report_n3b.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    dict(sp4=sp4, n3b=n3b)[sys.argv[1]]()
