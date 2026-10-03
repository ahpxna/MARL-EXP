#!/usr/bin/env python3
"""Report of PROTOCOL_E3_AGE_RESPONSE_SHIFT_20261001.md (written before the runs).  HC1: drop from the peak (a = 1..10) to
a = 8 smaller for relayCK1 than relay6Cage (same seed) in >= 3/4 seeds (K = 1 states); HC2: range over a = 1..8 smaller in
>= 3/4 seeds.  Also the parity self-check: v2 with the default tag must equal v1 on seed 0, K = 1."""
import json
from pathlib import Path

M = Path('research/marl_budget'); V1 = M / 'e3_age_response_20261001'; V2 = M / 'e3_age_response_shift_20261001'; SEEDS = ['0', '1', '2', '3']


def stats(a):
    peak = max(a[1:11]); return dict(peak_age=max(range(1, 11), key=lambda i: a[i]), drop8=peak - a[8], range18=max(a[1:9]) - min(a[1:9]), a0=a[0])


def main():
    par = json.loads((V2 / 'parity' / 'age_response_K1.json').read_text())['0']; ref = json.loads((V1 / 'age_response_K1.json').read_text())['0']
    if any(abs(x - y) > 1e-12 for x, y in zip(par['acc_by_age'], ref['acc_by_age'])) or abs(par['acc_actual'] - ref['acc_actual']) > 1e-12:
        raise SystemExit('SELF-CHECK FAIL: v2 (default tag) differs from v1 on seed 0, K = 1')
    L = ['SELF-CHECK PASS: v2 with the default tag reproduces v1 (seed 0, K = 1)']
    for K in ('1', '0'):
        base = json.loads((V1 / f'age_response_K{K}.json').read_text()); ck = json.loads((V2 / 'relayCK1' / f'age_response_K{K}.json').read_text())
        L.append(f'K = {K} states | seed | student | peak age | drop peak->a8 | range a1..8 | a0 | curve a0..a10')
        w1 = w2 = 0
        for s in SEEDS:
            b, c = stats(base[s]['acc_by_age']), stats(ck[s]['acc_by_age'])
            for name, st, curve in (('relay6Cage (iid-trained)', b, base[s]['acc_by_age']), ('relayCK1 (K=1-trained)', c, ck[s]['acc_by_age'])):
                L.append(f'  | {s} | {name} | {st["peak_age"]} | {st["drop8"]:.3f} | {st["range18"]:.3f} | {st["a0"]:.3f} | ' + ' '.join(f'{x:.3f}' for x in curve))
            w1 += c['drop8'] < b['drop8']; w2 += c['range18'] < b['range18']
        if K == '1':
            L += [f'HC1 drop smaller for relayCK1 in {w1}/4 seeds -> {"SUPPORTED" if w1 >= 3 else "NOT SUPPORTED"}',
                  f'HC2 range a1..8 smaller for relayCK1 in {w2}/4 seeds -> {"SUPPORTED" if w2 >= 3 else "NOT SUPPORTED"}']
        else:
            L.append(f'(iid states, reported only) drop smaller in {w1}/4, range smaller in {w2}/4')
    text = '\n'.join(L); print(text); (M / 'e3_age_response_shift_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
