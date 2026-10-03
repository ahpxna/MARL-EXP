#!/usr/bin/env python3
"""Report of PROTOCOL_E3_NET_COUNT_20261001.md Parts 1, 3, 4 (written before the composition run).
Part 1: frozen net = F - S_2 - never (per receiver-step, /8) on the hold-r cells vs their known gains (N1, N2, N3).
Part 3: the provisioning rule K_min = (1 + theta)(m - 1)/(tau_train + 2), theta = -0.08, scored on the known cells (A1).
Part 4: count-deadline vs age-first, S_2 + never per receiver-step (B1, B2)."""
import json, math
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); C = json.loads((M / 'e3_net_count_20261001' / 'composition.json').read_text()); THETA = -0.08
HD = json.loads((M / 'e3_hold_dose_report_20261001.json').read_text()); HP = json.loads((M / 'e3_hold_prospective_report_20261001.json').read_text())


def cell(K, r):
    return C[f'agefirst:{r}:const{K}']


def main():
    L = ['== Part 1: hold-r cells (channel-only net, frozen functional) ==', 'K | r | F | S_2 | never | net | net/8 | B_3 | dev gain | prosp gain']
    dev = [(1, 1), (2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (3, 1), (3, 4), (3, 6)]; pro = [(2, 1), (2, 3), (2, 4), (2, 6), (3, 1), (3, 6)]
    for K, r in dev:
        c = cell(K, r); g = float(np.mean(HD[f'K{K}_r{r}'])); gp = HP.get(f'K{K}_r{r}', {}).get('gain')
        L.append(f'{K} | {r} | {c["F"]:.2f} | {c["S_tau"]["2"]:.2f} | {c["never"]:.2f} | {c["net"]:+.2f} | {c["net"] / 8:+.3f} | {c["B3"]:.2f} | {g:+.2f}'
                 + (f' | {np.mean(gp):+.2f}' if gp else ' | -'))
    gd = [float(np.mean(HD[f'K{K}_r{r}'])) for K, r in dev]
    rn = float(spearmanr([cell(K, r)['net'] for K, r in dev], gd).correlation); rb = float(spearmanr([cell(K, r)['B3'] for K, r in dev], gd).correlation)
    rs = float(spearmanr([cell(K, r)['S_tau']['2'] + cell(K, r)['never'] for K, r in dev], gd).correlation)
    N1 = rn >= 0.80 and rn >= abs(rb); N3 = abs(rs) >= abs(rb)
    hits = []
    for K, r in pro:
        pred = cell(K, r)['net'] / 8 > THETA; obs = float(np.mean(HP[f'K{K}_r{r}']['gain'])) > 0; hits.append(pred == obs)
        L.append(f'  prospective K{K} r{r}: net/8 {cell(K, r)["net"] / 8:+.3f} -> predicted {"+" if pred else "-"}, observed mean {float(np.mean(HP[f"K{K}_r{r}"]["gain"])):+.2f} % -> {"hit" if pred == obs else "MISS"}')
    N2 = sum(hits) >= 5
    L += [f'N1 Spearman(net, dev gain) {rn:+.3f} (need >= +0.80 and >= |B_3| {abs(rb):.3f}) -> {"SUPPORTED" if N1 else "NOT SUPPORTED"}',
          f'N2 sign rule on the 6 prospective cells: {sum(hits)}/6 (need >= 5) -> {"SUPPORTED" if N2 else "NOT SUPPORTED"}',
          f'N3 |Spearman(S_2 + never, dev gain)| {abs(rs):.3f} vs |B_3| {abs(rb):.3f} -> {"SUPPORTED" if N3 else "NOT SUPPORTED"}']
    L += ['== Part 3: provisioning rule K_min = (1 + theta)(m - 1)/(tau_train + 2) ==']
    for name, m1, tau in (('3x3 iid-trained', 8, 2), ('3x3 K=1-trained', 8, 8), ('4x4 iid-trained, relative', 15, 9), ('4x4 iid-trained, absolute', 15, 2)):
        km = (1 + THETA) * m1 / (tau + 2); L.append(f'  {name}: K_min = {km:.2f} -> smallest allowed constant K = {math.floor(km) + 1}')
    G1 = {int(s): v for s, v in json.loads((M / 'e3_demand_frontier_report_20261001.json').read_text())['gain'].items()}
    obs = {K: float(np.mean([G1[s][K - 1] for s in range(10)])) for K in (1, 2, 3)}; km = (1 + THETA) * 8 / 4
    ok = [((K > km) == (obs[K] > 0)) for K in (1, 2, 3)]
    L.append(f'  A1 3x3 iid-trained: K_min {km:.2f}; observed const-K gains ' + ' / '.join(f'{obs[K]:+.2f}' for K in (1, 2, 3))
             + f' % -> forced-negative prediction matches the sign at {sum(ok)}/3 K')
    L.append('  A1 3x3 K=1-trained: K_min 0.74 -> K = 1 allowed; interim target gain +2.61 % (L-238; final on TM1)')
    L += ['== Part 4: count-deadline vs age-first, S_2 + never per receiver-step (lower is better) ==']
    room = {'const1': 0.12, 'const2': 0.23, 'const3': 0.78}; red = {}
    for cap in ('const1', 'const2', 'const3', 'iid', 'cap4', 'low'):
        base = C[f'agefirst:1:{cap}']; b = base['S_tau']['2'] + base['never']
        for tau in ('2', '3'):
            c = C[f'countdeadline{tau}:1:{cap}']; v = c['S_tau']['2'] + c['never']; red[(cap, tau)] = b - v
            L.append(f'  {cap} tau {tau}: age-first {b:.3f} vs count-deadline {v:.3f} (reduction {b - v:+.3f}; F {base["F"]:.2f} vs {c["F"]:.2f}; net {base["net"]:+.2f} vs {c["net"]:+.2f})')
    B1 = all(red[(cap, tau)] <= room[cap] + 1e-9 for cap in room for tau in ('2', '3'))
    B2 = sorted({cap for (cap, tau), v in red.items() if v >= 0.2})
    L += [f'B1 reductions at constant K within the room above the floor: {"SUPPORTED" if B1 else "NOT SUPPORTED (a theorem-consistency check failed: inspect)"}',
          f'B2 cells with a reduction >= 0.2 copies (candidates for a closed-loop test): {B2 if B2 else "none -> no room"}']
    text = '\n'.join(L); print(text); (M / 'e3_net_count_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
