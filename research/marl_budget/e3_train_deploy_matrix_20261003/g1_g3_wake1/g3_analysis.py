import json, numpy as np
from pathlib import Path
O = Path('/Users/phanan/cig-amf-main/research/city_sim/c0_v3_20261002')
EX = json.load(open('/private/tmp/claude-502/-Users-phanan-cig-amf-main/976002e4-6f9b-4c75-8890-ea54dcea033f/scratchpad/agentB/g3_c0_exact.json'))
R = {s: dict(np.load(O / f'seed_{s}' / 'regrets.npz')) for s in range(5)}
CJ = {s: json.load(open(O / f'seed_{s}' / 'cells.json'))['cells'] for s in range(5)}
RES = json.load(open(O / 'result.json')); KC = RES['addendum']['stats']
T9 = ['FT', 'EXT', 'CUT', 'A1', 'A2', 'A3', 'A4', 'A5', 'A6']
def rk(z):
    z = np.asarray(z, float); o = np.argsort(z, kind='stable'); r = np.empty(len(z)); r[o] = np.arange(len(z))
    for v in np.unique(z): r[z == v] = r[z == v].mean()
    return r
def sp(x, y):
    rx, ry = rk(x), rk(y); return float(np.corrcoef(rx, ry)[0, 1]) if rx.std() > 0 and ry.std() > 0 else float('nan')
cells = []
for L in T9:
    for s in range(5):
        if f'Z_ACT|{L}|plain' not in R[s] or f'Z_{L}|{L}|plain' not in R[s]: continue
        e = EX[f'{L}|Z_ACT_s{s}']
        cells.append(dict(L=L, s=s, Delta=R[s][f'Z_ACT|{L}|plain'].mean() - R[s][f'Z_{L}|{L}|plain'].mean(),
                          Exc=R[s][f'Z_ACT|{L}|plain'].mean() - R[0][f'Z*_{L}|{L}|plain'].mean(),
                          oos_real=CJ[s][f'Z_ACT|{L}|oos_mass'], oos=e['oos_mass'], w_oos=e['w_oos'], w_in=e['w_in'], w_tot=e['pdl'], exc_exact=e['excess'],
                          K=KC[L]['K'], S_exit=KC[L]['S_exit'], dis_oos=e['dis_rate_oos'], dis_all=e['dis_rate_all']))
print(f'n cells = {len(cells)} ((seed, light) with a specialist: lights {T9}; seeds 0-4 for FT/EXT/CUT, 0-2 for A1-A6)')
print('\n1) where the exact excess of the frozen learned car Z_ACT comes from (seed means over 0-4, exact model):')
for L in ['ACT'] + T9 + ['PROBE']:
    es = [EX[f'{L}|Z_ACT_s{s}'] for s in range(5)]; tb = EX[f'{L}|Zstar_ACT_table']
    ex = np.mean([e['excess'] for e in es]); wo = np.mean([e['w_oos'] for e in es]); wi = np.mean([e['w_in'] for e in es])
    print(f'  {L:5s} exact excess {ex:6.2f} = OOS cells {wo:6.2f} + in-support cells {wi:6.2f} (OOS share {wo / ex:5.2f}) | raw OOS mass {np.mean([e["oos_mass"] for e in es]):.3f} '
          f'| timeout {np.mean([e["timeout"] for e in es]):.4f} | PDL - excess {np.mean([e["pdl"] - e["excess"] for e in es]):+.4f} | exact frozen TABLE excess {tb["excess"]:.2f} (OOS share {tb["w_oos"] / max(tb["excess"], 1e-12):.2f})')
ACTex = np.mean([EX[f'ACT|Z_ACT_s{s}']['excess'] for s in range(5)])
print(f'  (on its own training light ACT the car already carries excess {ACTex:.2f}: the in-support baseline)')
print('\n2) agreement exact vs realised:  Spearman over cells(exact excess, realised excess) = %.3f; Pearson %.3f; realised OOS vs exact OOS mass max |diff| %.3f' % (
    sp([c['exc_exact'] for c in cells], [c['Exc'] for c in cells]), np.corrcoef([c['exc_exact'] for c in cells], [c['Exc'] for c in cells])[0, 1],
    max(abs(c['oos_real'] - c['oos']) for c in cells)))
preds = ['oos_real', 'oos', 'w_oos', 'w_in', 'w_tot', 'K', 'S_exit', 'dis_all']
for tgt in ('Delta', 'Exc'):
    y = [c[tgt] for c in cells]
    print(f'\n3) target = {tgt} (realised, regrets.npz).  Spearman over all {len(cells)} cells / over the 9 light means (seeds 0-2):')
    for p in preds:
        lm = [np.mean([c[p] for c in cells if c['L'] == L and c['s'] <= 2]) for L in T9]; ym = [np.mean([c[tgt] for c in cells if c['L'] == L and c['s'] <= 2]) for L in T9]
        print(f'   {p:9s} cells {sp([c[p] for c in cells], y):+.3f}   lights {sp(lm, ym):+.3f}')
# fit on one group of lights, test on the other (linear calibration y = a + b x on cells; rank and RMSE on held-out cells)
GA, GB = ['FT', 'EXT', 'CUT', 'A1', 'A2'], ['A3', 'A4', 'A5', 'A6']
for tgt in ('Delta', 'Exc'):
    print(f'\n4) target {tgt}: fit on one group of light controllers, test on the other (cells; linear calibration)')
    for tr, te in ((GA, GB), (GB, GA)):
        for p in ('oos', 'w_oos', 'w_tot', 'K'):
            A = [c for c in cells if c['L'] in tr]; B = [c for c in cells if c['L'] in te]
            xa = np.array([c[p] for c in A]); ya = np.array([c[tgt] for c in A]); xb = np.array([c[p] for c in B]); yb = np.array([c[tgt] for c in B])
            if xa.std() == 0: print(f'   fit {tr} -> test {te}  {p:6s}: predictor constant on the fit group'); continue
            b, a = np.polyfit(xa, ya, 1); pr = a + b * xb
            print(f'   fit {"+".join(tr)} -> test {"+".join(te)}  {p:6s}: held-out Spearman {sp(xb, yb):+.3f}  RMSE {np.sqrt(np.mean((pr - yb) ** 2)):6.2f} (sd y {yb.std():.2f})')
# leave-one-light-out rank of the held-out light by each predictor (light means, seeds 0-2)
print('\n5) in-support lights only (raw OOS mass = 0): FT, CUT, A1, A2, A6 -- Spearman of w_in / w_tot / K with Delta over their cells:')
ins = [c for c in cells if c['L'] in ('FT', 'CUT', 'A1', 'A2', 'A6')]
for p in ('oos', 'w_in', 'w_tot', 'K', 'dis_all'):
    print(f'   {p:8s} {sp([c[p] for c in ins], [c["Delta"] for c in ins]):+.3f}  (n {len(ins)})')
