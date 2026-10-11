import sys, time, json, numpy as np
sys.path.insert(0, '/private/tmp/claude-502/-Users-phanan-cig-amf-main/976002e4-6f9b-4c75-8890-ea54dcea033f/scratchpad/agentB')
from c0_exact import *
torch.set_num_threads(1); t0 = time.time()
LIGHTS = ['ACT', 'FT', 'EXT', 'CUT', 'A1', 'A2', 'A3', 'A4', 'A5', 'A6', 'PROBE']; TMAX = 39
Vact, Qact, hact = tables('ACT')
nets = {s: load_net(s) for s in range(5)}
res = {}
for L in LIGHTS:
    V, Q, h = tables(L); TM = V.shape[3]; oos = (np.arange(TM) > TMAX)[None, None, None, :]
    rs = evaluate(Q.argmin(-1), L, V, Q, h); floor = rs['cost']
    pols = {f'Z_ACT_s{s}': net_actions(nets[s], TM) for s in range(5)}; pols['Zstar_ACT_table'] = table_actions(Vact, hact, TM)
    for nm, pi in pols.items():
        r = evaluate(pi, L, V, Q, h); occ = r['occ']; tot = occ.sum(); wa = occ * r['adv']
        res[(L, nm)] = dict(excess=r['cost'] - floor, pdl=r['pdl'], timeout=r['alive'], floor_cost=floor, steps=float(tot),
                            oos_mass=float(occ[np.broadcast_to(oos, occ.shape)].sum() / tot), w_oos=float(wa[np.broadcast_to(oos, occ.shape)].sum()),
                            w_in=float(wa[~np.broadcast_to(oos, occ.shape)].sum()),
                            dis_rate_oos=float((occ * (r['adv'] > 1e-9))[np.broadcast_to(oos, occ.shape)].sum() / tot),
                            dis_rate_all=float((occ * (r['adv'] > 1e-9)).sum() / tot))
    print(f'{L}: floor E[cost] {floor:.2f}  ' + ' '.join(f'{nm[-2:] if "s" in nm[-2:] else "tab"}:{res[(L, nm)]["excess"]:.2f}' for nm in pols) + f'  [{time.time() - t0:.0f}s]', flush=True)
json.dump({f'{k[0]}|{k[1]}': v for k, v in res.items()}, open('/private/tmp/claude-502/-Users-phanan-cig-amf-main/976002e4-6f9b-4c75-8890-ea54dcea033f/scratchpad/agentB/g3_c0_exact.json', 'w'), indent=0)
