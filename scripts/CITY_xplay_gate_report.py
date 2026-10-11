#!/usr/bin/env python3
"""Report of B4F (research/city_sim/PROTOCOL_CITY_FLEET_GATE_20261004.md; written 04/10/2026 wake 2 while the panel ran).
SELF-CHECKS G-0 (ACT: gate fired 0 times and rows bit-identical to the plain h0 rows) and G-0b (the gate fires under RL-H).
FB-1 .. FB-3 registered; FB-4 / FB-5 reported (FB-5 = offline brake-propensity probe of each fleet network, no simulation)."""
import json
from pathlib import Path
import numpy as np
import torch

G = Path('research/city_sim/xplay_gate_20261004'); H0 = Path('research/city_sim/xplay_h0_20261004'); SEEDS = [100, 101, 102, 103, 104]; T = [0, 1, 2, 3]
Q7DIR = Path('research/city_sim/q7_cross_version_20261002'); Q7BDIR = Path('research/city_sim/q7b_contract_20261002')
ACC = np.array([-3.0, -2.0, -1.0, 0.0, 1.0, 2.0])


def load(d, key):
    R = {}
    for f in d.glob('*.json'):
        if f.name.startswith('report'):
            continue
        x = json.loads(f.read_text())
        if x.get('status') == 'COMPLETE':
            for r in x['rows']:
                k = key(r)
                if k is not None:
                    R[k] = r
    return R


def probe(fleet_t):
    p = Q7DIR / 'L-ACT.pt' if fleet_t == 0 else Q7BDIR / f'L-ACT_t{fleet_t}.pt'; net = torch.load(p, weights_only=False)['net']; net.eval()
    d, v, tau = np.meshgrid(np.linspace(0.02, 1.0, 25), np.linspace(0.0, 1.0, 15), np.arange(0, 201, 2.0), indexing='ij')
    O = np.stack([d.ravel(), v.ravel(), np.ones(d.size), np.zeros(d.size), tau.ravel() / 60.0, np.ones(d.size)], 1).astype(np.float32)
    with torch.no_grad():
        a = net(torch.as_tensor(O)).argmax(1).numpy()
    brake = ACC[a] < 0; t = tau.ravel()
    return float(brake[t <= 50].mean()), float(brake[t > 50].mean())


def main():
    Gr = load(G, lambda r: (r['light'], r['fleet'], r['gate'], r['seed'])); P = load(H0, lambda r: (r['light'], r['fleet'], r['seed']) if r['sense'] == 'default' else None)
    out = [f'== B4F fleet-side support gate ({len(Gr)} gated runs)']
    lights = ['ACT'] + [f'{f}:{t}' for f in ('RL-H', 'RL-C50', 'RL-J') for t in T]; fleets = [f'L-ACT:{t}' for t in T]
    miss = [(l, f, g, s) for l in lights for f in fleets for g in ('fallback', 'clip') for s in SEEDS if (l, f, g, s) not in Gr]
    g0 = [(f, g, s) for f in fleets for g in ('fallback', 'clip') for s in SEEDS if (('ACT', f, g, s) in Gr) and (Gr[('ACT', f, g, s)]['gate_fired'] != 0 or any(
        Gr[('ACT', f, g, s)][m] != P[('ACT', f, s)][m] for m in ('timeloss', 'approach_cost', 'timeloss_agent', 'hidden_a', 'unfinished')))]
    fired = sum(Gr[(f'RL-H:{i}', f, 'fallback', s)]['gate_fired'] for i in T for f in fleets for s in SEEDS if (f'RL-H:{i}', f, 'fallback', s) in Gr)
    ok = not miss and not g0 and fired > 0
    out.append(f"SELF-CHECK G-0 (ACT: 0 firings, bit-identical to plain): {40 - len(g0)}/40 runs; G-0b gate firings under RL-H {fired}; missing {len(miss)} {miss[:3]} -> {'PASS' if ok else 'FAIL'}")
    if not ok:
        (G / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    gv = lambda l, f, g, s, m: P[(l, f, s)][m] if g == 'none' else Gr[(l, f, g, s)][m]
    cells = lambda fam: [(f'{fam}:{i}', f'L-ACT:{j}') for i in T for j in T]
    res = {}; rng = np.random.default_rng(0)
    for fam in ('RL-H', 'RL-C50', 'RL-J'):
        for g in ('fallback', 'clip'):
            D = np.array([[gv(l, f, g, s, 'timeloss_agent') - gv(l, f, 'none', s, 'timeloss_agent') for s in SEEDS] for l, f in cells(fam)])
            bs = [D[rng.integers(0, 16, 16)][:, rng.integers(0, 5, 5)].mean() for _ in range(2000)]; lo, hi = np.percentile(bs, [2.5, 97.5])
            rA0 = np.mean([[gv(l, f, 'none', s, 'timeloss_agent') - gv('ACT', f, 'none', s, 'timeloss_agent') for s in SEEDS] for l, f in cells(fam)])
            city = np.array([np.mean([gv(l, f, g, s, 'timeloss') for s in SEEDS]) for l, f in cells(fam)])
            act = np.array([np.mean([gv('ACT', f, 'none', s, 'timeloss') for s in SEEDS]) for l, f in cells(fam)])
            plain_city = np.array([np.mean([gv(l, f, 'none', s, 'timeloss') for s in SEEDS]) for l, f in cells(fam)])
            dh = np.mean([[gv(l, f, g, s, 'timeloss_human') - gv(l, f, 'none', s, 'timeloss_human') for s in SEEDS] for l, f in cells(fam)])
            share = np.mean([Gr[(l, f, g, s)]['gate_fired'] / max(1, Gr[(l, f, g, s)]['decisions']) for l, f in cells(fam) for s in SEEDS])
            tele = np.mean([Gr[(l, f, g, s)]['teleports'] for l, f in cells(fam) for s in SEEDS])
            res[f'{fam}/{g}'] = dict(dA=float(D.mean()), ci=[float(lo), float(hi)], rA_plain=float(rA0), city=city.tolist(), act=act.tolist(), dh=float(dh), share=float(share))
            tag = {('RL-H', 'fallback'): 'FB-1', }.get((fam, g), 'FB-4')
            out.append(f"{tag} {fam} x L-ACT, gate {g}: agent-TL change vs plain {D.mean():+.2f} [{lo:+.2f}, {hi:+.2f}] s/veh (plain agent regression vs ACT {rA0:+.2f}); "
                       f"city TL {city.mean():.2f} (plain {plain_city.mean():.2f}, ACT with the plain fleet {act.mean():.2f}); cells below ACT {int((city < act).sum())}/16 "
                       f"(plain {int((plain_city < act).sum())}/16); human TL change {dh:+.2f}; gated share {share:.3f}; teleports/run {tele:.1f}"
                       + (f" -> {'SUPPORTED' if hi < 0 else 'NOT SUPPORTED'}" if tag == 'FB-1' else ''))
            if (fam, g) == ('RL-H', 'fallback'):
                out.append(f"FB-2 city TL below ACT in {int((city < act).sum())}/16 cells (>= 12 needed) -> {'SUPPORTED' if (city < act).sum() >= 12 else 'NOT SUPPORTED'}")
                out.append(f"FB-3 human TL change {dh:+.3f} s/veh (<= +0.5 needed) -> {'SUPPORTED' if dh <= 0.5 else 'NOT SUPPORTED'}")
                M = np.array([[np.mean([gv(f'RL-H:{i}', f'L-ACT:{j}', g, s, 'timeloss_agent') - gv('ACT', f'L-ACT:{j}', 'none', s, 'timeloss_agent') for s in SEEDS]) for j in T] for i in T])
                out.append('   agent regression with the fallback gate (rows RL-H_t, cols L-ACT_t\'): ' + ' | '.join(' '.join(f'{x:+6.2f}' for x in row) for row in M))
    # FB-5 offline probe
    pr = {t: probe(t) for t in T}
    rP = [np.mean([[np.mean([P[(f'RL-H:{i}', f'L-ACT:{t}', s)]['approach_cost'] - P[('ACT', f'L-ACT:{t}', s)]['approach_cost'] for s in SEEDS])] for i in T]) for t in T]
    rk = lambda z: np.argsort(np.argsort(z)).astype(float)
    out.append('FB-5 offline brake propensity on synthetic GREEN observations (tau <= 50 / tau > 50) vs mean regression r under RL-H: ' +
               ', '.join(f"L-ACT_{t} {pr[t][0]:.3f}/{pr[t][1]:.3f} r {rP[t]:+.2f}" for t in T) +
               f"; Spearman(OOS brake, r) {np.corrcoef(rk(np.array([pr[t][1] for t in T])), rk(np.array(rP)))[0, 1]:+.2f}, "
               f"Spearman(OOS - in-support brake, r) {np.corrcoef(rk(np.array([pr[t][1] - pr[t][0] for t in T])), rk(np.array(rP)))[0, 1]:+.2f} (n = 4)")
    res['probe'] = {str(t): pr[t] for t in T}; res['r_fleet'] = rP
    txt = '\n'.join(out) + '\n'; (G / 'report.txt').write_text(txt); (G / 'report.json').write_text(json.dumps(res, indent=1)); print(txt)


if __name__ == '__main__':
    main()
