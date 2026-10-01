"""Zero-byte baseline for direction (a): each state, the single (agent, phase) override with the largest ensemble Qhat,
taken if Qhat > tau (tau chosen on SELECT, same grid as MARL_e3_advantage_bid_eval), realised = its forced 3-step gain.
Also restricted to the (agent, phase) changes that some feasible MESSAGE candidate of the state induces (single-change)."""
import glob, json, sys
from pathlib import Path
import numpy as np
ROOT = Path('/Users/phanan/cig-amf-main'); sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_advantage_bid_eval import load_q, q_table
A = ROOT / 'research/marl_budget/e3_scratch_seeds34_20260928/actor_s3'; V = ROOT / 'research/marl_budget/e3_forced_v2_20260929/e3_scratch_seeds34_20260928_actor_s3'
Qs = [load_q(p) for p in sorted(glob.glob(str(A / 'agent_q/model_agentq_s*.pt')))]
def per(sp):
    out = []
    for r in json.loads(Path(V, f'{sp}_0', 'rows.json').read_text()):
        QT = np.mean([q_table(Q, r) for Q in Qs], 0); j0 = r['prefix_joint']
        f = [(x['agent'], x['action'], x['gain']) for x in r['forced']]
        sc = np.array([QT[i, a] for i, a, _ in f]); g = np.array([x[2] for x in f])
        reach = set()
        for mm in r['message']:
            d = [(i, a) for i, a in enumerate(mm['joint']) if a != j0[i]]
            if len(d) == 1:
                reach.add(d[0])
        rm = np.array([(i, a) in reach for i, a, _ in f])
        out.append(dict(sc=sc, g=g, rm=rm))
    return out
S, D = per('select'), per('dev')
def dec(P, tau, restrict):
    v = []
    for p in P:
        sc = np.where(p['rm'], p['sc'], -np.inf) if restrict else p['sc']
        k = int(np.argmax(sc)); v.append(float(p['g'][k]) if np.isfinite(sc[k]) and sc[k] > tau else 0.0)
    return float(np.mean(v))
for restrict in (False, True):
    grid = [-np.inf, 0.0] + sorted({float(np.quantile(p['sc'], q)) for p in S for q in (0.9, 0.99)}) + [np.inf]
    tau = max(grid, key=lambda t: dec(S, t, restrict))
    orc = np.mean([p['g'][p['rm']].max() if (restrict and p['rm'].any()) else (0.0 if restrict else p['g'].max()) for p in D])
    print(f"{'reachable-only' if restrict else 'all single changes'}: DEV gain argmax {dec(D, -np.inf, restrict):+.2f}, tau rule {dec(D, tau, restrict):+.2f} (tau {tau}), oracle {orc:+.2f}, "
          f"states with a reachable single change {np.mean([p['rm'].any() for p in D]):.2f}")
