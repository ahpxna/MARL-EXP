#!/usr/bin/env python3
"""Route 2 (MARL_DEEP_RESEARCH_20260929.md): is the value of a SINGLE-AGENT action change learnable from that agent's
own actor input?  Offline development diagnostic on MARL_e3_forced_action_probe_v2.py rows.

SMV (Xue et al., IJCAI 2022) values a message as the value of the action change it induces, Q_i(s, a_i^j) - Q_i(s, a_i),
under a per-agent decomposed critic.  L-81 found that the E3 scheduling headroom is, to first order, single-agent
action-change headroom.  So the question that decides whether ANY value-based scheduler can work is whether
    g(i, a) = 3-step team gain of forcing agent i to phase a at t (prefix delivery, prefix afterwards)
is predictable from x_i, the 276-dim input the actor itself sees at t (its own lanes and phase, its cache, t).
Model: ONE MLP shared by all agents, input [x_i, onehot(a), onehot(a0_i), logit(a) - logit(a0_i)], a0_i = the
actor's own action; target g / ys; MSE over every forced (i, a != a0_i).  Floored normaliser (v8).  Epoch chosen on
SELECT tie-half pair accuracy over all (i, a) alternatives of a state.
Reported on DEV, against two training-free baselines (the actor's own logit preference logit(a) - logit(a0), and
random): pair accuracy over all alternatives of a state and within one agent's alternatives; Spearman; the realised
gain of the model's top choice (argmax) and of an abstaining rule (act only if the predicted gain exceeds tau chosen on
SELECT, grid incl. +inf), against the oracle (the state's best alternative, > 0 by 3-step hindsight).
NOTE on legality: x_i here is the view AFTER this step's prefix deliveries; a receiver-side bid would be computed on the
pre-transmission view.  A learnability test, not a deployable rule.
"""
from __future__ import annotations
import argparse, glob, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn
from scipy.stats import spearmanr

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_ranking_diag_v2 import pair_acc

SOURCES = ['scripts/MARL_e3_agent_q_train.py', 'scripts/MARL_e3_ranking_diag_v2.py']
FLOOR = 0.05


def rows_of(pattern):
    R = []
    for d in sorted(x for x in glob.glob(pattern) if Path(x).is_dir()):     # the glob also matches the .log files
        if not Path(d, 'manifest.json').exists():
            raise SystemExit(f'refusing: {d} is not COMPLETE')
        R += json.loads(Path(d, 'rows.json').read_text())
    return R


def state_arrays(r):
    """All forced alternatives of one state: features, gains, agent ids, logit baseline."""
    x = np.asarray(r['x'], np.float32); L = np.asarray(r['logits'], np.float32); j0 = r['prefix_joint']
    F, g, ag, lb = [], [], [], []
    for f in r['forced']:
        i, a = f['agent'], f['action']
        F.append(np.concatenate([x[i], np.eye(9, dtype=np.float32)[a], np.eye(9, dtype=np.float32)[j0[i]], [L[i, a] - L[i, j0[i]]]]))
        g.append(f['gain']); ag.append(i); lb.append(L[i, a] - L[i, j0[i]])
    return np.stack(F), np.asarray(g, np.float32), np.asarray(ag), np.asarray(lb, np.float32)


def metrics(score, g, ag):
    within = [pair_acc(score[ag == i], g[ag == i])[0] for i in np.unique(ag) if (ag == i).sum() > 1]
    rho = spearmanr(score, g).correlation if np.ptp(score) > 0 and np.ptp(g) > 0 else np.nan
    return pair_acc(score, g)[0], float(np.nanmean(within)), rho


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    D = {sp: [state_arrays(r) for r in rows_of(pat)] for sp, pat in (('train', a.train), ('select', a.select), ('dev', a.dev))}
    seeds_dev = [r['traffic_seed'] for r in rows_of(a.dev)]
    X = np.concatenate([d[0] for d in D['train']]); mu = X.mean(0); sd = X.std(0); sd = np.where(sd < 1e-6, 1.0, np.maximum(sd, FLOOR)).astype(np.float32)
    ys = float(np.std(np.concatenate([d[1] for d in D['train']])) + 1e-6)
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    net = nn.Sequential(nn.Linear(X.shape[1], a.hidden), nn.ReLU(), nn.Linear(a.hidden, a.hidden), nn.ReLU(), nn.Linear(a.hidden, 1))
    opt = torch.optim.Adam(net.parameters(), lr=a.lr, weight_decay=1e-5)
    T = lambda d: torch.as_tensor((d[0] - mu) / sd)

    def scores(sp):
        with torch.no_grad():
            return [net(T(d)).squeeze(-1).numpy() * ys for d in D[sp]]

    def mean_pa(sp, sc):
        return float(np.nanmean([metrics(s, d[1], d[2])[0] for s, d in zip(sc, D[sp])]))

    def decide(sp, sc, tau):
        return float(np.mean([float(d[1][int(np.argmax(s))]) if s.max() > tau else 0.0 for s, d in zip(sc, D[sp])]))

    curve = []; best, saved, best_ep = -np.inf, None, None; t0 = time.perf_counter()
    for ep in range(a.epochs):
        for k in rng.permutation(len(D['train'])):
            d = D['train'][k]; loss = ((net(T(d)).squeeze(-1) - torch.as_tensor(d[1] / ys)) ** 2).mean()
            opt.zero_grad(); loss.backward(); opt.step()
        if ep % 4 == 3 or ep == a.epochs - 1:
            tr = mean_pa('train', scores('train')); sel = mean_pa('select', scores('select')); dv = mean_pa('dev', scores('dev'))
            curve.append(dict(epoch=ep, train_pa=tr, select_pa=sel, dev_pa_description_only=dv))
            if sel > best:
                best, saved, best_ep = sel, {k: v.clone() for k, v in net.state_dict().items()}, ep
            print(f'[{time.perf_counter() - t0:.0f}s] agent-Q s{a.seed} ep {ep}: pair acc train {tr:.4f} select {sel:.4f} dev {dv:.4f}', flush=True)
    net.load_state_dict(saved); ssel, sdev = scores('select'), scores('dev')
    grid = [-np.inf, 0.0] + sorted({float(np.quantile(s, q)) for s in ssel for q in (0.9, 0.99)}) + [np.inf]
    tau = max(grid, key=lambda t: decide('select', ssel, t))
    res = {}
    for name, sc in (('model', sdev), ('logit_baseline', [d[3] for d in D['dev']]),
                     ('random', [np.random.default_rng(7 + k).random(len(d[1])) for k, d in enumerate(D['dev'])])):
        M = np.array([metrics(s, d[1], d[2]) for s, d in zip(sc, D['dev'])], float)
        res[name] = dict(pair_acc=float(np.nanmean(M[:, 0])), within_agent_pair_acc=float(np.nanmean(M[:, 1])), spearman=float(np.nanmean(M[:, 2])),
                         argmax_gain=float(np.mean([float(d[1][int(np.argmax(s))]) for s, d in zip(sc, D['dev'])])),
                         per_state_pair_acc=[float(x) for x in M[:, 0]])
    res['model']['abstain_gain'] = decide('dev', sdev, tau); res['model']['abstain_act_rate'] = float(np.mean([s.max() > tau for s in sdev]))
    orc = float(np.mean([d[1].max() for d in D['dev']])); mean_alt = float(np.mean([d[1].mean() for d in D['dev']]))
    blob = dict(seed=a.seed, best_epoch=best_ep, select_pa=best, curve=curve, tau=('+inf' if tau > 0 else '-inf') if np.isinf(tau) else float(tau),
                dev=res, dev_oracle=orc, dev_mean_alternative=mean_alt, dev_traffic_seeds=seeds_dev, n_states={sp: len(D[sp]) for sp in D},
                evidence_class='offline development diagnostic (learnability)', source_hashes=h0)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / f'job_agentq_s{a.seed}.json').write_text(json.dumps(blob))
    torch.save(dict(state=saved, mu=mu, sd=sd, ys=ys, hidden=a.hidden, dim=int(X.shape[1]), tau=blob['tau']), out / f'model_agentq_s{a.seed}.pt')
    m_, l_ = res['model'], res['logit_baseline']
    print(f"agent-Q s{a.seed}: DEV pair acc {m_['pair_acc']:.4f} (logit {l_['pair_acc']:.4f}, random {res['random']['pair_acc']:.4f}) | within-agent {m_['within_agent_pair_acc']:.4f} "
          f"(logit {l_['within_agent_pair_acc']:.4f}) | argmax gain {m_['argmax_gain']:+.2f} (logit {l_['argmax_gain']:+.2f}, random {res['random']['argmax_gain']:+.2f}) | "
          f"abstain gain {m_['abstain_gain']:+.2f} act {m_['abstain_act_rate']:.2f} | oracle {orc:+.2f}, mean alternative {mean_alt:+.2f}", flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--train', required=True, help='glob of COMPLETE probe v2 dirs'); p.add_argument('--select', required=True); p.add_argument('--dev', required=True)
    p.add_argument('--out', required=True); p.add_argument('--seed', type=int, default=0); p.add_argument('--epochs', type=int, default=40)
    p.add_argument('--lr', type=float, default=1e-3); p.add_argument('--hidden', type=int, default=256); p.add_argument('--threads', type=int, default=2)
    main(p.parse_args())
