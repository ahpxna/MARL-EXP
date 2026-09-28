#!/usr/bin/env python3
"""LEARNED SchedNet-style scheduling baseline for a FROZEN E3 actor (readiness audit P3; critical path 3.4).

SchedNet (Kim et al., ICLR 2019) learns WHO talks under a shared bandwidth from each agent's own
observation.  Adaptation to PROTOCOL_HETERO_v0: before the capacity reveal every SENDER j computes a
scalar weight w_j = g(own sensor of j, own phase, time, agent id) and sends it (1 B each, 9 B + 1 B
header = 10 B charged every step); the stream order is by decreasing weight; each receiver decodes
its first k_i senders (R = 0); the frozen actor acts on its view.  g is trained by PPO on the TEAM
reward with the actor frozen; during training the order is sampled from the Plackett-Luce law of the
weights (log-probability of the sampled permutation), at evaluation it is the sorted order.  The
centralised critic reads the privileged global state (training only).
What is NOT adapted: SchedNet's message encoder and its joint actor training (the actor here is the
frozen E3 actor, as the selector comparisons require).
Modes: train (select split for checkpoint selection) and eval (closed-loop rows on --traffic-seeds in
the MARL_hetero_closed_loop_report.py format: methods prefix and schednet_learned/s<seed>).
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from models.marl_comm_actor import CentralCritic, N_PH, SCALE_Q, SCALE_T
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios, TRAIN, SELECT
from scripts.MARL_e3_continuation_labels import Policy

SOURCES = ['scripts/MARL_e3_schednet_train.py', 'scripts/MARL_e3_continuation_labels.py', 'scripts/MARL_e3_actor_train.py',
           'models/marl_comm_actor.py', 'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py']
W_BYTES = 10


def sender_obs(view, m, n_dec):
    return np.concatenate([np.asarray(view.lane_vehicles, np.float32).ravel() / SCALE_Q, np.asarray(view.lane_waiting, np.float32).ravel() / SCALE_Q,
                           np.eye(N_PH, dtype=np.float32)[int(view.own_phase)], [float(view.own_phase_elapsed) / SCALE_T, view.decision_step / n_dec],
                           np.eye(m, dtype=np.float32)[view.agent]]).astype(np.float32)


class WeightNet(nn.Module):
    def __init__(self, dim, h=64):
        super().__init__()
        self.net = nn.Sequential(nn.Linear(dim, h), nn.Tanh(), nn.Linear(h, h), nn.Tanh(), nn.Linear(h, 1))

    def forward(self, x):
        return self.net(x).squeeze(-1)


def pl_logprob(s, order):
    """log P(order) under Plackett-Luce with scores s (1-D tensor)."""
    so = s[order]; return (so - torch.logcumsumexp(so.flip(0), 0).flip(0)).sum()


def pl_sample(s, rng):
    g = -np.log(-np.log(rng.random(len(s))))            # Gumbel trick: sorting s + Gumbel samples PL
    return np.argsort(-(s + g))


def episode(sc, seed, load, pol_ck, wnet, mode, rng=None, record=False, adapter_state=False):
    env, topo, _, _ = sc.env(seed, load); m = env.n_agents; pol = Policy(pol_ck, topo, env.action_interval)
    traj = dict(O=[], S=[], order=[], LP=[], R=[]); total = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            pre = {j: env._build_view(j) for j in range(m)}                      # each sender's own view
        if mode == 'prefix':
            with no_oracle_access(env):
                order = tuple(env.scheduler_context().cached_queue_ranking()); wb = 0
        else:
            O = np.stack([sender_obs(pre[j], m, N_DEC) for j in range(m)])
            with torch.no_grad():
                s = wnet(torch.as_tensor(O)).numpy()
            order = tuple(int(x) for x in (pl_sample(s, rng) if mode == 'sample' else np.argsort(-s, kind='stable')))
            wb = W_BYTES
            if record:
                traj['O'].append(O); traj['S'].append(pol.adapter.global_state(pre, t)); traj['order'].append(np.array(order))
                with torch.no_grad():
                    traj['LP'].append(float(pl_logprob(torch.as_tensor(s), torch.as_tensor(np.array(order)))))
        with no_oracle_access(env):
            env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
            env.submit_profile(prefix_sets(order, K), R=0)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            _, _, rec = env.step(pol.act(views))
        total += rec['accounted_bytes'] + wb
        if record:
            traj['R'].append(-rec['queue'] / 100.0)
    row = dict(episode=f'seed{seed}_load{load:g}', queue_sum=float(sum(r['queue'] for r in env.step_records)),
               finished=int(env.step_records[-1]['finished']), bytes=int(total), edits=0, summary=env.episode_summary())
    return row, traj


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    pol_ck = torch.load(Path(a.actor), weights_only=False); sc = Scenarios(out)
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    m = 9; wnet = WeightNet(12 + 12 + N_PH + 2 + m); critic = None
    if a.mode == 'eval':
        ck = torch.load(Path(a.ckpt), weights_only=False); wnet.load_state_dict(ck['wnet']); rows = []; t0 = time.perf_counter()
        for seed in a.traffic_seeds:
            for load in (8.0, 16.0):
                for meth in ('prefix', f'schednet_learned/s{ck["seed"]}'):
                    r, _ = episode(sc, seed, load, pol_ck, wnet, 'prefix' if meth == 'prefix' else 'greedy'); r['method'] = meth; rows.append(r)
                    print(f'[{time.perf_counter() - t0:.0f}s] {r["episode"]} {meth}: queue_sum {r["queue_sum"]:.0f} bytes {r["bytes"]}', flush=True)
                    tmp = out / '.rows.json'; tmp.write_text(json.dumps(rows, default=float)); os.replace(tmp, out / 'rows.json')
        (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0), indent=1)); return
    opt = torch.optim.Adam(wnet.parameters(), lr=a.lr)
    evaluate = lambda mode: float(np.mean([episode(sc, s, h, pol_ck, wnet, mode)[0]['queue_sum'] for s, h in SELECT]))
    pre_sel = evaluate('prefix'); best = np.inf; log = open(out / 'log.jsonl', 'a'); t0 = time.perf_counter()
    print(f'prefix (same actor) on select: {pre_sel:.1f}', flush=True)
    for it in range(1, a.iters + 1):
        batch = [episode(sc, *TRAIN[k], pol_ck, wnet, 'sample', rng, record=True)[1] for k in rng.choice(len(TRAIN), a.eps_per_iter, replace=False)]
        if critic is None:
            critic = CentralCritic(batch[0]['S'][0].shape[0], 128); copt = torch.optim.Adam(critic.parameters(), lr=1e-3)
        S = torch.as_tensor(np.stack([np.stack(b['S']) for b in batch])); R = torch.as_tensor(np.array([b['R'] for b in batch], np.float32))
        with torch.no_grad():
            V = critic(S)
        adv = torch.zeros_like(R); last = torch.zeros(R.shape[0])
        for t in reversed(range(R.shape[1])):
            nv = V[:, t + 1] if t + 1 < R.shape[1] else torch.zeros(R.shape[0])
            d_ = R[:, t] + 0.99 * nv - V[:, t]; last = d_ + 0.99 * 0.95 * last; adv[:, t] = last
        ret = (adv + V).reshape(-1); advn = ((adv - adv.mean()) / (adv.std() + 1e-8)).reshape(-1)
        O = [o for b in batch for o in b['O']]; ORD = [o for b in batch for o in b['order']]; LP0 = torch.as_tensor([x for b in batch for x in b['LP']])
        Sf = S.reshape(-1, S.shape[-1]); idx = np.arange(len(O))
        for _ in range(a.epochs):
            rng.shuffle(idx)
            for mb in np.array_split(idx, max(1, len(idx) // 64)):
                lp = torch.stack([pl_logprob(wnet(torch.as_tensor(O[k])), torch.as_tensor(ORD[k])) for k in mb])
                ratio = torch.exp(lp - LP0[mb]); ad = advn[mb]
                pl = -torch.min(ratio * ad, torch.clamp(ratio, 0.8, 1.2) * ad).mean()
                opt.zero_grad(); pl.backward(); nn.utils.clip_grad_norm_(wnet.parameters(), 0.5); opt.step()
                vl = ((critic(Sf[mb]) - ret[mb]) ** 2).mean(); copt.zero_grad(); vl.backward(); nn.utils.clip_grad_norm_(critic.parameters(), 0.5); copt.step()
        rec = dict(it=it, train_queue_sum=float(-R.sum(1).mean() * 100), seconds=time.perf_counter() - t0)
        if it % a.eval_every == 0 or it == a.iters:
            sel = evaluate('greedy'); rec.update(select=sel, prefix_select=pre_sel)
            if sel < best:
                best = sel; torch.save(dict(wnet=wnet.state_dict(), it=it, select=sel, seed=a.seed, actor=a.actor), out / 'ckpt_best.pt')
        log.write(json.dumps(rec) + '\n'); log.flush()
        print(f'[{rec["seconds"]:.0f}s] it {it}: train Σwait {rec["train_queue_sum"]:.0f}' +
              (f' | select {rec["select"]:.0f} (prefix {pre_sel:.0f})' if 'select' in rec else ''), flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0, best_select=best, prefix_select=pre_sel), indent=1))
    print('COMPLETE', out, 'best', best, 'prefix', pre_sel, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mode', choices=['train', 'eval'], default='train'); p.add_argument('--actor', required=True); p.add_argument('--out', required=True)
    p.add_argument('--ckpt'); p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 917)))
    p.add_argument('--seed', type=int, default=0); p.add_argument('--iters', type=int, default=200); p.add_argument('--eps-per-iter', type=int, default=8)
    p.add_argument('--epochs', type=int, default=4); p.add_argument('--lr', type=float, default=3e-4); p.add_argument('--eval-every', type=int, default=10)
    p.add_argument('--threads', type=int, default=1)
    main(p.parse_args())
