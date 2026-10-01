#!/usr/bin/env python3
"""E3 actor pilot: MAPPO (shared actor, centralised critic) on PROTOCOL_HETERO_v0 (readiness audit P2).

Loop per decision step (the deployed protocol, every call inside no_oracle_access):
  scheduler context -> committed cached-queue order -> capacity reveal (the env's seeded i.i.d.
  trace) -> prefix profile, R = 0 -> transmit -> each receiver acts on ITS OWN view through
  CommAdapter -> env.step.
Objective: the TEAM reward r_t = -(total waiting after step t)/100, shared by all agents; finite
horizon N_DEC with time in the state, terminal value 0.  PPO clip 0.2, GAE (gamma 0.99, lambda 0.95),
entropy bonus, advantage normalised per batch.  CTDE: the critic reads a privileged global state
(every agent's own sensor) during training only; acting never reads it.
Splits: training episodes from train seeds 301-364 x headways 8, 16; checkpoint selection on the
select split 401-408 (greedy actions, mean sum of waiting), never on development or test seeds.
Reference on the same select episodes: frozen MP2 with the same prefix communication.
Outputs in --out: config.json, schema.json, log.jsonl, ckpt_last.pt, ckpt_best.pt, manifest.json.
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
from models.marl_comm_actor import CommAdapter, ActorNet, CentralCritic, N_PH
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_target_diag import scenario, new_env, grant

SOURCES = ['scripts/MARL_e3_actor_train.py', 'models/marl_comm_actor.py', 'scripts/MARL_hetero_target_diag.py',
           'envs/external/cityflow_hetero_mirror.py', 'envs/external/cityflow_hetero.py',
           'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py']
TRAIN = [(s, h) for s in range(301, 365) for h in (8.0, 16.0)]
SELECT = [(s, h) for s in range(401, 409) for h in (8.0, 16.0)]


class Scenarios:
    def __init__(self, out):
        self.out = out; self.cache = {}

    def env(self, seed, load):
        if (seed, load) not in self.cache:
            self.cache[(seed, load)] = scenario(self.out, seed, load)
        return new_env(self.cache[(seed, load)], seed, load)


def episode(sc, seed, load, policy, adapter=None, record=False, variant='actual', rng=None):
    """policy: 'mp2' or a callable (X, mask) -> actions.  Returns queues (and a trajectory if record)."""
    env, topo, down, onward = sc.env(seed, load); m = env.n_agents
    if adapter is not None:
        adapter.reset()
    traj = dict(X=[], S=[], A=[], LP=[], R=[]); queues = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            order, K = grant(env)
            env.submit_profile(prefix_sets(order, K), R=0)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            if policy == 'mp2':
                acts = {i: mp2_action(v, topo[i], down, onward) for i, v in views.items()}
            else:
                X = np.stack([adapter.encode(views[i], variant, rng) for i in range(m)])
                a, lp = policy(X)
                acts = {i: int(a[i]) for i in range(m)}
                if record:
                    traj['X'].append(X); traj['S'].append(adapter.global_state(views, t)); traj['A'].append(a); traj['LP'].append(lp)
                adapter.remember(views)
            _, _, rec = env.step(acts)
        queues.append(float(rec['queue']))
        if record:
            traj['R'].append(-rec['queue'] / 100.0)
    return queues, traj, env.episode_summary()


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    sc = Scenarios(out)
    env0, topo0, _, _ = sc.env(*TRAIN[0]); adapter = CommAdapter(topo0, N_DEC, env0.action_interval)
    mask = torch.as_tensor(adapter.valid_mask()); m = adapter.m
    actor = ActorNet(adapter.dim, a.hidden); critic = None; opt = None      # critic sized on the first batch
    cfg = dict(vars(a), algo='MAPPO (shared actor, centralised critic), PPO clip', gamma=0.99, lam=0.95, clip=0.2,
               reward='-(total waiting after step)/100, team-shared', n_dec=N_DEC, train_eps=len(TRAIN), select_eps=len(SELECT),
               scheduler='prefix of the cached-queue order, R = 0, i.i.d. capacities (env trace)')
    (out / 'config.json').write_text(json.dumps(cfg, indent=1)); (out / 'schema.json').write_text(json.dumps(adapter.schema(), indent=1))

    def act_sample(X):
        with torch.no_grad():
            lg = actor(torch.as_tensor(X), mask); d = torch.distributions.Categorical(logits=lg); A = d.sample()
            return A.numpy(), d.log_prob(A).numpy()

    def act_greedy(X):
        with torch.no_grad():
            return actor(torch.as_tensor(X), mask).argmax(-1).numpy(), None

    def evaluate(policy):
        qs = [sum(episode(sc, s, h, policy, adapter)[0]) for s, h in SELECT]
        return float(np.mean(qs)), qs

    mp2_sel, mp2_qs = evaluate('mp2')
    log = open(out / 'log.jsonl', 'a'); log.write(json.dumps(dict(ref='mp2_select', mean_queue_sum=mp2_sel, per_episode=mp2_qs)) + '\n'); log.flush()
    print(f'MP2 reference on select: mean Σ waiting {mp2_sel:.1f}', flush=True)
    best = np.inf; t0 = time.perf_counter()
    for it in range(1, a.iters + 1):
        batch = []
        for k in rng.choice(len(TRAIN), a.eps_per_iter, replace=False):
            _, tr, _ = episode(sc, *TRAIN[k], act_sample, adapter, record=True)
            batch.append(tr)
        if critic is None:
            critic = CentralCritic(batch[0]['S'][0].shape[0], a.hidden)
            opt = torch.optim.Adam(list(actor.parameters()) + list(critic.parameters()), lr=a.lr)
        X = torch.as_tensor(np.stack([np.stack(b['X']) for b in batch]))          # (E, T, m, dim)
        S = torch.as_tensor(np.stack([np.stack(b['S']) for b in batch]))          # (E, T, sdim)
        A = torch.as_tensor(np.stack([np.stack(b['A']) for b in batch]))          # (E, T, m)
        LP = torch.as_tensor(np.stack([np.stack(b['LP']) for b in batch]))
        R = torch.as_tensor(np.array([b['R'] for b in batch], np.float32))         # (E, T)
        with torch.no_grad():
            V = critic(S)
        adv = torch.zeros_like(R); last = torch.zeros(R.shape[0])
        for t in reversed(range(R.shape[1])):
            nv = V[:, t + 1] if t + 1 < R.shape[1] else torch.zeros(R.shape[0])
            delta = R[:, t] + 0.99 * nv - V[:, t]; last = delta + 0.99 * 0.95 * last; adv[:, t] = last
        ret = adv + V; advn = (adv - adv.mean()) / (adv.std() + 1e-8)
        E, T = R.shape; idx = np.arange(E * T)
        Xf, Sf, Af, LPf = X.reshape(E * T, m, -1), S.reshape(E * T, -1), A.reshape(E * T, m), LP.reshape(E * T, m)
        advf, retf = advn.reshape(-1), ret.reshape(-1)
        stats = []
        for _ in range(a.epochs):
            rng.shuffle(idx)
            for mb in np.array_split(idx, max(1, len(idx) // a.minibatch)):
                mb = torch.as_tensor(mb)
                lg = actor(Xf[mb], mask); d = torch.distributions.Categorical(logits=lg)
                lp = d.log_prob(Af[mb]); ratio = torch.exp(lp - LPf[mb]); ad = advf[mb][:, None]
                pl = -torch.min(ratio * ad, torch.clamp(ratio, 0.8, 1.2) * ad).mean()
                ent = d.entropy().mean(); vl = ((critic(Sf[mb]) - retf[mb]) ** 2).mean()
                loss = pl + 0.5 * vl - a.ent * ent
                opt.zero_grad(); loss.backward()
                nn.utils.clip_grad_norm_(actor.parameters(), 0.5); nn.utils.clip_grad_norm_(critic.parameters(), 0.5)   # separate: value scale must not shrink the policy step
                opt.step()
                stats.append((pl.item(), vl.item(), ent.item()))
        rec = dict(it=it, train_queue_sum=float(-R.sum(1).mean() * 100), policy_loss=float(np.mean([s[0] for s in stats])),
                   value_loss=float(np.mean([s[1] for s in stats])), entropy=float(np.mean([s[2] for s in stats])),
                   seconds=time.perf_counter() - t0)
        if it % a.eval_every == 0 or it == a.iters:
            sel, qs = evaluate(act_greedy); rec.update(select_queue_sum=sel, mp2_select=mp2_sel)
            ck = dict(actor=actor.state_dict(), critic=critic.state_dict(), it=it, select=sel, config=cfg, schema=adapter.schema())
            torch.save(ck, out / 'ckpt_last.pt')
            if sel < best:
                best = sel; torch.save(ck, out / 'ckpt_best.pt'); rec['best'] = True
        log.write(json.dumps(rec) + '\n'); log.flush()
        print(f'[{rec["seconds"]:.0f}s] it {it}: train Σwait {rec["train_queue_sum"]:.0f} ent {rec["entropy"]:.3f} '
              f'vl {rec["value_loss"]:.3f}' + (f' | select {rec["select_queue_sum"]:.0f} (MP2 {mp2_sel:.0f})' if 'select_queue_sum' in rec else ''), flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_hashes=h0, best_select=best, mp2_select=mp2_sel,
                                                       seconds=time.perf_counter() - t0), indent=1))
    print('COMPLETE', out, 'best select', best, 'MP2', mp2_sel, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True); p.add_argument('--seed', type=int, default=0)
    p.add_argument('--iters', type=int, default=200); p.add_argument('--eps-per-iter', type=int, default=8)
    p.add_argument('--epochs', type=int, default=4); p.add_argument('--minibatch', type=int, default=64)
    p.add_argument('--lr', type=float, default=3e-4); p.add_argument('--ent', type=float, default=0.01)
    p.add_argument('--hidden', type=int, default=128); p.add_argument('--eval-every', type=int, default=10)
    p.add_argument('--threads', type=int, default=2)
    main(p.parse_args())
