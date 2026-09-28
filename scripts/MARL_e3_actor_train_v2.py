#!/usr/bin/env python3
"""E3 actor v2: behaviour-cloning warm start from frozen MP2, then MAPPO fine-tuning on the team reward.

Why: the from-scratch MAPPO pilot (MARL_e3_actor_train.py, e3_actor_s0_*) learned slowly: after
1,440 episodes its select-split sum of waiting was about 3,600 against about 4,040 for a random
policy and 1,730 for MP2.  Warm-starting a policy by imitation and fine-tuning it with the task
objective is a standard recipe; nothing new is invented here.

Stage 1 (BC): on the TRAIN split, run MP2 with the deployed protocol (prefix scheduler, i.i.d.
capacities); at every step record the actor input CommAdapter.encode(view) of every receiver (its
OWN restricted view) and MP2's action on that same view.  MP2 reads the delivered downstream
queues, so imitating it requires reading messages.  Fit ActorNet by cross-entropy; checkpoint
selection by greedy select-split sum of waiting.
Stage 2 (critic warm-up): value-only updates on actor rollouts (the actor frozen) so that the
first PPO steps do not use a random critic.
Stage 3 (MAPPO): MARL_e3_actor_train's loss and splits, from the BC actor, with a smaller learning
rate; checkpoint selection on the select split.  The BC-only actor and the final actor are both
kept (ckpt_bc.pt, ckpt_best.pt).
Every actor step runs inside no_oracle_access and passes the access invariants (the imported
episode()); the critic's privileged global state is used in training only.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from models.marl_comm_actor import CommAdapter, ActorNet, CentralCritic
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios, episode, TRAIN, SELECT

SOURCES = ['scripts/MARL_e3_actor_train_v2.py', 'scripts/MARL_e3_actor_train.py', 'models/marl_comm_actor.py',
           'scripts/MARL_hetero_target_diag.py', 'envs/external/cityflow_hetero_mirror.py', 'envs/external/cityflow_hetero.py',
           'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py', 'scripts/DIAG_cityflow_set_objective_hops.py']


def bc_data(sc, eps, adapter):
    X, Y = [], []
    for seed, load in eps:
        env, topo, down, onward = sc.env(seed, load); adapter.reset()
        for t in range(N_DEC):
            with no_oracle_access(env):
                order, K = grant(env); env.submit_profile(prefix_sets(order, K), R=0)
                views = env.transmit(); env.verify_mirror()
                if env.check_access_invariants(views):
                    raise AssertionError('access invariant')
                acts = {i: mp2_action(v, topo[i], down, onward) for i, v in views.items()}
                for i in range(env.n_agents):
                    X.append(adapter.encode(views[i], 'actual')); Y.append(acts[i])
                adapter.remember(views); env.step(acts)
    return np.stack(X), np.array(Y)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    sc = Scenarios(out); env0, topo0, _, _ = sc.env(*TRAIN[0])
    adapter = CommAdapter(topo0, N_DEC, env0.action_interval); m = adapter.m
    mask = torch.as_tensor(adapter.valid_mask())
    actor = ActorNet(adapter.dim, a.hidden)
    cfg = dict(vars(a), algo='BC from frozen MP2 on the restricted views, critic warm-up, then MAPPO (PPO clip 0.2, GAE 0.99/0.95)',
               reward='-(total waiting after step)/100, team-shared', n_dec=N_DEC, scheduler='prefix, R = 0, i.i.d. capacities')
    (out / 'config.json').write_text(json.dumps(cfg, indent=1)); (out / 'schema.json').write_text(json.dumps(adapter.schema(), indent=1))
    log = open(out / 'log.jsonl', 'a'); t0 = time.perf_counter()

    def greedy(X):
        with torch.no_grad():
            return actor(torch.as_tensor(X), mask).argmax(-1).numpy(), None

    def sample(X):
        with torch.no_grad():
            d = torch.distributions.Categorical(logits=actor(torch.as_tensor(X), mask)); A = d.sample()
            return A.numpy(), d.log_prob(A).numpy()

    def evaluate(policy):
        qs = [sum(episode(sc, s, h, policy, adapter)[0]) for s, h in SELECT]
        return float(np.mean(qs)), qs

    mp2_sel, _ = evaluate('mp2'); print(f'MP2 on select: {mp2_sel:.1f}', flush=True)
    # ---------------- stage 1: BC
    X, Y = bc_data(sc, TRAIN, adapter); agent = np.tile(np.arange(m), len(Y) // m)
    Xs = torch.as_tensor(X); Yt = torch.as_tensor(Y); Mt = mask[torch.as_tensor(agent)]
    print(f'[{time.perf_counter() - t0:.0f}s] BC data: {len(Y)} samples from {len(TRAIN)} MP2 episodes', flush=True)
    opt = torch.optim.Adam(actor.parameters(), lr=a.bc_lr); best = np.inf
    for ep in range(1, a.bc_epochs + 1):
        perm = torch.randperm(len(Y)); tot = 0.0
        for b in perm.split(512):
            loss = nn.functional.cross_entropy(actor(Xs[b], Mt[b]), Yt[b]); opt.zero_grad(); loss.backward(); opt.step(); tot += loss.item() * len(b)
        with torch.no_grad():
            acc = float((actor(Xs, Mt).argmax(-1) == Yt).float().mean())
        rec = dict(stage='bc', epoch=ep, loss=tot / len(Y), train_acc=acc)
        if ep % a.bc_eval_every == 0 or ep == a.bc_epochs:
            sel, _ = evaluate(greedy); rec.update(select_queue_sum=sel, mp2_select=mp2_sel)
            if sel < best:
                best = sel; torch.save(dict(actor=actor.state_dict(), it=0, bc_epoch=ep, select=sel, config=cfg, schema=adapter.schema()), out / 'ckpt_bc.pt')
        log.write(json.dumps(rec) + '\n'); log.flush()
        print(f'[{time.perf_counter() - t0:.0f}s] BC ep {ep}: loss {rec["loss"]:.3f} acc {acc:.3f}' +
              (f' | select {rec["select_queue_sum"]:.0f} (MP2 {mp2_sel:.0f})' if 'select_queue_sum' in rec else ''), flush=True)
    ck = torch.load(out / 'ckpt_bc.pt', weights_only=False); actor.load_state_dict(ck['actor']); bc_sel = ck['select']
    # ---------------- stage 2 + 3: critic warm-up, then MAPPO
    critic = None; best_rl = bc_sel; torch.save(dict(ck, stage='bc'), out / 'ckpt_best.pt')
    for it in range(1, a.warmup + a.iters + 1):
        warm = it <= a.warmup
        batch = [episode(sc, *TRAIN[k], sample, adapter, record=True)[1] for k in rng.choice(len(TRAIN), a.eps_per_iter, replace=False)]
        if critic is None:
            critic = CentralCritic(batch[0]['S'][0].shape[0], a.hidden)
            copt = torch.optim.Adam(critic.parameters(), lr=a.critic_lr); aopt = torch.optim.Adam(actor.parameters(), lr=a.lr)
        Xb = torch.as_tensor(np.stack([np.stack(b['X']) for b in batch])); S = torch.as_tensor(np.stack([np.stack(b['S']) for b in batch]))
        A = torch.as_tensor(np.stack([np.stack(b['A']) for b in batch])); LP = torch.as_tensor(np.stack([np.stack(b['LP']) for b in batch]))
        R = torch.as_tensor(np.array([b['R'] for b in batch], np.float32))
        with torch.no_grad():
            V = critic(S)
        adv = torch.zeros_like(R); last = torch.zeros(R.shape[0])
        for t in reversed(range(R.shape[1])):
            nv = V[:, t + 1] if t + 1 < R.shape[1] else torch.zeros(R.shape[0])
            d_ = R[:, t] + 0.99 * nv - V[:, t]; last = d_ + 0.99 * 0.95 * last; adv[:, t] = last
        ret = adv + V; advn = (adv - adv.mean()) / (adv.std() + 1e-8)
        E, T = R.shape; idx = np.arange(E * T)
        Xf, Sf, Af, LPf = Xb.reshape(E * T, m, -1), S.reshape(E * T, -1), A.reshape(E * T, m), LP.reshape(E * T, m)
        advf, retf = advn.reshape(-1), ret.reshape(-1); st = []
        for _ in range(a.epochs):
            rng.shuffle(idx)
            for mb in np.array_split(idx, max(1, len(idx) // a.minibatch)):
                mb = torch.as_tensor(mb)
                vl = ((critic(Sf[mb]) - retf[mb]) ** 2).mean(); copt.zero_grad(); vl.backward()
                nn.utils.clip_grad_norm_(critic.parameters(), 0.5); copt.step()
                if not warm:
                    d = torch.distributions.Categorical(logits=actor(Xf[mb], mask)); lp = d.log_prob(Af[mb])
                    ratio = torch.exp(lp - LPf[mb]); ad = advf[mb][:, None]
                    pl = -torch.min(ratio * ad, torch.clamp(ratio, 0.8, 1.2) * ad).mean() - a.ent * d.entropy().mean()
                    aopt.zero_grad(); pl.backward(); nn.utils.clip_grad_norm_(actor.parameters(), 0.5); aopt.step()
                    st.append(pl.item())
        rec = dict(stage='warmup' if warm else 'mappo', it=it, train_queue_sum=float(-R.sum(1).mean() * 100), value_loss=vl.item(),
                   policy_loss=float(np.mean(st)) if st else None, seconds=time.perf_counter() - t0)
        if not warm and ((it - a.warmup) % a.eval_every == 0 or it == a.warmup + a.iters):
            sel, _ = evaluate(greedy); rec.update(select_queue_sum=sel, mp2_select=mp2_sel, bc_select=bc_sel)
            ckr = dict(actor=actor.state_dict(), critic=critic.state_dict(), it=it, select=sel, stage='mappo', config=cfg, schema=adapter.schema())
            torch.save(ckr, out / 'ckpt_last.pt')
            if sel < best_rl:
                best_rl = sel; torch.save(ckr, out / 'ckpt_best.pt'); rec['best'] = True
        log.write(json.dumps(rec) + '\n'); log.flush()
        print(f'[{rec["seconds"]:.0f}s] {rec["stage"]} it {it}: train Σwait {rec["train_queue_sum"]:.0f} vl {rec["value_loss"]:.3f}' +
              (f' | select {rec["select_queue_sum"]:.0f} (BC {bc_sel:.0f}, MP2 {mp2_sel:.0f})' if 'select_queue_sum' in rec else ''), flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_hashes=h0, mp2_select=mp2_sel, bc_select=bc_sel,
        best_select=best_rl, seconds=time.perf_counter() - t0), indent=1))
    print('COMPLETE', out, 'MP2', mp2_sel, 'BC', bc_sel, 'best', best_rl, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True); p.add_argument('--seed', type=int, default=0)
    p.add_argument('--bc-epochs', type=int, default=30); p.add_argument('--bc-lr', type=float, default=1e-3); p.add_argument('--bc-eval-every', type=int, default=5)
    p.add_argument('--warmup', type=int, default=20); p.add_argument('--iters', type=int, default=300)
    p.add_argument('--eps-per-iter', type=int, default=8); p.add_argument('--epochs', type=int, default=4); p.add_argument('--minibatch', type=int, default=64)
    p.add_argument('--lr', type=float, default=5e-5); p.add_argument('--critic-lr', type=float, default=1e-3); p.add_argument('--ent', type=float, default=0.001)
    p.add_argument('--hidden', type=int, default=128); p.add_argument('--eval-every', type=int, default=10); p.add_argument('--threads', type=int, default=2)
    main(p.parse_args())
