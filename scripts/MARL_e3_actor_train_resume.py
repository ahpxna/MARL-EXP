#!/usr/bin/env python3
"""E3 actor trainer with EXACT resume (28/09; scratch s4 lost ~1,640 iterations to three CityFlow hangs).

The training loop is MARL_e3_actor_train.py's (scratch recipe) or, with --p-mix > 0, MARL_e3_actor_train_mix.py's
(its episode() with p_mix = 0 is identical to the scratch one), line for line in its random-number consumption.
Added:
  * FULL training state at every evaluation point, written atomically (temporary file + os.replace), so a hang or
    kill never leaves a half-written file: state_last.pt = actor, critic, Adam state, torch / numpy / mix RNG states,
    iteration, best select value, MP2 reference; ckpt_last.pt and ckpt_best.pt in the original format.
  * In-place resume: if --out exists without manifest.json and holds state_last.pt, training continues from that
    iteration with every state restored, so the result is identical to an uninterrupted run (tested with --stop-after).
    Run the watchdog WITHOUT --out so a restart resumes in place.  Every log line carries its attempt number; lines of a
    killed attempt past its last checkpoint are kept and marked, never deleted.
  * --init-from CKPT: continue from an OLD checkpoint that has no optimizer/RNG state (a declared deviation: Adam
    moments and RNG streams restart; recorded in config.json and the manifest).
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_comm_actor import CommAdapter, ActorNet, CentralCritic
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios, TRAIN, SELECT
from scripts.MARL_e3_actor_train_mix import episode

SOURCES = ['scripts/MARL_e3_actor_train_resume.py', 'scripts/MARL_e3_actor_train.py', 'scripts/MARL_e3_actor_train_mix.py',
           'models/marl_comm_actor.py', 'scripts/MARL_hetero_target_diag.py', 'envs/external/cityflow_hetero_mirror.py',
           'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py', 'models/marl_hetero_selector.py']


def atomic_save(obj, path):
    tmp = path.with_name(path.name + '.tmp'); torch.save(obj, tmp); os.replace(tmp, path)


def main(a):
    out = Path(a.out); state_f = out / 'state_last.pt'; resume = False
    if out.exists():
        if (out / 'manifest.json').exists():
            raise SystemExit(f'{out} is already complete')
        if not state_f.exists() and not a.init_from:
            raise SystemExit(f'{out} exists without state_last.pt: refusing to overwrite (park it first)')
        resume = state_f.exists()
        if (out / 'scenarios').exists():                         # make_grid_scenario refuses to overwrite (the labels-v2 crash)
            j = 0
            while (out / f'scenarios_partial_{j}').exists():
                j += 1
            (out / 'scenarios').rename(out / f'scenarios_partial_{j}')    # kept, regenerated deterministically
    else:
        out.mkdir(parents=True)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    mix_rng = np.random.default_rng([a.seed, 0x31F])
    sc = Scenarios(out); env0, topo0, _, _ = sc.env(*TRAIN[0]); adapter = CommAdapter(topo0, N_DEC, env0.action_interval)
    mask = torch.as_tensor(adapter.valid_mask()); m = adapter.m
    actor = ActorNet(adapter.dim, a.hidden); critic = None; opt = None
    cfg = dict({k: v for k, v in vars(a).items() if k not in ('stop_after',)}, algo='MAPPO (shared actor, centralised critic), PPO clip',
               gamma=0.99, lam=0.95, clip=0.2, reward='-(total waiting after step)/100, team-shared', n_dec=N_DEC, train_eps=len(TRAIN),
               select_eps=len(SELECT), scheduler='prefix of the cached-queue order, R = 0, i.i.d. capacities (env trace)' +
               ('; training mixes random +84 B candidates with probability p_mix' if a.p_mix > 0 else ''), trainer='MARL_e3_actor_train_resume.py')
    attempt = 0; start_it = 1; best = np.inf; mp2_sel = None; resumes = []
    if resume:
        S = torch.load(state_f, weights_only=False)
        if S['config']['seed'] != a.seed or S['config']['p_mix'] != a.p_mix or S['config']['iters'] != a.iters:
            raise SystemExit('state_last.pt belongs to a different configuration')
        actor.load_state_dict(S['actor']); critic = CentralCritic(S['critic_dim'], a.hidden); critic.load_state_dict(S['critic'])
        opt = torch.optim.Adam(list(actor.parameters()) + list(critic.parameters()), lr=a.lr); opt.load_state_dict(S['opt'])
        torch.set_rng_state(S['torch_rng']); rng.bit_generator.state = S['np_rng']; mix_rng.bit_generator.state = S['mix_rng']
        start_it, best, mp2_sel, attempt = S['it'] + 1, S['best'], S['mp2_sel'], S['attempt'] + 1; resumes = S['resumes'] + [dict(attempt=attempt, from_it=S['it'], time=time.ctime())]
        cfg = S['config']
        print(f'RESUMED at iteration {S["it"]} (attempt {attempt}); every state restored', flush=True)
    elif a.init_from:
        C = torch.load(a.init_from, weights_only=False); actor.load_state_dict(C['actor']); start_it = C['it'] + 1
        cfg.update(init_from=a.init_from, init_from_it=C['it'], deviation='continued from a checkpoint WITHOUT optimizer/RNG state: Adam moments and RNG streams restart')
        resumes = [dict(attempt=0, init_from=a.init_from, from_it=C['it'], time=time.ctime())]
        print(f'INIT from {a.init_from} at iteration {C["it"]} (declared deviation: no optimizer/RNG state)', flush=True)
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

    log = open(out / 'log.jsonl', 'a')
    if mp2_sel is None:
        mp2_sel, mp2_qs = evaluate('mp2'); log.write(json.dumps(dict(ref='mp2_select', mean_queue_sum=mp2_sel, per_episode=mp2_qs, attempt=attempt)) + '\n'); log.flush()
        print(f'MP2 reference on select: mean Σ waiting {mp2_sel:.1f}', flush=True)
    else:
        log.write(json.dumps(dict(resume=True, attempt=attempt, from_it=start_it - 1)) + '\n'); log.flush()
    t0 = time.perf_counter()
    for it in range(start_it, a.iters + 1):
        batch = []
        for k in rng.choice(len(TRAIN), a.eps_per_iter, replace=False):
            _, tr, _ = episode(sc, *TRAIN[k], act_sample, adapter, record=True, p_mix=a.p_mix, mix_rng=mix_rng)
            batch.append(tr)
        if critic is None:
            critic = CentralCritic(batch[0]['S'][0].shape[0], a.hidden)
            opt = torch.optim.Adam(list(actor.parameters()) + list(critic.parameters()), lr=a.lr)
        X = torch.as_tensor(np.stack([np.stack(b['X']) for b in batch])); S_ = torch.as_tensor(np.stack([np.stack(b['S']) for b in batch]))
        A = torch.as_tensor(np.stack([np.stack(b['A']) for b in batch])); LP = torch.as_tensor(np.stack([np.stack(b['LP']) for b in batch]))
        R = torch.as_tensor(np.array([b['R'] for b in batch], np.float32))
        with torch.no_grad():
            V = critic(S_)
        adv = torch.zeros_like(R); last = torch.zeros(R.shape[0])
        for t in reversed(range(R.shape[1])):
            nv = V[:, t + 1] if t + 1 < R.shape[1] else torch.zeros(R.shape[0])
            delta = R[:, t] + 0.99 * nv - V[:, t]; last = delta + 0.99 * 0.95 * last; adv[:, t] = last
        ret = adv + V; advn = (adv - adv.mean()) / (adv.std() + 1e-8)
        E, T = R.shape; idx = np.arange(E * T)
        Xf, Sf, Af, LPf = X.reshape(E * T, m, -1), S_.reshape(E * T, -1), A.reshape(E * T, m), LP.reshape(E * T, m)
        advf, retf = advn.reshape(-1), ret.reshape(-1); stats = []
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
                nn.utils.clip_grad_norm_(actor.parameters(), 0.5); nn.utils.clip_grad_norm_(critic.parameters(), 0.5)
                opt.step(); stats.append((pl.item(), vl.item(), ent.item()))
        rec = dict(it=it, attempt=attempt, train_queue_sum=float(-R.sum(1).mean() * 100), policy_loss=float(np.mean([s[0] for s in stats])),
                   value_loss=float(np.mean([s[1] for s in stats])), entropy=float(np.mean([s[2] for s in stats])), seconds=time.perf_counter() - t0)
        if it % a.eval_every == 0 or it == a.iters:
            sel, qs = evaluate(act_greedy); rec.update(select_queue_sum=sel, mp2_select=mp2_sel)
            ck = dict(actor=actor.state_dict(), critic=critic.state_dict(), it=it, select=sel, config=cfg, schema=adapter.schema())
            atomic_save(ck, out / 'ckpt_last.pt')
            if sel < best:
                best = sel; atomic_save(ck, out / 'ckpt_best.pt'); rec['best'] = True
            atomic_save(dict(actor=actor.state_dict(), critic=critic.state_dict(), critic_dim=Sf.shape[1], opt=opt.state_dict(), torch_rng=torch.get_rng_state(),
                             np_rng=rng.bit_generator.state, mix_rng=mix_rng.bit_generator.state, it=it, best=best, mp2_sel=mp2_sel, attempt=attempt,
                             resumes=resumes, config=cfg), state_f)
        log.write(json.dumps(rec) + '\n'); log.flush()
        print(f'[{rec["seconds"]:.0f}s] it {it}: train Σwait {rec["train_queue_sum"]:.0f} ent {rec["entropy"]:.3f} vl {rec["value_loss"]:.3f}' +
              (f' | select {rec["select_queue_sum"]:.0f} (MP2 {mp2_sel:.0f})' if 'select_queue_sum' in rec else ''), flush=True)
        if a.stop_after and it == a.stop_after:
            print(f'STOP after iteration {it} (test of the resume path)', flush=True); return
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_hashes=h0, best_select=best, mp2_select=mp2_sel, resumes=resumes,
                                                       seconds=time.perf_counter() - t0), indent=1))
    print('COMPLETE', out, 'best select', best, 'MP2', mp2_sel, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True); p.add_argument('--seed', type=int, default=0)
    p.add_argument('--iters', type=int, default=200); p.add_argument('--eps-per-iter', type=int, default=8)
    p.add_argument('--epochs', type=int, default=4); p.add_argument('--minibatch', type=int, default=64)
    p.add_argument('--lr', type=float, default=3e-4); p.add_argument('--ent', type=float, default=0.01)
    p.add_argument('--hidden', type=int, default=128); p.add_argument('--eval-every', type=int, default=10)
    p.add_argument('--threads', type=int, default=2); p.add_argument('--p-mix', type=float, default=0.0)
    p.add_argument('--init-from'); p.add_argument('--stop-after', type=int, default=0)
    main(p.parse_args())
