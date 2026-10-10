#!/usr/bin/env python3
"""v12 RECEIVER ADAPTATION trainer (03/10/2026 19:1x EDT; external audit METHOD_ADVANTAGE_PLAN / RECEIVER_ADAPTATION_SPEC
W1-W3; WHY_NOT_WIN_REVIEW_20261003).  Imports v11 (not edited: the NYC jobs import it) and adds:
  W1  --init-from PARENT: the student starts from the parent receiver's weights (architecture, hidden size, schema, relay,
      quantisation, order and teacher checked against the parent's config); a FRESH Adam optimiser; budget counters start at 0;
      the manifest records the parent's sha256.  (v11's resume is a different thing and is not used.)
  W2  PAIRED episodes: two CityFlow instances of the same scenario, one per channel (new / old capacity process), stepped with
      the SAME actions (chosen by the student on the NEW channel's view, or by the teacher with probability beta).  CityFlow is
      deterministic and the channel never touches physics, so the two stay physically identical — asserted at every step
      (queue and every agent's lane counts).  The old-channel views are therefore genuine, causal old-channel histories on
      the new channel's trajectory (privileged TRAINING augmentation, like the teacher's counterfactual view).
  W3  methods, same architecture, optimiser, epochs, minibatch, learning rate and simulated-episode budget:
      ft_new  : new-channel episodes only; CE to the teacher's action.
      ft_mix  : alternating new / old independent episodes (half each); CE.
      pct     : ft_mix data; CE + lam * KL(pi0(x) || pi(x)) on samples where pi0's action is teacher-acceptable (focal-
                distillation / PCT-style preservation on the SAME input).
      paired  : half as many PAIRED episodes (each costs 2 simulated episodes): CE on x_new weighted 1 + gamma * h, plus rho *
                CE on x_old, plus lam * KL(pi0(x_old) || pi(x_old)) where pi0(x_old) is acceptable; h = 1 iff pi0's action on
                x_old is teacher-acceptable and its action on x_new is not (teacher-relative channel regression; a proxy).
      Teacher-acceptable set A_T = valid actions whose teacher logit is within --margin of the maximum (teacher != oracle).
Budget = simulated episodes on all channels (a paired episode counts 2); teacher queries are counted separately.
Checkpoints are written at the budget points of --save-at (episodes) in the trainers' format (actor, config, schema), so the
existing evaluators load them.  SELF-CHECKS: zero updates => saved weights == parent weights (b0 checkpoint, asserted);
--identity-check: new cap == old cap must give x_new == x_old at every step; physical identity of paired envs every step.
Run under scripts/MARL_grid_relay_wrapper.py for 4x4 (as the parents were trained).
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn
import torch.nn.functional as F

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_e3_actor_distill_v11 as V11
from scripts.MARL_e3_actor_distill_v11 import load_actor, apply_capacity, N_DEC, Scenarios, TRAIN, SELECT, DV, no_oracle_access
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized
import models.marl_relay_v2 as RV2

SOURCES = ['scripts/MARL_e3_actor_adapt_v12.py', 'scripts/MARL_e3_actor_distill_v11.py', 'models/marl_relay_v2.py', 'models/marl_relay_v3.py',
           'models/marl_comm_actor_quant.py', 'models/marl_comm_actor.py', 'models/marl_comm_actor_set.py', 'models/marl_delivery_agefirst.py',
           'scripts/MARL_e3_actor_train_delivery_v7.py', 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']
CHECK_KEYS = ('arch', 'hidden', 'relay', 'quant', 'order', 'student_delivery', 'student_adapter', 'student_view', 'codebook', 'teacher')


def set_cap(cap):
    DV.DELIVERY['capacity'] = cap


def run_episode(sc, seed, load, adapter, t_adapter, student, teacher, mask, beta, rng, caps, collect, identity=False):
    """One physical episode observed through len(caps) channels (caps[0] = the channel the behaviour policy reads).
    Returns (queue sum, records) with records = [(X per channel (list of (m, dim)), teacher logits (m, A) or None)]."""
    envs = []
    for cap in caps:
        env, _, _, _ = sc.env(seed, load); set_cap(cap); apply_capacity(env, seed, load, env.n_agents); envs.append(env)
    m = envs[0].n_agents; iv = envs[0].action_interval; prevs = [None] * len(caps); q = 0.0; data = []
    for t in range(N_DEC):
        for env in envs:
            with no_oracle_access(env):
                DV.deliver(env, seed, load, t)
        lt = None
        if collect:
            cf = [envs[0].counterfactual_view(i, [j for j in range(m) if j != i]) for i in range(m)]     # TRAINING label only
            Xt = np.stack([t_adapter.encode(v, 'actual') for v in cf])
        Xs = []
        for k, env in enumerate(envs):
            with no_oracle_access(env):
                views = env.transmit(); sv = RV2.merge_views(views, prevs[k], t, iv, 'age'); prevs[k] = sv
                Xs.append(np.stack([adapter.encode(sv[i], 'actual') for i in range(m)]))
        if identity and len(Xs) == 2 and not np.array_equal(Xs[0], Xs[1]):
            raise SystemExit(f'SELF-CHECK FAIL: identical channels gave different views at t={t}')
        with torch.no_grad():
            a_s = student(torch.as_tensor(Xs[0]), mask).argmax(-1).numpy()
            if collect:
                lt = teacher(torch.as_tensor(Xt), mask).numpy(); a_t = lt.argmax(-1)
        use_t = collect and rng.random() < beta
        acts = {i: int((a_t if use_t else a_s)[i]) for i in range(m)}
        recs = []
        for env in envs:
            with no_oracle_access(env):
                recs.append(env.step(acts)[2])
        own = adapter.own_dim
        if any(r['queue'] != recs[0]['queue'] for r in recs[1:]) or any(not np.array_equal(Xs[0][:, :own], x[:, :own]) for x in Xs[1:]):
            raise SystemExit(f'SELF-CHECK FAIL: paired environments diverged physically at t={t}')
        q += float(recs[0]['queue'])
        if collect:
            data.append((Xs, lt))
    return q, data


def acceptable(lt, mask_np, margin):
    l = np.where(mask_np, lt, -np.inf)                                             # lt: (m, A); mask_np: (m, A)
    return (l >= l.max(-1, keepdims=True) - margin) & mask_np


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    pck = torch.load(a.init_from, weights_only=False); pcfg = pck['config']
    DV.DELIVERY['mode'] = pcfg['student_delivery']
    if pcfg.get('order') == 'agefirst':
        from models.marl_delivery_agefirst import deliver_agefirst
        DV.deliver = deliver_agefirst
    if pcfg.get('relay') != 'age' or pcfg.get('arch', 'set') != 'set':
        raise SystemExit('v12 supports the relay-age set-actor receivers only')
    sc = Scenarios(out); env0, topo0, _, _ = sc.env(*TRAIN[0])
    SA = quantized(CommAdapter, json.loads((ROOT / pcfg['codebook']).read_text()), pcfg['quant']) if pcfg.get('quant') else CommAdapter
    adapter = SA(topo0, N_DEC, env0.action_interval); t_adapter = CommAdapter(topo0, N_DEC, env0.action_interval)
    if pck['schema'] != adapter.schema():
        raise SystemExit('parent schema differs from the rebuilt adapter')
    teacher_path = a.teacher or pcfg['teacher']
    if Path(teacher_path).resolve() != Path(pcfg['teacher']).resolve():
        raise SystemExit('the teacher must be the parent\'s teacher')
    tck, TNet = load_actor(teacher_path); teacher = TNet(adapter.dim, tck['config']['hidden']); teacher.load_state_dict(tck['actor']); teacher.eval()
    for p_ in teacher.parameters():
        p_.requires_grad_(False)
    student = SetActorNet(adapter.dim, pcfg['hidden'])
    if not a.from_scratch:                                   # E11 (03/10 23:2x): --from-scratch keeps the random initialisation
        student.load_state_dict(pck['actor'])
    pi0 = SetActorNet(adapter.dim, pcfg['hidden']); pi0.load_state_dict(pck['actor']); pi0.eval()
    for p_ in pi0.parameters():
        p_.requires_grad_(False)
    mask = torch.as_tensor(adapter.valid_mask()); mask_np = adapter.valid_mask().astype(bool); m = env0.n_agents
    opt = torch.optim.Adam(student.parameters(), lr=a.lr)                          # FRESH optimiser (not the parent's)
    cfg = dict({k: pcfg.get(k) for k in CHECK_KEYS}, set_actor=True, trainer='MARL_e3_actor_adapt_v12.py', parent=a.init_from,
               parent_sha256=sha(a.init_from), parent_config=pcfg, method=a.method, from_scratch=a.from_scratch, new_cap=a.new_cap, old_cap=a.old_cap, budget=a.budget,
               eps_per_iter=a.eps_per_iter, beta0=a.beta0, gamma=a.gamma, lam=a.lam, rho=a.rho, margin=a.margin, lr=a.lr, epochs=a.epochs,
               minibatch=a.minibatch, buffer=a.buffer, seed=a.seed, capacity=a.new_cap, iters=None,
               privileged='teacher labels from env.counterfactual_view; old-channel shadow views from a lockstep simulator (training only)')

    def save(tag, extra):
        torch.save(dict(actor=student.state_dict(), config=cfg, schema=adapter.schema(), **extra), out / f'ckpt_{tag}.pt')
    save('b0', dict(budget_used=0))
    b0 = torch.load(out / 'ckpt_b0.pt', weights_only=False)['actor']
    same = all(torch.equal(b0[k], pck['actor'][k]) for k in pck['actor'])
    if same == a.from_scratch:                                    # warm start: b0 == parent; from scratch: b0 != parent
        raise SystemExit('SELF-CHECK FAIL: zero-update checkpoint vs parent is wrong for this initialisation')
    if a.identity_check:                                                            # x_new == x_old when the two channels are equal
        run_episode(sc, *TRAIN[0], adapter, t_adapter, student, teacher, mask, 0.0, rng, [a.new_cap, a.new_cap], True, identity=True)
    used = 0; tq = 0; n_ep = 0; buf = []; log = open(out / 'log.jsonl', 'a'); t0 = time.perf_counter(); saves = sorted(set(a.save_at)); it = 0
    while used < a.budget:
        it += 1; beta = a.beta0; batch = dict(x=[], y=[], w=[], ag=[], px=[], pt=[], pag=[]); hstat = [0, 0]
        n_phys = a.eps_per_iter if a.method != 'paired' else max(1, a.eps_per_iter // 2)
        for e, k in enumerate(rng.choice(len(TRAIN), n_phys, replace=False)):
            s, h = TRAIN[k]
            if a.method == 'ft_new':
                caps = [a.new_cap]
            elif a.method in ('ft_mix', 'pct'):                         # independent episodes, alternating new / old
                caps = [a.new_cap if n_ep % 2 == 0 else a.old_cap]
            else:
                caps = [a.new_cap, a.old_cap]
            _, d = run_episode(sc, s, h, adapter, t_adapter, student, teacher, mask, beta, rng, caps, True)
            used += len(caps); tq += len(d); n_ep += 1
            for Xs, lt in d:
                y = lt.argmax(-1); A = acceptable(lt, mask_np, a.margin); ag = np.arange(m)
                if a.method == 'paired':
                    with torch.no_grad():
                        an = pi0(torch.as_tensor(Xs[0]), mask).argmax(-1).numpy(); ao = pi0(torch.as_tensor(Xs[1]), mask).argmax(-1).numpy()
                    hh = A[ag, ao] & ~A[ag, an]; hstat[0] += int(hh.sum()); hstat[1] += m
                    batch['x'] += [Xs[0], Xs[1]]; batch['y'] += [y, y]; batch['w'] += [1.0 + a.gamma * hh, np.full(m, a.rho)]; batch['ag'] += [ag, ag]
                    keep = A[ag, ao]
                    if a.lam > 0 and keep.any():
                        batch['px'].append(Xs[1][keep]); batch['pag'].append(ag[keep])
                else:
                    batch['x'].append(Xs[0]); batch['y'].append(y); batch['w'].append(np.ones(m)); batch['ag'].append(ag)
                    if a.method == 'pct' and a.lam > 0:
                        with torch.no_grad():
                            a0 = pi0(torch.as_tensor(Xs[0]), mask).argmax(-1).numpy()
                        keep = A[ag, a0]
                        if keep.any():
                            batch['px'].append(Xs[0][keep]); batch['pag'].append(ag[keep])
        buf.append({k: (np.concatenate(v) if v else None) for k, v in batch.items()}); buf = buf[-a.buffer:]
        X = torch.as_tensor(np.concatenate([b['x'] for b in buf])); Y = torch.as_tensor(np.concatenate([b['y'] for b in buf]), dtype=torch.long)
        W = torch.as_tensor(np.concatenate([b['w'] for b in buf]), dtype=torch.float32); AG = torch.as_tensor(np.concatenate([b['ag'] for b in buf]))
        PX = [b['px'] for b in buf if b['px'] is not None]; PX = torch.as_tensor(np.concatenate(PX)) if PX else None
        PAG = torch.as_tensor(np.concatenate([b['pag'] for b in buf if b['pag'] is not None])) if PX is not None else None
        P0 = None
        if PX is not None:
            with torch.no_grad():
                P0 = F.log_softmax(pi0(PX, mask[PAG]), -1)
        idx = np.arange(len(Y)); losses = []
        for _ in range(a.epochs):
            rng.shuffle(idx); mbs = np.array_split(idx, max(1, len(idx) // a.minibatch))
            pidx = np.array_split(rng.permutation(len(PX)), len(mbs)) if PX is not None else [None] * len(mbs)
            for mb, pb in zip(mbs, pidx):
                mb = torch.as_tensor(mb); logit = student(X[mb], mask[AG[mb]])
                ce = F.cross_entropy(logit, Y[mb], reduction='none'); loss = (W[mb] * ce).sum() / W[mb].sum()
                if pb is not None and len(pb):
                    pb = torch.as_tensor(pb); lp = F.log_softmax(student(PX[pb], mask[PAG[pb]]), -1); p0 = P0[pb]
                    kl = (p0.exp() * (p0 - lp)).masked_fill(~mask[PAG[pb]], 0.0).sum(-1).mean()
                    loss = loss + a.lam * kl
                opt.zero_grad(); loss.backward(); nn.utils.clip_grad_norm_(student.parameters(), 1.0); opt.step(); losses.append(loss.item())
        rec = dict(it=it, used=used, teacher_queries=tq, loss=float(np.mean(losses)), n=int(len(Y)), n_pres=int(len(PX)) if PX is not None else 0,
                   h_rate=(hstat[0] / hstat[1]) if hstat[1] else None, seconds=time.perf_counter() - t0)
        log.write(json.dumps(rec) + '\n'); log.flush()
        print(f"[{rec['seconds']:.0f}s] it {it}: used {used} eps, loss {rec['loss']:.3f}, n {rec['n']}, pres {rec['n_pres']}" + (f", h {rec['h_rate']:.3f}" if rec['h_rate'] is not None else ''), flush=True)
        while saves and used >= saves[0]:
            save(f'b{saves[0]}', dict(budget_used=used, teacher_queries=tq, it=it)); saves.pop(0)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'config.json').write_text(json.dumps(cfg, indent=1, default=str))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', budget_used=used, teacher_queries=tq, iterations=it,
                                                       parent_sha256=cfg['parent_sha256'], source_hashes=h0, seconds=time.perf_counter() - t0), indent=1))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--init-from', required=True); p.add_argument('--teacher'); p.add_argument('--out', required=True)
    p.add_argument('--method', choices=['ft_new', 'ft_mix', 'pct', 'paired'], required=True)
    p.add_argument('--new-cap', default='iid'); p.add_argument('--old-cap', default='const1')
    p.add_argument('--budget', type=int, default=80, help='simulated episodes, all channels (a paired episode counts 2)')
    p.add_argument('--save-at', type=int, nargs='+', default=[8, 16, 40, 80])
    p.add_argument('--eps-per-iter', type=int, default=8); p.add_argument('--buffer', type=int, default=40)
    p.add_argument('--epochs', type=int, default=2); p.add_argument('--minibatch', type=int, default=256); p.add_argument('--lr', type=float, default=1e-3)
    p.add_argument('--beta0', type=float, default=0.0, help='probability that the teacher drives a step (constant)')
    p.add_argument('--gamma', type=float, default=0.0); p.add_argument('--lam', type=float, default=0.0); p.add_argument('--rho', type=float, default=1.0)
    p.add_argument('--margin', type=float, default=0.25); p.add_argument('--seed', type=int, default=0); p.add_argument('--threads', type=int, default=1)
    p.add_argument('--identity-check', action='store_true')
    p.add_argument('--from-scratch', action='store_true', help='E11: random initialisation (same architecture, recipe and budgets)')
    main(p.parse_args())
