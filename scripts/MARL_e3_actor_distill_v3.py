#!/usr/bin/env python3
"""v3 (30/09 00:4x; ledger L-147): v2 plus two CONTROL options for "is the 0-byte student's gain about communication?":
  --teacher-view {counterfactual_full (v1/v2 default), own}: own = the teacher acts on the SAME delivered view as the env gives
    (a no-communication teacher sees no messages; a prefix teacher sees its prefix deliveries with its trained adapter);
  --student-view {actual (default), none}: none = the student's input has every message removed (a 0-byte student even when
    the env delivers messages for the teacher).  Defaults reproduce v2.
v2 docstring follows.
v2 (29/09 22:5x; ledger L-130): v1 plus --student-adapter {default, freshonly}: the student's input under its delivery may drop
stale cached blocks (FO receiver, L-124 ... L-129), so that training-time communication (the teacher) and deployment
messages (fresh only) are combined.  Default reproduces v1.
v1 docstring follows.
Privileged-teacher distillation for E3 (29/09 22:1x; ledger L-122): "communicate to learn, act with fewer bytes".

Asymmetric / teacher-student idea (asymmetric actor-critic, Pinto et al. 2018; privileged teacher-student).  The
TEACHER is a trained actor that acts on FULL, fresh delivery (every receiver decodes all m-1 packets; e.g. set_full_s0,
-7.5 % against set_none).  The STUDENT sees only what the deployed protocol gives it (--student-delivery: none = zero
bytes, prefix, rxq, nbr, with the capacities of the env) and is trained by DAgger:
  * at every training step the teacher's input is the receiver's view with every other sender's CURRENT packet delivered
    (env.counterfactual_view, an ORACLE call used for TRAINING LABELS only, like the centralised critic; never at
    deployment: the checkpoint is evaluated by MARL_e3_delivery_eval_v6.py like any actor);
  * the behaviour policy acts with the teacher's action with probability beta (decaying linearly from --beta0 to 0 over the
    first half of training), else with the student's greedy action;
  * the student minimises the cross-entropy to the teacher's action on every visited state, over an aggregated buffer of
    the last --buffer iterations (DAgger).
Checkpoint selection on SELECT (401-408) with the greedy student under its own delivery, as every E3 trainer.  The
checkpoint has the trainers' format (actor, config, schema), so evaluation needs no special path.
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
from models.marl_comm_actor import CommAdapter, ActorNet
from models.marl_comm_actor_set import SetActorNet
import models.marl_comm_actor_variants as VAR
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios, TRAIN, SELECT
import scripts.MARL_e3_actor_train_delivery_v7 as DV

SOURCES = ['scripts/MARL_e3_actor_distill_v3.py', 'scripts/MARL_e3_actor_distill_v2.py', 'scripts/MARL_e3_actor_distill.py', 'models/marl_comm_actor_variants.py', 'scripts/MARL_e3_actor_train_delivery_v7.py', 'models/marl_comm_actor.py', 'models/marl_comm_actor_set.py',
           'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']


def load_actor(path):
    ck = torch.load(path, weights_only=False); cfg = ck['config']
    return ck, (SetActorNet if cfg.get('set_actor') or cfg.get('arch') == 'set' else ActorNet)


VIEW = {'teacher': 'counterfactual_full', 'student': 'actual'}


def episode(sc, seed, load, adapter, t_adapter, student, teacher, mask, beta, rng, collect):
    """One episode under the student's delivery; returns (queue sum, [(X_student, teacher action)])."""
    env, topo, down, onward = sc.env(seed, load); m = env.n_agents; data = []; q = 0.0
    for t in range(N_DEC):
        with no_oracle_access(env):
            DV.deliver(env, seed, load, t)
        Xt = None
        if collect and VIEW['teacher'] == 'counterfactual_full':
            cf = [env.counterfactual_view(i, [j for j in range(m) if j != i]) for i in range(m)]      # TRAINING label only
            Xt = np.stack([t_adapter.encode(v, 'actual') for v in cf])
        with no_oracle_access(env):
            views = env.transmit()
            Xs = np.stack([adapter.encode(views[i], VIEW['student']) for i in range(m)])
            if collect and VIEW['teacher'] == 'own':
                Xt = np.stack([t_adapter.encode(views[i], 'actual') for i in range(m)])
            with torch.no_grad():
                a_s = student(torch.as_tensor(Xs), mask).argmax(-1).numpy()
                a_t = teacher(torch.as_tensor(Xt), mask).argmax(-1).numpy() if collect else None
            use_t = collect and rng.random() < beta
            acts = {i: int((a_t if use_t else a_s)[i]) for i in range(m)}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
        if collect:
            data.append((Xs, a_t))
    return q, data


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    DV.DELIVERY['mode'] = a.student_delivery; DV.DELIVERY['capacity'] = 'iid'
    VIEW['teacher'] = a.teacher_view; VIEW['student'] = a.student_view
    sc = Scenarios(out); env0, topo0, _, _ = sc.env(*TRAIN[0])
    SA = {'default': CommAdapter, 'freshonly': VAR.FreshOnlyCommAdapter}[a.student_adapter]
    adapter = SA(topo0, N_DEC, env0.action_interval); t_adapter = CommAdapter(topo0, N_DEC, env0.action_interval)
    tck, TNet = load_actor(a.teacher)
    if tck['schema'] != adapter.schema():
        raise SystemExit('teacher schema differs')
    teacher = TNet(adapter.dim, tck['config']['hidden']); teacher.load_state_dict(tck['actor']); teacher.eval()
    student = (SetActorNet if a.arch == 'set' else ActorNet)(adapter.dim, a.hidden)
    mask = torch.as_tensor(adapter.valid_mask()); opt = torch.optim.Adam(student.parameters(), lr=a.lr)
    cfg = dict(vars(a), set_actor=(a.arch == 'set'), algo='DAgger distillation from a privileged full-delivery teacher',
               teacher_config=tck['config'], n_dec=N_DEC, train_eps=len(TRAIN), select_eps=len(SELECT), adapter=a.student_adapter,
               privileged=('teacher labels from env.counterfactual_view (training only)' if a.teacher_view == 'counterfactual_full' else 'teacher acts on the delivered view (no privileged view)'))
    (out / 'config.json').write_text(json.dumps(cfg, indent=1, default=str)); (out / 'schema.json').write_text(json.dumps(adapter.schema(), indent=1))
    log = open(out / 'log.jsonl', 'a'); buf = []; best = np.inf; t0 = time.perf_counter(); lossf = nn.CrossEntropyLoss()
    for it in range(1, a.iters + 1):
        beta = max(0.0, a.beta0 * (1.0 - it / (0.5 * a.iters)))
        batch = []
        for k in rng.choice(len(TRAIN), a.eps_per_iter, replace=False):
            _, d = episode(sc, *TRAIN[k], adapter, t_adapter, student, teacher, mask, beta, rng, True); batch += d
        buf.append(batch); buf = buf[-a.buffer:]
        X = torch.as_tensor(np.concatenate([np.stack([x for x, _ in b]) for b in buf]))               # (N, m, dim)
        Y = torch.as_tensor(np.concatenate([np.stack([y for _, y in b]) for b in buf]), dtype=torch.long)
        Xf, Yf = X.reshape(-1, X.shape[-1]), Y.reshape(-1); Mf = mask.repeat(X.shape[0], 1)
        idx = np.arange(len(Yf)); losses = []
        for _ in range(a.epochs):
            rng.shuffle(idx)
            for mb in np.array_split(idx, max(1, len(idx) // a.minibatch)):
                mb = torch.as_tensor(mb); loss = lossf(student(Xf[mb], Mf[mb]), Yf[mb])
                opt.zero_grad(); loss.backward(); nn.utils.clip_grad_norm_(student.parameters(), 1.0); opt.step(); losses.append(loss.item())
        with torch.no_grad():
            agree = float((student(Xf, Mf).argmax(-1) == Yf).float().mean())
        rec = dict(it=it, beta=beta, loss=float(np.mean(losses)), agree=agree, n=int(len(Yf)), seconds=time.perf_counter() - t0)
        if it % a.eval_every == 0 or it == a.iters:
            sel = float(np.mean([episode(sc, s, h, adapter, t_adapter, student, teacher, mask, 0.0, rng, False)[0] for s, h in SELECT]))
            rec['select_queue_sum'] = sel
            ck = dict(actor=student.state_dict(), it=it, select=sel, config=cfg, schema=adapter.schema())
            torch.save(ck, out / 'ckpt_last.pt')
            if sel < best:
                best = sel; torch.save(ck, out / 'ckpt_best.pt'); rec['best'] = True
        log.write(json.dumps(rec) + '\n'); log.flush()
        print(f'[{rec["seconds"]:.0f}s] it {it}: beta {beta:.2f} loss {rec["loss"]:.3f} agree {agree:.3f}' + (f' | select {rec["select_queue_sum"]:.0f}' if 'select_queue_sum' in rec else ''), flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_hashes=h0, best_select=best, seconds=time.perf_counter() - t0), indent=1))
    print('COMPLETE', out, 'best select', best, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--teacher', required=True); p.add_argument('--student-delivery', choices=['none', 'prefix', 'rxq', 'nbr'], required=True)
    p.add_argument('--out', required=True); p.add_argument('--seed', type=int, default=0); p.add_argument('--arch', choices=['set', 'flat'], default='set')
    p.add_argument('--iters', type=int, default=500); p.add_argument('--eps-per-iter', type=int, default=8); p.add_argument('--buffer', type=int, default=40)
    p.add_argument('--epochs', type=int, default=2); p.add_argument('--minibatch', type=int, default=256); p.add_argument('--lr', type=float, default=1e-3)
    p.add_argument('--beta0', type=float, default=1.0); p.add_argument('--hidden', type=int, default=128); p.add_argument('--eval-every', type=int, default=20)
    p.add_argument('--threads', type=int, default=2)
    p.add_argument('--student-adapter', choices=['default', 'freshonly'], default='default')
    p.add_argument('--teacher-view', choices=['counterfactual_full', 'own'], default='counterfactual_full')
    p.add_argument('--student-view', choices=['actual', 'none'], default='actual')
    main(p.parse_args())
