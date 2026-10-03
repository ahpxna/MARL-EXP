#!/usr/bin/env python3
"""v2 (02/10/2026 13:0x; PROTOCOL_E3_G4_TIME_PROJECTION_20261002.md): v1 plus --project timecov --table T.json: the actor
reads its view with the DECISION-STEP feature replaced by the latest step s <= t at which the training channel's support table
(scripts/MARL_e3_coverage_time_table.py, development episodes) shows the view's present count c (the earliest such step if
none is <= t): the minimal move of the (coverage, time) pair into the training support.  The view itself is unchanged.  With
a pair already in support the projection is the identity.  v1 docstring follows.
SUPPORT-PROJECTION closed-loop evaluator (02/10/2026 12:4x EDT; PROTOCOL_E3_SUPPORT_PROJECTION_20261002.md):
MARL_e3_ageremap_eval.py plus --project onefresh: of the entries DELIVERED DIRECTLY this step (the raw transmit inbox), only
the one whose sender comes first in the committed public order (the prefix head, the single fresh packet of a K = 1
channel) keeps its age 0; every other direct entry is shown one decision step old (the minimal move that puts the view's
fresh count inside a K = 1 receiver's training support).  Relayed entries, content and the protocol state are unchanged.
At K = 1 there is exactly one direct entry, so the projection is the identity (self-check by parity).  Legal: the committed
order is the public stream order.  Original docstring follows.
AGE-REMAP closed-loop evaluator (02/10/2026 12:0x EDT; PROTOCOL_E3_AGE_REMAP_20261002.md): MARL_e3_ageclip_eval.py plus
--remap TRAIN (1, 2, 3 = const K, 0 = iid; none = off): every present entry of the merged view the ACTOR reads gets its age
label drawn from the exact monotone transport coupling between the DEPLOYMENT channel's age histogram (that of --K) and the
TRAINING channel's (TRAIN), from the channel-only g3_nopolicy composition; u from a hash of (traffic seed, headway, step,
receiver, sender).  Content and the protocol state are unchanged.  With TRAIN = the deployment channel the map is the
identity (self-check by parity).  Deployable: the receiver's own ages plus two histograms known before deployment.
--A (clip) as before; --A and --remap are exclusive.  Original docstring follows.
AGE-CLIP closed-loop evaluator (01/10/2026 12:1x EDT; PROTOCOL_E3_AGECLIP_PROSPECTIVE_20261001.md).

relay6Cage_st_s<s> closed loop under age-first, capacity const K (K = 0: the iid process of make(..., 'iid')), relay v2 merge,
3 B codebook (the code path of MARL_e3_negflip_probe.py / MARL_e3_protocol_demand_probe.py).  With --A a >= 0 the ACTOR
reads the merged view with every entry older than a decision steps re-labelled to age a (content unchanged); the protocol
state (what is relayed next step) is the unmodified merged view.  --A -1 = no clipping (the plain relay system).
Deployable: the rule uses only the receiver's own merged view (ages it already holds); no oracle call.
SELF-CHECK: --parity rows.json (episode -> queue_sum) must be reproduced exactly where given.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from dataclasses import replace
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_zero_loss_truncation import make
import scripts.MARL_e3_continuation_labels as CLAB
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery

SOURCES = ['scripts/MARL_e3_projection_eval_v2.py', 'scripts/MARL_e3_projection_eval.py', 'scripts/MARL_e3_ageremap_eval.py', 'research/marl_budget/e3_channel_composition_20261001/g3_nopolicy/composition.json', 'models/marl_relay_v2.py', 'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py',
           'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py',
           'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']


def clipped(v, interval, A):
    """(view the actor reads, number of entries re-labelled)."""
    if A < 0:
        return v, 0
    old = [float(e.age) / float(interval) > A + 1e-9 for e in v.inbox]
    if not any(old):
        return v, 0
    return replace(v, inbox=tuple(replace(e, age=A * float(interval)) if o else e for e, o in zip(v.inbox, old))), sum(old)


COMP = ROOT / 'research/marl_budget/e3_channel_composition_20261001/g3_nopolicy/composition.json'


def hist(K):
    h = json.loads(COMP.read_text())[str(K)]['age_hist']
    h = np.asarray(json.loads(h) if isinstance(h, str) else h, float)[:15]
    return h / h.sum()


class Remap:
    """Exact monotone coupling deployment histogram p -> training histogram q on the ages 0..14."""
    def __init__(self, K_deploy, K_train):
        self.p = hist(K_deploy); self.Fp = np.cumsum(self.p); self.Fq = np.cumsum(hist(K_train)); self.n = 0

    def label(self, a, key):
        a = int(min(14, max(0, a)))
        if self.p[a] <= 0:                                     # an age the channel histogram never shows: left unchanged
            return a
        h = (int.from_bytes(hashlib.blake2b(repr(key).encode(), digest_size=8).digest(), 'big') + 1) / 2.0 ** 64   # (0, 1]
        u = (self.Fp[a - 1] if a > 0 else 0.0) + self.p[a] * h
        return int(np.argmax(self.Fq >= min(u, 1.0) - 1e-12))

    def view(self, v, interval, key):
        new = []
        for e in v.inbox:
            a = int(round(float(e.age) / float(interval))); b = self.label(a, key + (int(e.sender),))
            if b != a:
                self.n += 1
            new.append(replace(e, age=b * float(interval)) if b != a else e)
        return replace(v, inbox=tuple(new))


def onefresh(mv, raw, order, i, interval):
    """(projected view, number of direct entries shown one step old)."""
    direct = {e.sender for e in raw.inbox}
    if len(direct) <= 1:
        return mv, 0
    head = next(j for j in order if j != i and j in direct)
    new = tuple(replace(e, age=float(interval)) if (e.sender in direct and e.sender != head) else e for e in mv.inbox)
    return replace(mv, inbox=new), len(direct) - 1


TABLE = {}


def timecov(mv, t):
    """(view with the projected decision step, 1 if moved)."""
    c = len(mv.inbox); steps = TABLE.get(c)
    if not steps:
        return mv, 0
    le = [s for s in steps if s <= t]; s2 = max(le) if le else min(steps)
    return (mv, 0) if s2 == t else (replace(mv, decision_step=int(s2)), 1)


def run(sc, seed, load, ck, book, K, A, remap=None, project='none'):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, ck, 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; n_clip = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            if project == 'timecov':
                pv = [timecov(mv[i], t) for i in range(m)]
                rv = [p[0] for p in pv]; n_clip += sum(p[1] for p in pv)
            elif project == 'onefresh':
                pv = [onefresh(mv[i], views[i], mus.last_order, i, env.action_interval) for i in range(m)]
                rv = [p[0] for p in pv]; n_clip += sum(p[1] for p in pv)
            elif remap is not None:
                rv = [remap.view(mv[i], env.action_interval, (int(seed), float(load), int(t), int(i))) for i in range(m)]
            else:
                cv = [clipped(mv[i], env.action_interval, A) for i in range(m)]
                rv = [c[0] for c in cv]; n_clip += sum(c[1] for c in cv)
            X = np.stack([pol.adapter.encode(rv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                acts = {i: int(a) for i, a in enumerate(pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
    return q, (remap.n if remap is not None and project == 'none' else n_clip)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    if a.project == 'timecov' and a.table not in SOURCES:
        SOURCES.append(a.table)                                   # the table's hash is recorded and checked like a source
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text()); ck = torch.load(Path(a.relay), weights_only=False)
    ck_sha = hashlib.sha256(Path(a.relay).read_bytes()).hexdigest()
    par = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text())} if a.parity else {}
    sc = Scenarios(out); rows = []; t0 = time.perf_counter()
    if a.project == 'timecov':
        TABLE.update({int(c): v for c, v in json.loads(Path(a.table).read_text()).items()})
    if sum([a.remap != 'none', a.A >= 0, a.project != 'none']) > 1:
        raise SystemExit('--A, --remap and --project are exclusive')
    rule = f'project{a.project}' if a.project != 'none' else (f'remap{a.remap}' if a.remap != 'none' else ('prefix' if a.A < 0 else f'clip{a.A:g}'))
    for seed in a.traffic_seeds:
        for load in a.headways:
            rm = Remap(a.K, int(a.remap)) if a.remap != 'none' else None
            ep = f'seed{seed}_load{load:g}'; q, nc = run(sc, seed, load, ck, book, a.K, a.A, rm, a.project)
            if ep in par and abs(par[ep] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != parity row {par[ep]}')
            rows.append(dict(actor=a.tag, rule=rule, episode=ep, queue_sum=q, clipped_views=nc, parity_checked=ep in par))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', K=a.K, A=a.A, remap=a.remap, project=a.project, rule=rule, args=vars(a),
        parity_episodes=sum(r['parity_checked'] for r in rows), checkpoint_sha256=ck_sha, source_hashes=h0,
        seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--tag', required=True)
    p.add_argument('--K', type=int, required=True, help='constant K; 0 = iid'); p.add_argument('--A', type=float, required=True, help='clip age (steps); -1 = off')
    p.add_argument('--remap', choices=['none', '0', '1', '2', '3'], default='none', help='training channel of the age remap (0 = iid)')
    p.add_argument('--project', choices=['none', 'onefresh', 'timecov'], default='none', help='support projection of the actor view')
    p.add_argument('--table', default=None, help='coverage-time support table (timecov)')
    p.add_argument('--parity', default=None); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', required=True); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
