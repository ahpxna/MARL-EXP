#!/usr/bin/env python3
"""RELAY eval SATROT (30/09 14:1x EDT; ledger L-173): the parallel session's relay eval v3 (cap-correct orders prefix / agefirst /
bass from models/marl_delivery_music.py, AgeMirror self-check) with the relay merge of models/marl_relay_v2.py (the 25 B
layout of L-165: 4-bit ages saturated at 14 decision steps).  Measurement times are unchanged by the v2 merge, so the
AgeMirror check is the same.  Everything else is relay eval v3.
Relay eval v3 docstring follows.
RELAY eval v3 (30/09 13:3x EDT; ledger L-168): the relay eval plus --order {prefix, agefirst, bass}
(models/marl_delivery_music.py), with the cap<c> delivery rule applied under EVERY order (relay eval v2 replaces deliver() by
deliver_agefirst, which ignores cap<c>).  --order prefix reproduces the relay eval exactly.  SELF-CHECK at every relay step:
the scheduler-side AgeMirror equals the measurement times of the merged views (so the bass rule uses scheduler records only).
Relay eval docstring follows.
RELAY eval (30/09 11:0x; ledger L-162): v8 plus --relay {none, age, fresh}.  The packet channel of PROTOCOL_HETERO_v0 is
unchanged (K_i packets of 25 B, the prefix stream, the same byte accounting).  Each packet carries 3 B summaries of its
sender and of every agent the sender knew (models/marl_relay.py); use with --quant 4 so every summary is 3 B.  The receiver
merges its decoded packets' relays with its own cache (freshest copy per agent).  Relays are MULTI-HOP: a sender forwards what
it learned from relays too.  The access audit runs on the env's own views before the merge.
v8 docstring follows.
v8 (30/09 09:2x; ledger L-155): v7 plus --loss p: every packet decoded this step is lost independently with
probability p (models/marl_comm_actor_lossy.py; deterministic in receiver, step, sender), a robustness diagnostic.
--loss 0 is exactly v7.
v7 docstring follows.
v7 (29/09 22:4x): v6 plus --quant L --codebook JSON: SENDER-side payload compression (models/marl_comm_actor_quant.py,
codebook fitted on TRAIN traffic by scripts/MARL_e3_payload_codebook.py) wrapped around the adapter; a diagnostic for
direction 2 (ledger L-128).  Rows keep the PROTOCOL's accounted bytes (25 B packets); the compressed byte cost is the
stream's packet count times the codebook's bytes_per_packet, computed in the report.
--byte-capacity bpp turns the packet capacities K_i into a BYTE budget 25 K_i spent on bpp-byte packets (the direction-2
protocol variant; declared as a diagnostic, not PROTOCOL_HETERO_v0).
v6 docstring follows.
v6 (29/09 22:0x): v5 plus the root-cause variants (config keys arch, adapter) and the delivery rules of
MARL_e3_actor_train_delivery_v7.py.
v5 docstring follows.
v5 (29/09 19:5x): v4 plus --capacity (the capacity process of every episode, as the closed-loop scripts) and the
delivery rules of MARL_e3_actor_train_delivery_v6.py.
v4 docstring follows.
v4 (29/09 19:1x): v3 plus set-structured actors (config flag set_actor): the continuation-labels Policy is built
with models.marl_comm_actor_set.SetActorNet for those checkpoints; delivery rules of MARL_e3_actor_train_delivery_v5.py.
v3 docstring follows.
v3 (29/09 18:4x): v2 plus the masked adapter for actors trained with --mask-nonneighbors (config flag), and the
delivery rules of MARL_e3_actor_train_delivery_v4.py.
v2 docstring follows.
v2 (29/09 18:1x): v1 with the delivery rules of MARL_e3_actor_train_delivery_v3.py (adds nbr and cap<c>).
v1 docstring follows.
Evaluate E3 actors under several DELIVERY rules on the closed-loop panel (29/09; the information ceiling).

For every actor checkpoint in --actors (tag=path) and every rule in --deliveries (MARL_e3_actor_train_delivery.deliver:
prefix / full / none / random), the greedy actor is run on the panel (901-916 x 8/16 by default, the env's i.i.d.
capacity trace, the same scenario factory as the closed-loop scripts).  Recorded per episode: sum of queues (the
closed-loop metric), accounted bytes.  Self-check: an actor under 'prefix' must reproduce its saved closed-loop prefix
row (queue_sum and bytes) when --parity tag=rows.json is given.  Report: per actor x rule the mean waiting, and paired
per-episode differences against a named reference system (--reference tag:rule).
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_zero_loss_truncation import make
import scripts.MARL_e3_actor_train_delivery_v7 as DV
import models.marl_comm_actor_variants as VAR
from models.marl_comm_actor import CommAdapter
import scripts.MARL_e3_continuation_labels as CLAB
from models.marl_comm_actor import ActorNet
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_masked import MaskedCommAdapter
from models.marl_comm_actor_quant import quantized
from models.marl_comm_actor_lossy import lossy
from models.marl_relay import merge_views
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery, NEVER

SOURCES = ['scripts/MARL_e3_delivery_eval_relay_satrot.py', 'models/marl_relay_v2.py', 'scripts/MARL_e3_delivery_eval_relay_v3.py', 'models/marl_delivery_music.py', 'scripts/MARL_e3_delivery_eval_relay.py', 'models/marl_relay.py', 'scripts/MARL_e3_delivery_eval_v8.py', 'models/marl_comm_actor_lossy.py', 'scripts/MARL_e3_delivery_eval_v7.py', 'models/marl_comm_actor_quant.py', 'scripts/MARL_e3_delivery_eval_v6.py', 'models/marl_comm_actor_variants.py', 'scripts/MARL_e3_actor_train_delivery_v7.py', 'scripts/MARL_e3_delivery_eval_v5.py', 'scripts/MARL_e3_actor_train_delivery_v6.py', 'scripts/MARL_e3_delivery_eval_v4.py', 'models/marl_comm_actor_set.py', 'scripts/MARL_e3_actor_train_delivery_v5.py', 'scripts/MARL_e3_delivery_eval_v3.py', 'scripts/MARL_e3_delivery_eval_v2.py', 'scripts/MARL_e3_actor_train_delivery_v4.py', 'models/marl_comm_actor_masked.py', 'scripts/MARL_e3_zero_loss_truncation.py',
           'models/marl_comm_actor.py', 'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py']


CAPACITY = {'kind': 'iid'}
MUS = MusicDelivery('prefix')
CHECKS = {'mirror_steps': 0}


def run(sc, seed, load, ck, rule):
    cfg = ck['config']; arch = 'set' if cfg.get('set_actor') else cfg.get('arch', 'flat')
    CLAB.ActorNet = {'flat': ActorNet, 'set': SetActorNet, 'sharedconcat': VAR.SharedConcatActorNet, 'attn': VAR.AttnActorNet}[arch]
    CLAB.CommAdapter = {'default': CommAdapter, 'noise': VAR.NoiseCommAdapter, 'freshonly': VAR.FreshOnlyCommAdapter}[CAPACITY.get('adapter_override') or cfg.get('adapter', 'default')]
    if CAPACITY.get('quant'):
        CLAB.CommAdapter = quantized(CLAB.CommAdapter, CAPACITY['book'], CAPACITY['quant'])
    if CAPACITY.get('loss'):
        CLAB.CommAdapter = lossy(CLAB.CommAdapter, CAPACITY['loss'])
    env, pol = make(sc, seed, load, ck, CAPACITY['kind']); DV.DELIVERY['mode'] = rule; q = 0.0; b = 0
    if CAPACITY.get('byte_capacity'):
        # BYTES-limited variant: a receiver that could decode K raw 25 B packets decodes floor(25 K / bpp) compressed ones
        env._trace = np.minimum(env.n_agents - 1, (25 * np.asarray(env._trace)) // int(CAPACITY['byte_capacity']))
    if ck['config'].get('mask_nonneighbors'):
        pol.adapter = MaskedCommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    prev = None
    for t in range(N_DEC):
        with no_oracle_access(env):
            MUS.mode = rule; MUS(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            if CAPACITY.get('relay', 'none') != 'none':
                mv = merge_views_v2(views, prev, t, env.action_interval, CAPACITY['relay']); prev = mv
                for i in range(env.n_agents):
                    got = {e.sender: float(e.measured_at) for e in mv[i].inbox}
                    for j in range(env.n_agents):
                        tm = float(MUS.mirror.table[i, j])
                        if (j in got) != (tm > NEVER / 2) or (j in got and abs(got[j] - tm) > 1e-6):
                            raise AssertionError(f'AgeMirror != merged view: t {t} receiver {i} agent {j}: {got.get(j)} vs {tm}')
                CHECKS['mirror_steps'] += 1
                acts = pol.act(mv)
            else:
                acts = pol.act(views)
            _, _, rec = env.step(acts)
        q += float(rec['queue']); b += int(rec['accounted_bytes'])
    return q, b


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    actors = dict(x.split('=', 1) for x in a.actors); parity = {}
    for x in a.parity:
        tag, f = x.split('=', 1); parity[tag] = {r['episode']: r for r in json.loads(Path(f).read_text()) if r['method'] == 'prefix'}
    sc = Scenarios(out); rows = []; t0 = time.perf_counter()
    for tag, path in actors.items():
        ck = torch.load(Path(path), weights_only=False)
        for rule in a.deliveries:
            for seed in a.traffic_seeds:
                for load in a.headways:
                    ep = f'seed{seed}_load{load:g}'; q, b = run(sc, seed, load, ck, rule)
                    if rule == 'prefix' and tag in parity and ep in parity[tag]:
                        pr = parity[tag][ep]
                        if abs(pr['queue_sum'] - q) > 1e-6 or pr['bytes'] != b:
                            raise SystemExit(f'SELF-CHECK FAIL: {tag} {ep}: {q}/{b} != saved prefix row {pr["queue_sum"]}/{pr["bytes"]}')
                    rows.append(dict(actor=tag, rule=rule, episode=ep, queue_sum=q, bytes=b))
            mq = np.mean([r['queue_sum'] for r in rows if r['actor'] == tag and r['rule'] == rule])
            print(f'[{time.perf_counter() - t0:.0f}s] {tag} {rule}: mean waiting {mq:.1f}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', mirror_checked_steps=CHECKS['mirror_steps'], args=vars(a), source_hashes=h0,
                                                       seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actors', nargs='+', required=True, help='tag=ckpt path'); p.add_argument('--deliveries', nargs='+', default=['prefix', 'full', 'none', 'random'])
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 917))); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--parity', nargs='*', default=[], help='tag=closed-loop rows.json'); p.add_argument('--out', required=True)
    p.add_argument('--capacity', choices=['iid', 'fixed', 'high', 'low', 'bursty'], default='iid')
    p.add_argument('--adapter-override', choices=['default', 'noise', 'freshonly'], default=None,
                   help='DIAGNOSTIC: evaluate with this input variant instead of the one the actor was trained with')
    p.add_argument('--quant', type=int, default=0, help='DIAGNOSTIC: sender-side payload quantisation levels (0 = raw)')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--relay', choices=['none', 'age', 'fresh'], default='none', help='relay-compressed packets inside the packet channel')
    p.add_argument('--order', choices=['prefix', 'agefirst', 'bass'], default='prefix', help='broadcast order (models/marl_delivery_music.py)')
    p.add_argument('--loss', type=float, default=0.0, help='DIAGNOSTIC: per-packet loss probability of this step\'s deliveries')
    p.add_argument('--byte-capacity', type=int, default=0, help='DIAGNOSTIC: bytes per compressed packet; capacities become floor(25 K / bpp), capped at m-1 (0 = off)')
    a = p.parse_args(); CAPACITY['kind'] = a.capacity; CAPACITY['adapter_override'] = a.adapter_override
    CAPACITY['quant'] = a.quant
    CAPACITY['byte_capacity'] = a.byte_capacity
    CAPACITY['loss'] = a.loss
    CAPACITY['relay'] = a.relay
    MUS.order = a.order
    if a.relay == 'fresh' and a.order == 'bass':
        raise SystemExit('bass needs --relay age (the mirror replays measurement times)')
    if a.quant:
        CAPACITY['book'] = json.loads(Path(a.codebook).read_text()); SOURCES.append(a.codebook)
    main(a)
