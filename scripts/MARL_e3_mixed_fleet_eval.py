#!/usr/bin/env python3
"""Mixed-version fleet evaluator (03/10/2026 20:2x EDT; PROTOCOL_E3_MIXED_FLEET_20261003.md).
OLD agents run the legacy receiver (CK1), NEW agents the upgraded-channel receiver (Cage); arms (channel / what OLD agents do):
U1/PLAIN, U2/PLAIN, U2/EMU_OLD (P2's near-exact legacy-view emulator at OLD agents only), U1/FB_OLD (FB_S+ fallback to Z at OLD
agents only, detector frozen in P1), K1/ROLLBACK (whole network on const1).  --refs: ZTEAM (all Z, delivery none), ALLOLD (all CK1
on K1), ALLNEW (all Cage on U1).  Code paths are imported: MARL_e3_fallback_eval_v2 (relay_env, act_relay, act_z, z_policy,
view_stats), MARL_e3_p2_nesting_replay (NestedDelivery, Exact), MARL_e3_repair_panel_eval (gate_of, run_arm for the identities).
Per-agent queue = waiting on that agent's incoming lanes after each step (measurement only, never an input); rows keep the
16 per-agent episode sums so any group's local gain can be computed.
SELF-CHECKS (no manifest otherwise): on the first episode, OLD = all with U1/PLAIN equals homogeneous CK1 PLAIN, OLD = none
equals homogeneous Cage PLAIN, OLD = all with U2/EMU_OLD equals P2's U2/EXACT total; per-agent queues sum to the step queue;
access invariants and the oracle guard every step; source hashes unchanged."""
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
from models.marl_delivery_music import MusicDelivery
from models.marl_relay_v3 import grid_coords
import models.marl_relay_v2 as RV2
import scripts.MARL_e3_continuation_labels as CLAB
import scripts.MARL_e3_actor_train_delivery_v7 as DV
import scripts.MARL_e3_fallback_eval_v2 as FB2
import scripts.MARL_e3_p2_nesting_replay as NR
import scripts.MARL_e3_repair_panel_eval as RP

SOURCES = ['scripts/MARL_e3_mixed_fleet_eval.py', 'scripts/MARL_e3_fallback_eval_v2.py', 'scripts/MARL_e3_p2_nesting_replay.py',
           'scripts/MARL_e3_repair_panel_eval.py', 'models/marl_delivery_music.py', 'models/marl_relay_v2.py', 'models/marl_relay_v3.py',
           'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py']
ARMS = ['U1/PLAIN', 'U2/PLAIN', 'U2/EMU_OLD', 'U1/FB_OLD', 'K1/ROLLBACK']


def layout(env, name):
    rc = grid_coords(env.agent_ids)
    if name == 'D':
        return frozenset(i for i, (r, c) in enumerate(rc) if (r + c) % 2 == 0)
    if name == 'C':
        return frozenset(i for i, (r, c) in enumerate(rc) if c in (1, 2))
    if name == 'ALL':
        return frozenset(range(len(rc)))
    if name == 'NONE':
        return frozenset()
    raise ValueError(name)


def agent_q(env):
    return [sum(env._lane_wait.get(l, 0.0) for lanes in env._lanes[i] for l in lanes) for i in range(env.n_agents)]


def mixed(sc, seed, load, ck_old, ck_new, ckz, book, arm, lay, gate=None):
    chan, what = arm.split('/')
    env, pol_old = FB2.relay_env(sc, seed, load, ck_old, book, 1 if chan == 'K1' else 0); m = env.n_agents; iv = env.action_interval
    pol_new = CLAB.Policy(ck_new, {i: env.public_topology(i) for i in range(m)}, iv)          # same quantised adapter as pol_old
    zp = FB2.z_policy(ckz, env) if what == 'FB_OLD' else None
    O = layout(env, lay); deliv = NR.NestedDelivery() if chan == 'U2' else MusicDelivery('agefirst')
    if chan != 'U2':
        deliv.mode = 'prefix'
    ex = NR.Exact(m, iv) if what == 'EMU_OLD' else None; prev = None; q = 0.0; qa = np.zeros(m); st = dict(delivered=0, flags=0, buffer=0)
    t0 = time.perf_counter()
    for t in range(N_DEC):
        with no_oracle_access(env):
            sets = deliv(env, seed, load, t); st['delivered'] += sum(len(x) for x in sets)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = RV2.merge_views(views, prev, t, iv, 'age'); now = float(env._now())
            if ex is not None:
                ex.observe(views, prev); ov = ex.views(mv, t, now)
            else:
                ov = mv
            prev = mv
            a_old = FB2.act_relay(pol_old, ov); a_new = FB2.act_relay(pol_new, mv)
            if zp is not None:
                az = FB2.act_z(zp, mv); fl = {i: bool(gate(FB2.view_stats(mv[i], t, iv, m - 1)[0])) for i in O}; st['flags'] += sum(fl.values())
            acts = {}
            for i in range(m):
                if i in O:
                    acts[i] = int(az[i]) if (zp is not None and fl[i]) else int(a_old[i])
                else:
                    acts[i] = int(a_new[i])
            _, _, rec = env.step(acts)
            per = agent_q(env)
            if abs(sum(per) - float(rec['queue'])) > 1e-6:
                raise AssertionError('per-agent queues do not sum to the step queue')
        q += float(rec['queue']); qa += np.asarray(per)
    if ex is not None:
        st['buffer'] = sum(len(b) for b in ex.seen)
    return dict(queue_sum=q, q_agents=qa.tolist(), seconds=time.perf_counter() - t0, old=sorted(O), **st)


def zteam(sc, seed, load, ckz):
    """FB2.run_z with per-agent queues."""
    CLAB.ActorNet = FB2.SetActorNet; CLAB.CommAdapter = FB2.CommAdapter
    env, pol = FB2.make(sc, seed, load, ckz, 'iid'); DV.DELIVERY['mode'] = 'none'; q = 0.0; qa = np.zeros(env.n_agents)
    for t in range(N_DEC):
        with no_oracle_access(env):
            DV.deliver(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            _, _, rec = env.step(pol.act(views))
            per = agent_q(env)
            if abs(sum(per) - float(rec['queue'])) > 1e-6:
                raise AssertionError('per-agent queues do not sum to the step queue')
        q += float(rec['queue']); qa += np.asarray(per)
    return dict(queue_sum=q, q_agents=qa.tolist())


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1); FB2.KEY_SLOTS['n'] = 8
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}; sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    book = json.loads((ROOT / a.codebook).read_text()); sc = Scenarios(out); t0 = time.perf_counter()
    ck_old = torch.load(a.old, weights_only=False); ck_new = torch.load(a.new, weights_only=False); ckz = torch.load(a.z, weights_only=False)
    gate = None
    if not a.refs and 'U1/FB_OLD' in a.arms:
        det = json.loads(Path(a.detectors).read_text())
        if det['relay_sha256'] != sha(a.old):
            raise SystemExit('detectors belong to another checkpoint')
        gate = RP.gate_of(det['detectors']['FB_S+'])
    rows = []; ids = {}
    for s in a.traffic_seeds:
        for h in a.headways:
            ep = f'seed{s}_load{h:g}'
            if not rows:                                                   # first-episode identities
                z0 = FB2.run_z(sc, s, h, ckz); zt = zteam(sc, s, h, ckz)['queue_sum']
                ids['zteam'] = (zt, z0)
                ids['old_all'] = (mixed(sc, s, h, ck_old, ck_new, ckz, book, 'U1/PLAIN', 'ALL')['queue_sum'], RP.run_arm(sc, s, h, ck_old, ckz, book, 0, 'PLAIN')['queue_sum'])
                ids['old_none'] = (mixed(sc, s, h, ck_old, ck_new, ckz, book, 'U1/PLAIN', 'NONE')['queue_sum'], RP.run_arm(sc, s, h, ck_new, ckz, book, 0, 'PLAIN')['queue_sum'])
                ids['emu_all'] = (mixed(sc, s, h, ck_old, ck_new, ckz, book, 'U2/EMU_OLD', 'ALL')['queue_sum'], NR.episode(sc, s, h, ck_old, book, 'U2', 'EXACT')[0])
                bad = {k: v for k, v in ids.items() if abs(v[0] - v[1]) > 1e-6}
                if bad:
                    raise SystemExit(f'SELF-CHECK FAIL: first-episode identities {bad}')
            if a.refs:
                todo = [('ZTEAM', None), ('ALLOLD', ('K1/PLAIN', 'ALL')), ('ALLNEW', ('U1/PLAIN', 'NONE'))]
            else:
                todo = [(arm, (arm, a.layout)) for arm in a.arms]
            for name, spec in todo:
                r = zteam(sc, s, h, ckz) if spec is None else mixed(sc, s, h, ck_old, ck_new, ckz, book, spec[0], spec[1], gate)
                rows.append(dict(arm=name, layout=None if a.refs else a.layout, episode=ep, **r))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {s}: ' + ', '.join(f"{r['arm']} {r['queue_sum']:.0f}" for r in rows if r['episode'] == f'seed{s}_load{a.headways[-1]:g}'), flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', identities=ids, args=vars(a), old_sha256=sha(a.old),
                                                       new_sha256=sha(a.new), z_sha256=sha(a.z), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--old', required=True); p.add_argument('--new', required=True); p.add_argument('--z', required=True); p.add_argument('--detectors')
    p.add_argument('--layout', choices=['D', 'C'], default='D'); p.add_argument('--arms', nargs='+', default=ARMS); p.add_argument('--refs', action='store_true')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
