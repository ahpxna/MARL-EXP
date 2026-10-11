#!/usr/bin/env python3
"""E6 / E3 evaluator (03/10/2026 23:2x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003).  Homogeneous CK1 team, one checkpoint per
process; arms CHAN/ARM with CHAN in {K1, U1, U2} and ARM in
  PLAIN; EXACT (ExactV older, all copies = P2's Exact); EXACT_PACKET (older, packet-recoverable copies only);
  EMU_OLDER / EMU_ABSENT / EMU_FRESH (packet-only, missing-entry rule older / absent / fresh).
Z (delivery none) is run on every episode in the same process.  U2 emulator arms are locked to K1/PLAIN when both run
(mismatched steps and queue equality RECORDED, as P2 Amendment 1).  Counters per episode: entries / missing / substituted /
ambiguous / fresh / absent.
SELF-CHECKS (no manifest otherwise): first episode — ExactV(older, all copies) equals P2's Exact on U2 and on U1 (queue,
scripts/MARL_e3_p2_nesting_replay.episode); access invariants / oracle guard every step; source hashes unchanged."""
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
import models.marl_delivery_music as MUSIC
import models.marl_relay_v2 as RV2
import scripts.MARL_e3_fallback_eval_v2 as FB2
import scripts.MARL_e3_p2_nesting_replay as NR
from scripts.MARL_e3_emulator_variants import ExactV

SOURCES = ['scripts/MARL_e3_emulator_rules_eval.py', 'scripts/MARL_e3_emulator_variants.py', 'scripts/MARL_e3_p2_nesting_replay.py',
           'scripts/MARL_e3_fallback_eval_v2.py', 'models/marl_delivery_music.py', 'models/marl_relay_v2.py', 'models/marl_relay_v3.py',
           'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py']
SPEC = {'EXACT': ('older', False), 'EXACT_PACKET': ('older', True), 'EMU_OLDER': ('older', True), 'EMU_ABSENT': ('absent', True), 'EMU_FRESH': ('fresh', True)}


def episode(sc, seed, load, ck, book, chan, kind, lock=None):
    env, pol = FB2.relay_env(sc, seed, load, ck, book, 1 if chan == 'K1' else 0); m = env.n_agents; iv = env.action_interval
    deliv = NR.NestedDelivery() if chan == 'U2' else MUSIC.MusicDelivery('agefirst')
    if chan != 'U2':
        deliv.mode = 'prefix'
    ex = ExactV(m, iv, *SPEC[kind]) if kind != 'PLAIN' else None; prev = None; q = 0.0; recs = []; mism = 0; first = None; t0 = time.perf_counter()
    for t in range(N_DEC):
        with no_oracle_access(env):
            deliv(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = RV2.merge_views(views, prev, t, iv, 'age'); now = float(env._now())
            if ex is not None:
                ex.observe(views, prev); rv = ex.views(mv, t, now)
            else:
                rv = mv
            prev = mv
            X = np.stack([pol.adapter.encode(rv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                acts = pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1)
            if lock is not None:
                ref = next(lock)
                if not (np.array_equal(ref[0], X) and np.array_equal(ref[1], acts)):
                    mism += 1; first = t if first is None else first
            recs.append((X, acts))
            _, _, r = env.step({i: int(a) for i, a in enumerate(acts)})
        q += float(r['queue'])
    out = dict(queue_sum=q, seconds=time.perf_counter() - t0, lock_mismatch_steps=mism if lock is not None else None, first_mismatch=first)
    if ex is not None:
        out.update(ex.cnt); out['buffer'] = sum(len(b) for b in ex.seen)
    return out, recs


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}; sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    book = json.loads((ROOT / a.codebook).read_text()); ck = torch.load(Path(a.relay), weights_only=False); ckz = torch.load(Path(a.z), weights_only=False)
    sc = Scenarios(out); rows = []; t0 = time.perf_counter(); ids = {}
    for s in a.traffic_seeds:
        for h in a.headways:
            ep = f'seed{s}_load{h:g}'
            if not rows:
                for chan in ('U2', 'U1'):
                    ids[chan] = (episode(sc, s, h, ck, book, chan, 'EXACT')[0]['queue_sum'], NR.episode(sc, s, h, ck, book, chan, 'EXACT')[0])
                bad = {k: v for k, v in ids.items() if abs(v[0] - v[1]) > 1e-6}
                if bad:
                    raise SystemExit(f'SELF-CHECK FAIL: ExactV(older, all) != P2 Exact: {bad}')
            rows.append(dict(arm='Z', episode=ep, queue_sum=FB2.run_z(sc, s, h, ckz)))
            ref = None
            for arm in a.arms:
                chan, kind = arm.split('/')
                lock = iter(ref) if (ref is not None and chan == 'U2' and kind != 'PLAIN') else None
                r, recs = episode(sc, s, h, ck, book, chan, kind, lock)
                if arm == 'K1/PLAIN':
                    ref = recs
                rows.append(dict(arm=arm, episode=ep, **r))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {s}: ' + ', '.join(f"{r['arm']} {r['queue_sum']:.0f}" for r in rows if r['episode'] == f'seed{s}_load{a.headways[-1]:g}'), flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', identities=ids, args=vars(a), relay_sha256=sha(a.relay),
                                                       z_sha256=sha(a.z), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--z', required=True)
    p.add_argument('--arms', nargs='+', required=True, help='K1/PLAIN must come first when U2 emulator arms are to be locked')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', required=True); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
