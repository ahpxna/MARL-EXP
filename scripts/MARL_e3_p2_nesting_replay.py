#!/usr/bin/env python3
"""P2 replay check: does an upgrade that NESTS the old channel admit an exact receiver-side emulator? (03/10/2026 18:5x EDT;
external audit Addendum C; scripts/MARL_e3_p2_replay_feasibility.py gave the trace-level answer: K1 view entries recoverable
from what a receiver decodes = 79 % on the iid upgrade (adaptive age-first order), 100 % on an order-preserving upgrade.)

Channels (all with the episode's exogenous capacity trace):
  K1  : constant capacity 1, MusicDelivery 'agefirst' (the CK1 receiver's training channel);
  U1  : the iid upgrade as deployed (MusicDelivery 'agefirst': the order adapts to the larger broadcast sets);
  U2  : an ORDER-PRESERVING iid upgrade (NestedDelivery): the scheduler ranks senders with the K1 rule computed on a legacy
        shadow history (only the K1 broadcast sets update it), and the extra capacity fills the later positions of that order,
        so every receiver decodes a superset of its K1 packets.  Scheduler-side information only.
Receiver-side exact emulator (EXACT, one per receiver, no ACK, no reads of other nodes' state): the K1 schedule is a public
function of time (legacy shadow order + mirror replay, models.marl_delivery_music.AgeMirror, slot mirror under the grid wrapper),
so receiver i knows the measurement time m*(i, j, t) of every entry of its K1 merged view; it shows the copy of j measured at
m* if it has SEEN it — decoded directly or carried in a decoded packet (the sender's previous merged view, slot-restricted) —
with the merged view's age rule.  Missing copies (only on U1): the most recent seen copy measured before m* with its true age,
else absent; counted.  The protocol state (what nodes relay) is the actual channel's, untouched.
REPLAY CHECK (--replay): K1 + PLAIN and U2 + EXACT run in lockstep on the same episode; at every step the K1 packet sets, the
view entries (sender, measured_at, age, payload), the encoded actor inputs and the actions must be identical, and the queue sums
equal.  Fails loudly at the first difference.  Also: NestedDelivery's legacy sets equal MusicDelivery's K1 sets at every step.
--rates: on U1 and U2, per episode, the share of K1 view entries the emulator could not reproduce exactly (closed loop, PLAIN
actions on the actual channel; diagnostic).  Development episodes only (901-904)."""
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
from models.marl_hetero_selector import prefix_sets
from models.marl_relay_v2 import AGE_CAP_STEPS
from models.marl_relay_v3 import nearest_slots
import models.marl_delivery_music as MUSIC
import models.marl_relay_v2 as RV2
import scripts.MARL_e3_fallback_eval_v2 as FB2
from envs.external.cityflow_budgeted import CacheEntry

SOURCES = ['scripts/MARL_e3_p2_nesting_replay.py', 'scripts/MARL_e3_fallback_eval_v2.py', 'models/marl_delivery_music.py',
           'models/marl_relay_v2.py', 'models/marl_relay_v3.py', 'models/marl_comm_actor.py', 'models/marl_comm_actor_quant.py',
           'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']


class Legacy:
    """The public K1 schedule: age-first over the legacy broadcast history (only K1 sets update it) + the mirror replay."""

    def __init__(self, m):
        self.m = m; self.last = {}; self.mirror = MUSIC.AgeMirror(m); self.order = None; self.sets = None

    def step(self, now):
        m = self.m
        self.order = tuple(sorted(range(m), key=lambda j: (0, j) if j not in self.last else (1, self.last[j], j)))
        self.sets = prefix_sets(self.order, [1] * m)
        for j in set().union(*self.sets):
            self.last[j] = now
        self.mirror.update(self.sets, now)
        return self.order, self.sets


class NestedDelivery(MUSIC.MusicDelivery):
    """U2: the legacy (K1) order, with the revealed capacities filling its later positions."""

    def __init__(self):
        super().__init__('agefirst'); self.legacy = None

    def __call__(self, env, seed, load, t):
        m = env.n_agents
        if t == 0 or self.mirror is None:
            self.mirror = MUSIC.AgeMirror(m); self.legacy = Legacy(m)
        now = float(env._now()); order, _ = self.legacy.step(now)
        env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        sets = prefix_sets(order, K)
        env.submit_profile([set(s) for s in sets], R=0)
        self.mirror.update(sets, now); self.last_order = order
        return sets


class Exact:
    """Receiver-side exact emulator of the K1 merged view (one object holds every receiver's OWN buffers; no sharing)."""

    def __init__(self, m, iv):
        self.m = m; self.iv = float(iv); self.legacy = Legacy(m); self.seen = [dict() for _ in range(m)]
        r = int(round(m ** 0.5)); self.slots = nearest_slots(r, r) if r * r == m else None
        self.n = self.miss = self.older = 0

    def observe(self, views, prev_actual):
        for i in range(self.m):
            for e in views[i].inbox:                                   # direct decodes of this step
                self.seen[i][(e.sender, float(e.measured_at))] = e.payload
                if prev_actual is not None:                            # the decoded packet's relay table
                    pk = prev_actual[e.sender]
                    for c in tuple(pk.inbox) + tuple(pk.cache):
                        if c.sender != i and (self.slots is None or c.sender in self.slots[e.sender]):
                            self.seen[i][(c.sender, float(c.measured_at))] = c.payload

    def views(self, mv, t, now):
        self.legacy.step(now); out = {}; tab = self.legacy.mirror.table
        for i in range(self.m):
            ents = []
            for j in range(self.m):
                ms = tab[i, j]
                if j == i or ms <= MUSIC.NEVER / 2:
                    continue
                self.n += 1; p = self.seen[i].get((j, float(ms)))
                if p is None:
                    self.miss += 1
                    olds = [k for k in self.seen[i] if k[0] == j and k[1] < ms]
                    if not olds:
                        continue
                    ms = max(olds)[1]; p = self.seen[i][(j, ms)]; self.older += 1
                age = 0.0 if ms == now else min(AGE_CAP_STEPS, int(round((now - ms) / self.iv))) * self.iv
                ents.append(CacheEntry(j, p, ms, age, int(t)))
            out[i] = replace(mv[i], inbox=tuple(ents), cache=())
        return out


def sig(v):
    return sorted((e.sender, float(e.measured_at), round(float(e.age), 6), e.payload) for e in tuple(v.inbox) + tuple(v.cache))


def episode(sc, seed, load, ck, book, chan, arm, lock=None, strict=True):
    """chan: K1 | U1 | U2; arm: PLAIN | EXACT.  lock: a generator of the K1 PLAIN run's per-step records to compare against."""
    env, pol = FB2.relay_env(sc, seed, load, ck, book, 1 if chan == 'K1' else 0); m = env.n_agents; iv = env.action_interval
    deliv = NestedDelivery() if chan == 'U2' else MUSIC.MusicDelivery('agefirst')
    if chan != 'U2':
        deliv.mode = 'prefix'
    ex = Exact(m, iv) if arm == 'EXACT' else None; prev = None; q = 0.0; recs = []; info = dict(delivered=0, t0=time.perf_counter(), lock_mismatch_steps=0, first_mismatch=None)
    for t in range(N_DEC):
        with no_oracle_access(env):
            sets = deliv(env, seed, load, t); info['delivered'] += sum(len(x) for x in sets)
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
            rec = dict(sets=[sorted(s) for s in (ex.legacy.sets if ex is not None else sets)], sig=[sig(rv[i]) for i in range(m)], X=X, acts=acts)
            if chan == 'U2' and ex is None:
                assert all(set(deliv.legacy.sets[i]) <= set(sets[i]) for i in range(m)), 'U2 does not nest K1'
            if lock is not None and not strict:                        # Amendment 1 (P2): record, do not abort
                ref = next(lock)
                if ref['sets'] != rec['sets'] or ref['sig'] != rec['sig'] or not np.array_equal(ref['X'], rec['X']) or not np.array_equal(ref['acts'], rec['acts']):
                    info['lock_mismatch_steps'] += 1
                    if info['first_mismatch'] is None:
                        info['first_mismatch'] = t
            elif lock is not None:
                ref = next(lock)
                for key in ('sets', 'sig'):
                    if ref[key] != rec[key]:
                        i = next(i for i in range(m) if ref[key][i] != rec[key][i])
                        raise SystemExit(f'REPLAY FAIL t={t} {key} receiver {i}:\n K1  {ref[key][i]}\n EMU {rec[key][i]}')
                if not np.array_equal(ref['X'], rec['X']) or not np.array_equal(ref['acts'], rec['acts']):
                    raise SystemExit(f'REPLAY FAIL t={t}: encoded inputs / actions differ')
            recs.append(rec)
            _, _, r = env.step({i: int(a) for i, a in enumerate(acts)})
        q += float(r['queue'])
    info.update(seconds=time.perf_counter() - info.pop('t0'), buffer=sum(len(b) for b in ex.seen) if ex is not None else 0)
    episode.info = info
    return q, recs, (ex.n, ex.miss, ex.older) if ex is not None else None


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); torch.set_num_threads(1)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    book = json.loads((ROOT / a.codebook).read_text()); ck = torch.load(Path(a.relay), weights_only=False)
    import tempfile; sc = Scenarios(Path(tempfile.mkdtemp(prefix=f'scen_{a.tag}_', dir=out))); res = dict(relay=a.relay, relay_sha256=hashlib.sha256(Path(a.relay).read_bytes()).hexdigest(), episodes={})
    t0 = time.perf_counter()
    for s in a.traffic_seeds:
        for h in a.headways:
            ep = f'seed{s}_load{h:g}'; r = {}
            qk, rk, _ = episode(sc, s, h, ck, book, 'K1', 'PLAIN'); r['K1_PLAIN'] = qk
            if a.replay:
                qe, _, st = episode(sc, s, h, ck, book, 'U2', 'EXACT', lock=iter(rk))
                if abs(qe - qk) > 1e-9:
                    raise SystemExit(f'REPLAY FAIL {ep}: queue {qe} != {qk}')
                r['U2_EXACT'] = qe; r['U2_EXACT_missing'] = st
            if a.rates:
                for chan in ('U1', 'U2'):
                    q, _, _ = episode(sc, s, h, ck, book, chan, 'PLAIN'); r[f'{chan}_PLAIN'] = q
                q, _, st = episode(sc, s, h, ck, book, 'U1', 'EXACT'); r['U1_EXACT'] = q; r['U1_EXACT_entries_missing_older'] = st
            res['episodes'][ep] = r
            print(f'[{time.perf_counter() - t0:.0f}s] {ep}: ' + json.dumps(r), flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    res.update(status='COMPLETE', replay='PASS' if a.replay else None, source_hashes=h0, seconds=time.perf_counter() - t0)
    (out / f'{a.tag}.json').write_text(json.dumps(res, indent=1, default=str)); print('COMPLETE', out / f'{a.tag}.json')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--tag', required=True)
    p.add_argument('--replay', action='store_true'); p.add_argument('--rates', action='store_true')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901]); p.add_argument('--headways', type=float, nargs='+', default=[8.0])
    p.add_argument('--out', default='research/marl_budget/e3_p2_feasibility_20261003')
    main(p.parse_args())
