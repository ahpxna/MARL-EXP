#!/usr/bin/env python3
"""PER-NODE legacy decoder with WIRE-FORMAT base packets (04/10/2026 00:4x EDT; review HISTORY_FRAMING_REVIEW_20261004 items 1-4).
Successor of scripts/MARL_e3_legacy_decoder_eval.py (running, not edited).  That decoder keeps every agent's state in one object
and passes base-packet relay tables as Python objects with full-precision measurement times.  Here:
  * every agent is a separate Node: its own copy of the public legacy (K1) schedule, its own cache, its own legacy table.
    A node's update receives ONLY (its physical view on U2, the base packets addressed to it that were physically delivered);
    the bundle is built by a Channel object that serialises the sender's table, so no node object is ever passed to another;
  * the base packet's relay table is serialised in a declared wire format, slot-positional over the sender's 8 nearest slots:
        full  : (payload, measurement time)  — the simulator's semantics (reference for the old decoder);
        wire4 : (payload, age in decision steps saturated at 14) — the deployed 25 B layout (17 + 8 x 21 = 185 bits);
        wire5 : (payload, age in decision steps saturated at 31) — 17 + 8 x 22 = 193 bits <= 200, the SAME 25 B packet;
    the receiver reconstructs the measurement time as (send time - age x interval);
  * NEGATIVE CONTROLS --controls (each a broken decoder with the right packet sizes and schedule):
        ages    : every entry of every base table is one step older than the truth;
        empty   : base tables carry nothing (the packet-only decoder of E6, zero extra bytes);
        u2table : senders put their UPGRADED (U2) merged view in the table — i.e. NEW senders keep no legacy state;
        stale   : the decoded fresh entry is taken one step old (a stale base packet) — must be detected wherever decoded.
    Diagnostic relay_needed (reference only): entries of the K1 merged view that come from a relay table and are strictly
    fresher than the receiver's own cache — the only places where a table can matter.
Cross-checks at every step and agent: against the lockstep K1 reference (packets / cache / view / input / action, as in the
old decoder; in wire modes the view is compared on (sender, age, payload), the actor-visible content, and timestamp
differences are counted separately as 'ts'), and against the old single-object decoder run alongside ('old_dec': view
signature equality).  Every node's schedule replica must agree (asserted).
SELF-CHECKS (no manifest otherwise): first episode, layout ALL, full format: queue == homogeneous K1 PLAIN; source hashes."""
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
from models.marl_delivery_music import MusicDelivery
import models.marl_relay_v2 as RV2
import models.marl_relay_v3 as RV3
import scripts.MARL_e3_continuation_labels as CLAB
import scripts.MARL_e3_fallback_eval_v2 as FB2
import scripts.MARL_e3_p2_nesting_replay as NR
import scripts.MARL_e3_repair_panel_eval as RP
import scripts.MARL_e3_mixed_fleet_eval as MF1
import scripts.MARL_e3_legacy_decoder_eval as LD
from envs.external.cityflow_budgeted import CacheEntry

SOURCES = ['scripts/MARL_e3_legacy_decoder_nodes_eval.py'] + LD.SOURCES
PARTS = ('packets', 'cache', 'view', 'input', 'action', 'ts', 'old_dec')
CONTROLS = ('ages', 'empty', 'u2table', 'stale')
CAPS = {'full': None, 'wire4': 14, 'wire5': 31}
BITS = {'full': None, 'wire4': 17 + 8 * 21, 'wire5': 17 + 8 * 22}


def actor_sig(ents):
    return sorted((e.sender, round(float(e.age), 6), e.payload) for e in ents)


class Node:
    """Agent k's local legacy state only."""

    def __init__(self, k, m, slots, iv):
        self.k = k; self.slots = slots; self.iv = float(iv); self.sched = NR.Legacy(m)
        self.cache = {}; self.table = {}                                       # sender -> (payload, measured_at, step) / CacheEntry

    def schedule(self, now):
        _, sets = self.sched.step(now)
        return sets                                                            # public: every replica is identical (asserted)

    def base_packet(self, now, fmt, corrupt, u2view):
        """The relay part of k's base packet, slot-positional over slots[k]; a tuple of plain values (no object shared)."""
        out = []; table = {e.sender: e for e in u2view.inbox} if corrupt == 'u2table' else self.table
        for j in sorted(self.slots[self.k]):
            e = table.get(j)
            if corrupt == 'empty':
                e = None
            if e is None:
                out.append(None); continue
            if fmt == 'full':
                out.append((e.payload, int(e.measured_at)))
            else:
                out.append((e.payload, min(CAPS[fmt], int(round((now - float(e.measured_at)) / self.iv)))))
        if corrupt == 'ages':
            out = [None if x is None else (x[0], x[1] + 1 if fmt != 'full' else x[1] - int(self.iv)) for x in out]
        return tuple(out)

    def update(self, t, now, phys, sched_i, bundle, fmt, corrupt):
        """phys: this node's own physical view on U2 (own sensors + the packets physically delivered to it);
        bundle: {sender: (fresh payload entry from the real packet, decoded base table)} for the base packets it received."""
        dec = {j: bundle[j][0] for j in sorted(bundle)}
        if corrupt == 'stale':
            dec = {j: replace(e, measured_at=int(e.measured_at) - int(self.iv)) for j, e in dec.items()}
        inbox = tuple(CacheEntry(j, e.payload, e.measured_at, now - float(e.measured_at), int(t)) for j, e in dec.items())
        cache = tuple(CacheEntry(j, p, ms, now - float(ms), ds) for j, (p, ms, ds) in sorted(self.cache.items()) if j not in dec)
        mine = replace(phys, inbox=inbox, cache=cache,
                       never_heard=tuple(j for j in phys.neighbours if j not in dec and j not in self.cache))
        prev = {}
        for j, (_, tab) in bundle.items():
            ents = []
            for s, x in zip(sorted(self.slots[j]), tab):
                if x is None:
                    continue
                p, v = x; ms = v if fmt == 'full' else int(round(now - v * self.iv))
                ents.append(CacheEntry(s, p, ms, now - float(ms), int(t)))
            prev[j] = replace(phys, inbox=tuple(ents), cache=())
        mv = RV2.merge_views({self.k: mine}, prev if t > 0 else None, t, self.iv, 'age')[self.k]
        for j, e in dec.items():
            self.cache[j] = (e.payload, e.measured_at, int(t))
        self.table = {e.sender: e for e in mv.inbox}
        return mine, mv


def episode(sc, seed, load, ck_old, ck_new, book, lay, fmt, corrupt, slots):
    env, pol_old = FB2.relay_env(sc, seed, load, ck_old, book, 0); m = env.n_agents; iv = env.action_interval
    pol_new = CLAB.Policy(ck_new, {i: env.public_topology(i) for i in range(m)}, iv)
    envk, _ = FB2.relay_env(sc, seed, load, ck_old, book, 1); dk = MusicDelivery('agefirst'); dk.mode = 'prefix'; prevk = None
    O = MF1.layout(env, lay); nodes = [Node(k, m, slots, iv) for k in range(m)]; old = LD.LegacyDecoder(m); prev = None
    deliv = NR.NestedDelivery(); q = 0.0; qa = np.zeros(m); missing = 0
    st = dict(base_delivered=0, base_unique=0, base_bits=BITS[fmt], relay_needed=0)
    mis = {p: 0 for p in PARTS}; first = None; t0 = time.perf_counter()
    for t in range(N_DEC):
        with no_oracle_access(env):
            deliv(env, seed, load, t); views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = RV2.merge_views(views, prev, t, iv, 'age'); now = float(env._now())
        S = [n.schedule(now) for n in nodes]
        if any(S[k] != S[0] for k in range(m)):
            raise AssertionError('schedule replicas disagree')
        S = S[0]; senders = set().union(*S)
        pk = {j: nodes[j].base_packet(now, fmt, corrupt, mv[j]) for j in sorted(senders)}  # broadcast once per scheduled sender
        lmv = {}; lv = {}
        for i in range(m):
            have = {e.sender: e for e in views[i].inbox}                       # physically delivered to i on U2
            bundle = {}
            for j in sorted(S[i]):
                if j in have:
                    bundle[j] = (have[j], pk[j])
                else:
                    missing += 1
            lv[i], lmv[i] = nodes[i].update(t, now, views[i], S[i], bundle, fmt, corrupt)
        st['base_delivered'] += sum(len(s) for s in S); st['base_unique'] += len(senders)
        osets, olv, odec = old.step(views, t, now); omv = old.finish(olv, odec, t, iv)
        with no_oracle_access(envk):
            sk = dk(envk, seed, load, t); vk = envk.transmit(); envk.verify_mirror()
            mvk = RV2.merge_views(vk, prevk, t, iv, 'age'); prevk = mvk
        for i in range(m):
            if not np.array_equal(np.asarray(views[i].lane_vehicles), np.asarray(vk[i].lane_vehicles)):
                raise AssertionError(f'reference environment diverged physically at t={t}')
        a_dec = FB2.act_relay(pol_old, lmv); a_ref = FB2.act_relay(pol_old, mvk); a_new = FB2.act_relay(pol_new, mv)
        Xd = np.stack([pol_old.adapter.encode(lmv[i], 'actual') for i in range(m)]); Xr = np.stack([pol_old.adapter.encode(mvk[i], 'actual') for i in range(m)])
        for i in range(m):
            for e in mvk[i].inbox:
                c = envk._cache[i].get(e.sender)
                if e.sender not in sk[i] and (c is None or float(e.measured_at) > float(c[1])):
                    st['relay_needed'] += 1
            ref_cache = {j: (float(ms), p) for j, (p, ms, ds) in envk._cache[i].items()}
            my_cache = {j: (float(ms), p) for j, (p, ms, ds) in nodes[i].cache.items()}
            checks = dict(packets=(sorted(S[i]) == sorted(sk[i]) and LD.sig_entries(lv[i].inbox) == LD.sig_entries(vk[i].inbox)),
                          cache=my_cache == ref_cache, view=actor_sig(lmv[i].inbox) == actor_sig(mvk[i].inbox),
                          input=np.array_equal(Xd[i], Xr[i]), action=int(a_dec[i]) == int(a_ref[i]),
                          ts=LD.sig_entries(lmv[i].inbox) == LD.sig_entries(mvk[i].inbox),
                          old_dec=LD.sig_entries(lmv[i].inbox) == LD.sig_entries(omv[i].inbox))
            for p_, ok in checks.items():
                if not ok:
                    mis[p_] += 1
                    if first is None and p_ != 'old_dec' and p_ != 'ts':
                        first = dict(t=t, agent=i, part=p_)
        acts = {i: int(a_dec[i]) if i in O else int(a_new[i]) for i in range(m)}
        prev = mv
        with no_oracle_access(env):
            _, _, rec = env.step(acts); per = MF1.agent_q(env)
        with no_oracle_access(envk):
            _, _, reck = envk.step(acts)
        if reck['queue'] != rec['queue']:
            raise AssertionError(f'reference environment queue diverged at t={t}')
        q += float(rec['queue']); qa += np.asarray(per)
    return dict(queue_sum=q, q_agents=qa.tolist(), seconds=time.perf_counter() - t0, old=sorted(O), mismatches=mis, first_mismatch=first,
                legacy_missing=missing, decisions=N_DEC * m, **st)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}; sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    if RV2.merge_views.__qualname__.split('.')[0] != 'make_slot_merge':
        raise SystemExit('run under scripts/MARL_grid_relay_wrapper.py --relay-slots nearest8')
    slots = RV3.nearest_slots(4, 4, 8)
    book = json.loads((ROOT / a.codebook).read_text()); sc = Scenarios(out); t0 = time.perf_counter()
    ck_old = torch.load(a.old, weights_only=False); ck_new = torch.load(a.new, weights_only=False); ckz = torch.load(a.z, weights_only=False)
    rows = []; ids = {}
    for s in a.traffic_seeds:
        for h in a.headways:
            ep = f'seed{s}_load{h:g}'
            if not rows:
                ids['all_full_eq_K1'] = (episode(sc, s, h, ck_old, ck_new, book, 'ALL', 'full', None, slots)['queue_sum'],
                                         RP.run_arm(sc, s, h, ck_old, ckz, book, 1, 'PLAIN')['queue_sum'])
                if abs(ids['all_full_eq_K1'][0] - ids['all_full_eq_K1'][1]) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: layout ALL node decoder {ids}')
            for fmt in a.formats:
                for corrupt in [None] + (a.controls if fmt == a.formats[0] else []):
                    for lay in a.layouts:
                        r = episode(sc, s, h, ck_old, ck_new, book, lay, fmt, corrupt, slots)
                        rows.append(dict(arm=f'U2/NODE_DEC_OLD/{fmt}' + (f'/CTRL_{corrupt}' if corrupt else ''), fmt=fmt, corrupt=corrupt, layout=lay, episode=ep, **r))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {s}: ' + ', '.join(f"{r['arm'].split('/', 2)[2]} {r['layout']} {r['queue_sum']:.0f} "
              f"mism {dict((k, v) for k, v in r['mismatches'].items() if v)} miss {r['legacy_missing']} relay_needed {r['relay_needed']}"
              for r in rows if r['episode'] == f'seed{s}_load{a.headways[-1]:g}'), flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    tot = {f"{r_['arm']}": {p: sum(r['mismatches'][p] for r in rows if r['arm'] == r_['arm']) for p in PARTS} for r_ in rows}
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', identities=ids, mismatches_total=tot,
                                                       legacy_missing_total=sum(r['legacy_missing'] for r in rows), args=vars(a), old_sha256=sha(a.old),
                                                       new_sha256=sha(a.new), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, json.dumps(tot), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--old', required=True); p.add_argument('--new', required=True); p.add_argument('--z', required=True)
    p.add_argument('--layouts', nargs='+', default=['ALL', 'D', 'C']); p.add_argument('--formats', nargs='+', default=['full', 'wire4', 'wire5'])
    p.add_argument('--controls', nargs='*', default=[], choices=CONTROLS, help='negative controls, run with the first format only')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
