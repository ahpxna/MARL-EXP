#!/usr/bin/env python3
"""DISTRIBUTED legacy decoder (04/10/2026 00:1x EDT; external audit WAVE1_AND_COMPATIBILITY_PROTOCOL; closes the E9 gap).
Protocol on the order-preserving upgraded channel (U2, NestedDelivery): every scheduled packet is sent as before; the senders that
the LEGACY (K1) schedule would broadcast at this step additionally send a BASE packet = their fresh summary (the same payload the
real packet carries) + their own LEGACY relay table (their legacy merged view of the previous step, slot-restricted, 4-bit ages).
Every agent k (OLD and NEW: every sender must be able to send its legacy table) keeps only LOCAL legacy state:
  cache_k : the last base packet decoded directly from each sender (payload, measured time, step);
  view_k  : its legacy merged view of the previous step (what it puts in its own base packets).
At step t agent i decodes the base packets of S_i^legacy(t) — the public legacy schedule (age-first over the legacy broadcast
history, a function of time; scripts/MARL_e3_p2_nesting_replay.Legacy) — which must be physically delivered to it on U2 (checked:
S_i^legacy(t) is a subset of its delivered set; a miss is counted, never filled from the simulator), and rebuilds its legacy merged
view with the UNCHANGED merge rule (models.marl_relay_v2.merge_views, slot-restricted under the grid wrapper) from its own cache
and the tables carried by the decoded base packets.  Nothing else is read.  OLD agents act on that view; NEW agents act on the U2
merged view.
REFERENCE CHECK (always on): a K1 environment stepped in lockstep with the same joint actions provides the legacy truth; at every
step and for every agent the decoder is compared with it on
  packets (decoded sender set and payloads), cache (sender -> measured time, payload), view (sender, measured time, age, payload),
  input (encoded actor input of the OLD receiver), action (OLD receiver's action on decoder view vs on reference view);
mismatch counts and the first mismatch are recorded; --strict stops at the first mismatch.  Physical identity of the two
environments is asserted every step.
Costs: base packets delivered = sum over ALL agents of |S_i^legacy(t)| x 25 B; unique base broadcasts = |union S^legacy(t)| x 25 B;
legacy state entries = sum over agents of cache + view entries (max over the episode).
SELF-CHECKS (no manifest otherwise): first episode, layout ALL: queue == homogeneous K1 PLAIN (scripts/MARL_e3_repair_panel_eval.run_arm);
source hashes unchanged."""
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
import scripts.MARL_e3_continuation_labels as CLAB
import scripts.MARL_e3_fallback_eval_v2 as FB2
import scripts.MARL_e3_p2_nesting_replay as NR
import scripts.MARL_e3_repair_panel_eval as RP
import scripts.MARL_e3_mixed_fleet_eval as MF1
from envs.external.cityflow_budgeted import CacheEntry

SOURCES = ['scripts/MARL_e3_legacy_decoder_eval.py', 'scripts/MARL_e3_p2_nesting_replay.py', 'scripts/MARL_e3_mixed_fleet_eval.py',
           'scripts/MARL_e3_fallback_eval_v2.py', 'scripts/MARL_e3_repair_panel_eval.py', 'models/marl_delivery_music.py', 'models/marl_relay_v2.py',
           'models/marl_relay_v3.py', 'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py',
           'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py', 'scripts/MARL_grid_relay_wrapper.py']
PKT = 25
PARTS = ('packets', 'cache', 'view', 'input', 'action')


def sig_entries(ents):
    return sorted((e.sender, float(e.measured_at), round(float(e.age), 6), e.payload) for e in ents)


class LegacyDecoder:
    """Local legacy state of every agent (one object for convenience; agent i only ever touches cache[i], view[i])."""

    def __init__(self, m):
        self.m = m; self.cache = [dict() for _ in range(m)]; self.view = None; self.legacy = NR.Legacy(m); self.missing = 0

    def step(self, views, t, now):
        _, sets = self.legacy.step(now); lv = {}; decoded = []
        for i in range(self.m):
            have = {e.sender: e for e in views[i].inbox}                       # what agent i physically received this step
            dec = {}
            for j in sorted(sets[i]):
                if j in have:
                    dec[j] = have[j]
                else:
                    self.missing += 1                                           # never filled from the simulator
            inbox = tuple(CacheEntry(j, e.payload, e.measured_at, now - float(e.measured_at), int(t)) for j, e in sorted(dec.items()))
            cache = tuple(CacheEntry(j, p, ms, now - float(ms), ds) for j, (p, ms, ds) in sorted(self.cache[i].items()) if j not in dec)
            lv[i] = replace(views[i], inbox=inbox, cache=cache)
            decoded.append(dec)
        return sets, lv, decoded

    def finish(self, lv, decoded, t, iv):
        mv = RV2.merge_views(lv, self.view, t, iv, 'age')                     # each i uses its cache + the decoded senders' tables
        for i in range(self.m):
            for j, e in decoded[i].items():
                self.cache[i][j] = (e.payload, e.measured_at, int(t))
        self.view = mv
        return mv


def episode(sc, seed, load, ck_old, ck_new, book, lay, strict, channel='U2'):
    env, pol_old = FB2.relay_env(sc, seed, load, ck_old, book, 0); m = env.n_agents; iv = env.action_interval
    pol_new = CLAB.Policy(ck_new, {i: env.public_topology(i) for i in range(m)}, iv)
    envk, _ = FB2.relay_env(sc, seed, load, ck_old, book, 1); dk = MusicDelivery('agefirst'); dk.mode = 'prefix'; prevk = None
    O = MF1.layout(env, lay); dec = LegacyDecoder(m); prev = None
    deliv = NR.NestedDelivery() if channel == 'U2' else MusicDelivery('agefirst')   # U1 = NEGATIVE CONTROL (not nested)
    if channel != 'U2':
        deliv.mode = 'prefix'
    q = 0.0; qa = np.zeros(m); st = dict(delivered=0, unique=0, base_delivered=0, base_unique=0, legacy_entries=0)
    mis = {p: 0 for p in PARTS}; first = None; t0 = time.perf_counter()
    for t in range(N_DEC):
        with no_oracle_access(env):
            sets = deliv(env, seed, load, t); st['delivered'] += sum(len(x) for x in sets); st['unique'] += len(set().union(*sets))
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = RV2.merge_views(views, prev, t, iv, 'age'); now = float(env._now())
        lsets, lv, decoded = dec.step(views, t, now); lmv = dec.finish(lv, decoded, t, iv)
        st['base_delivered'] += sum(len(s) for s in lsets); st['base_unique'] += len(set().union(*lsets))
        st['legacy_entries'] = max(st['legacy_entries'], sum(len(dec.cache[i]) + len(lmv[i].inbox) for i in range(m)))
        with no_oracle_access(envk):                                           # reference truth (checks only)
            sk = dk(envk, seed, load, t); vk = envk.transmit(); envk.verify_mirror()
            mvk = RV2.merge_views(vk, prevk, t, iv, 'age'); prevk = mvk
        for i in range(m):
            if not np.array_equal(np.asarray(views[i].lane_vehicles), np.asarray(vk[i].lane_vehicles)):
                raise AssertionError(f'reference environment diverged physically at t={t}')
        a_old_dec = FB2.act_relay(pol_old, lmv); a_old_ref = FB2.act_relay(pol_old, mvk); a_new = FB2.act_relay(pol_new, mv)
        Xd = np.stack([pol_old.adapter.encode(lmv[i], 'actual') for i in range(m)]); Xr = np.stack([pol_old.adapter.encode(mvk[i], 'actual') for i in range(m)])
        for i in range(m):
            ref_cache = {j: (float(ms), p) for j, (p, ms, ds) in envk._cache[i].items()}
            my_cache = {j: (float(ms), p) for j, (p, ms, ds) in dec.cache[i].items()}
            checks = dict(packets=(sorted(lsets[i]) == sorted(sk[i]) and sig_entries(lv[i].inbox) == sig_entries(vk[i].inbox)),
                          cache=my_cache == ref_cache, view=sig_entries(lmv[i].inbox) == sig_entries(mvk[i].inbox),
                          input=np.array_equal(Xd[i], Xr[i]), action=int(a_old_dec[i]) == int(a_old_ref[i]))
            for p_, ok in checks.items():
                if not ok:
                    mis[p_] += 1
                    if first is None:
                        first = dict(t=t, agent=i, part=p_)
                    if strict:
                        raise SystemExit(f'DECODER MISMATCH t={t} agent {i} part {p_}')
        acts = {i: int(a_old_dec[i]) if i in O else int(a_new[i]) for i in range(m)}
        prev = mv
        with no_oracle_access(env):
            _, _, rec = env.step(acts); per = MF1.agent_q(env)
        with no_oracle_access(envk):
            _, _, reck = envk.step(acts)
        if reck['queue'] != rec['queue']:
            raise AssertionError(f'reference environment queue diverged at t={t}')
        q += float(rec['queue']); qa += np.asarray(per)
    return dict(queue_sum=q, q_agents=qa.tolist(), seconds=time.perf_counter() - t0, old=sorted(O), mismatches=mis, first_mismatch=first,
                legacy_missing=dec.missing, decisions=N_DEC * m, **st)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}; sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    book = json.loads((ROOT / a.codebook).read_text()); sc = Scenarios(out); t0 = time.perf_counter()
    ck_old = torch.load(a.old, weights_only=False); ck_new = torch.load(a.new, weights_only=False); ckz = torch.load(a.z, weights_only=False)
    rows = []; ids = {}
    for s in a.traffic_seeds:
        for h in a.headways:
            ep = f'seed{s}_load{h:g}'
            if not rows:
                ids['all_eq_K1'] = (episode(sc, s, h, ck_old, ck_new, book, 'ALL', a.strict)['queue_sum'], RP.run_arm(sc, s, h, ck_old, ckz, book, 1, 'PLAIN')['queue_sum'])
                if abs(ids['all_eq_K1'][0] - ids['all_eq_K1'][1]) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: layout ALL decoder {ids}')
            for lay in a.layouts:
                r = episode(sc, s, h, ck_old, ck_new, book, lay, a.strict, a.channel)
                rows.append(dict(arm=f'{a.channel}/EXACT_DEC_OLD', layout=lay, episode=ep, **r))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {s}: ' + ', '.join(f"{r['layout']} {r['queue_sum']:.0f} mism {sum(r['mismatches'].values())} miss {r['legacy_missing']}"
                                                                     for r in rows if r['episode'] == f'seed{s}_load{a.headways[-1]:g}'), flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    tot = {p: sum(r['mismatches'][p] for r in rows) for p in PARTS}
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', identities=ids, mismatches_total=tot,
                                                       legacy_missing_total=sum(r['legacy_missing'] for r in rows), args=vars(a), old_sha256=sha(a.old),
                                                       new_sha256=sha(a.new), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, 'mismatches', tot, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--old', required=True); p.add_argument('--new', required=True); p.add_argument('--z', required=True)
    p.add_argument('--layouts', nargs='+', default=['ALL', 'D', 'C']); p.add_argument('--strict', action='store_true')
    p.add_argument('--channel', choices=['U2', 'U1'], default='U2', help='U1 = negative control: the base packets are not nested there')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
