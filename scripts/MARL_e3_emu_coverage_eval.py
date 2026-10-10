#!/usr/bin/env python3
"""E12-b / E12-c (research/marl_budget/PROTOCOL_E3_E12_E14_G3_G6_20261004.md §E12; written 04/10/2026 wake 2): when is the zero-byte
emulator EMU_OLD exact?  The E7 mixed fleet with the OLD group on U2/EMU_OLD — MARL_e3_mixed_fleet_eval_v2.mixed's arm, mirrored step
for step (same delivery, emulator, actions) — plus a lockstep K1 reference environment (the EXACT_PROTO_OLD construction) used for
CHECKS ONLY: OLD actions are always computed on the emulated view, so the trajectory is E7's.
Per OLD agent-step:
  coverage C(i,t)  every key (j, m*_ij(t)) of the public legacy mirror is usable by i (received directly, or relayed at age < 14 steps);
  missing classes  never (no copy of that measurement received) / ambiguous (received only at age >= 14 steps);
  view equality    full signature (sender, measurement time, age, payload) and actor-visible (sender, age, payload) vs the K1 view;
  input / action   the OLD actor's input and greedy action on the EMU view vs on the K1 view.
Run under scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8.
SELF-CHECKS (no manifest otherwise): first episode, layout ALL = the homogeneous packet-only run (MARL_e3_emulator_rules_eval
EXACT_PACKET), as in E7; physical identity of the two environments every step; source hashes unchanged."""
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
import models.marl_delivery_music as MUSIC
import models.marl_relay_v2 as RV2
import scripts.MARL_e3_continuation_labels as CLAB
import scripts.MARL_e3_fallback_eval_v2 as FB2
import scripts.MARL_e3_p2_nesting_replay as NR
import scripts.MARL_e3_mixed_fleet_eval as MF1
import scripts.MARL_e3_mixed_fleet_eval_v2 as MF2
import scripts.MARL_e3_emulator_rules_eval as ERE
import scripts.MARL_e3_legacy_decoder_eval as LD

SOURCES = ['scripts/MARL_e3_emu_coverage_eval.py'] + MF2.SOURCES + ['scripts/MARL_e3_legacy_decoder_eval.py']
CELLS = ('cov_eq', 'cov_neq', 'unc_eq', 'unc_neq')


def actor_sig(ents):
    return sorted((e.sender, round(float(e.age), 6), e.payload) for e in ents)


def grid_nbrs(i, m):
    n = int(round(m ** 0.5)); r, c = divmod(i, n)
    return [rr * n + cc for rr, cc in ((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)) if 0 <= rr < n and 0 <= cc < n]


def episode(sc, seed, load, ck_old, ck_new, book, lay):
    env, pol_old = FB2.relay_env(sc, seed, load, ck_old, book, 0); m = env.n_agents; iv = env.action_interval
    pol_new = CLAB.Policy(ck_new, {i: env.public_topology(i) for i in range(m)}, iv)
    O = MF2.layout(env, lay); Os = set(O); deliv = NR.NestedDelivery(); ex = MF2.ExactVO(m, iv, O, 'older', True)
    envk, _ = FB2.relay_env(sc, seed, load, ck_old, book, 1); dk = MusicDelivery('agefirst'); dk.mode = 'prefix'; prevk = None
    nnew = {i: sum(j not in Os for j in grid_nbrs(i, m)) for i in O}
    C = dict(agent_steps=0, keys=0, missing=0, never=0, ambiguous=0, actor_neq=0, input_neq=0, action_neq=0, action_neq_cov=0, action_neq_unc=0,
             **{c: 0 for c in CELLS})
    fail_t = [0] * N_DEC; by_nn = {}; first = None
    prev = None; q = 0.0; qa = np.zeros(m); t0 = time.perf_counter()
    for t in range(N_DEC):
        with no_oracle_access(env):
            deliv(env, seed, load, t); views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = RV2.merge_views(views, prev, t, iv, 'age'); now = float(env._now())
        ex.observe(views, prev); ov = ex.views(mv, t, now); tab = ex.legacy.mirror.table
        with no_oracle_access(envk):
            dk(envk, seed, load, t); vk = envk.transmit(); envk.verify_mirror()
            bad = envk.check_access_invariants(vk)
            if bad:
                raise AssertionError(f'access invariant (reference): {bad[:3]}')
            mvk = RV2.merge_views(vk, prevk, t, iv, 'age'); prevk = mvk
        for i in range(m):
            if not np.array_equal(np.asarray(views[i].lane_vehicles), np.asarray(vk[i].lane_vehicles)):
                raise AssertionError(f'reference environment diverged physically at t={t}')
        prev = mv
        a_old = FB2.act_relay(pol_old, ov); a_new = FB2.act_relay(pol_new, mv); a_ref = FB2.act_relay(pol_old, mvk)
        for i in O:
            keys = [(j, float(tab[i, j])) for j in range(m) if j != i and tab[i, j] > MUSIC.NEVER / 2]
            miss = [k for k in keys if not ex.usable(i, k)]; nev = sum(k not in ex.seen[i] for k in miss)
            cov = not miss; eq = LD.sig_entries(ov[i].inbox) == LD.sig_entries(mvk[i].inbox)
            C['agent_steps'] += 1; C['keys'] += len(keys); C['missing'] += len(miss); C['never'] += nev; C['ambiguous'] += len(miss) - nev
            C[('cov_' if cov else 'unc_') + ('eq' if eq else 'neq')] += 1
            C['actor_neq'] += actor_sig(ov[i].inbox) != actor_sig(mvk[i].inbox)
            C['input_neq'] += not np.array_equal(pol_old.adapter.encode(ov[i], 'actual'), pol_old.adapter.encode(mvk[i], 'actual'))
            an = int(a_old[i]) != int(a_ref[i]); C['action_neq'] += an; C['action_neq_cov' if cov else 'action_neq_unc'] += an
            b = by_nn.setdefault(str(nnew[i]), [0, 0]); b[0] += 1
            if not cov:
                fail_t[t] += 1; b[1] += 1
            if cov != eq and first is None:
                first = dict(t=t, agent=i, cov=cov, eq=eq, miss=[list(k) for k in miss[:3]])
        acts = {i: int(a_old[i]) if i in Os else int(a_new[i]) for i in range(m)}
        with no_oracle_access(env):
            _, _, rec = env.step(acts); per = MF1.agent_q(env)
        with no_oracle_access(envk):
            _, _, reck = envk.step(acts)
        if reck['queue'] != rec['queue']:
            raise AssertionError(f'reference environment queue diverged at t={t}')
        q += float(rec['queue']); qa += np.asarray(per)
    return dict(queue_sum=q, q_agents=qa.tolist(), seconds=time.perf_counter() - t0, old=sorted(O), counts=C, fail_by_t=fail_t,
                by_new_nbrs=by_nn, first_exception=first, emu_cnt=dict(ex.cnt))


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1); FB2.KEY_SLOTS['n'] = 8
    if RV2.merge_views.__qualname__.split('.')[0] != 'make_slot_merge':
        raise SystemExit('run under scripts/MARL_grid_relay_wrapper.py --relay-slots nearest8')
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}; sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    book = json.loads((ROOT / a.codebook).read_text()); sc = Scenarios(out); t0 = time.perf_counter()
    ck_old = torch.load(a.old, weights_only=False); ck_new = torch.load(a.new, weights_only=False); rows = []; ids = {}
    for s in a.traffic_seeds:
        for h in a.headways:
            ep = f'seed{s}_load{h:g}'
            if not rows:
                r = episode(sc, s, h, ck_old, ck_new, book, 'ALL')
                ids['emu_all'] = (r['queue_sum'], ERE.episode(sc, s, h, ck_old, book, 'U2', 'EXACT_PACKET')[0]['queue_sum'])
                ids['emu_all_counts'] = r['counts']
                if abs(ids['emu_all'][0] - ids['emu_all'][1]) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: layout ALL emulator run {ids}')
            for lay in a.layouts:
                rows.append(dict(arm='U2/EMU_OLD', layout=lay, episode=ep, **episode(sc, s, h, ck_old, ck_new, book, lay)))
        last = [r for r in rows if r['episode'] == f'seed{s}_load{a.headways[-1]:g}']
        print(f'[{time.perf_counter() - t0:.0f}s] seed {s}: ' + ', '.join(f"{r['layout']} q {r['queue_sum']:.0f} " + ' '.join(f'{c} {r["counts"][c]}' for c in CELLS) +
              f" amb {r['counts']['ambiguous']} act {r['counts']['action_neq']}" for r in last), flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    tot = {c: sum(r['counts'][c] for r in rows) for c in rows[0]['counts']}
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', identities=ids, totals=tot, args=vars(a), old_sha256=sha(a.old),
                                                       new_sha256=sha(a.new), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, json.dumps(tot), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--old', required=True); p.add_argument('--new', required=True)
    p.add_argument('--layouts', nargs='+', default=['D', 'C']); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
