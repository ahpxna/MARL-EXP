#!/usr/bin/env python3
"""Mixed-version fleet evaluator v2 (03/10/2026 23:3x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003 E7 / E9).  v1
(scripts/MARL_e3_mixed_fleet_eval.py, not edited) plus:
  * EMU_OLD uses the PACKET-ONLY emulator (E6: copies whose measurement time is recoverable from the 25 B packets), with
    entries / missing / substituted / ambiguous counted over OLD receivers only;
  * EXACT_PROTO_OLD (E9): base packets carry the senders' LEGACY (K1) relay state.  Simulated by a lockstep K1 environment
    stepped with the team's actions: its merged views are exactly what base packets would let OLD receivers build.  Physical
    identity of the two environments is asserted every step (queue and every agent's own lane counts).  U2 only (the K1 direct
    packets are nested in U2).  Base-packet bytes are added: unique +25 B per legacy broadcast, delivered +25 B per OLD
    receiver per legacy decode;
  * alternate OLD checkpoints (--alt FT=path --alt PCT=path; arm 'U1/PLAIN@FT');
  * FBR_OLD: the residual-guarded Gaussian gate FB_Mr- (detectors from scripts/MARL_e3_repair_panel_eval_v2.py --calibrate);
  * unique broadcast bytes (|union of decoded sets| x 25 B per step) beside delivered bytes;
  * layout ALL (every agent OLD) for the E9 replay job.
SELF-CHECKS (first episode, else no manifest): OLD = all with U1/PLAIN = homogeneous PLAIN of the OLD checkpoint; OLD = none =
homogeneous NEW PLAIN; OLD = all EMU_OLD = the packet-only emulator's homogeneous run (MARL_e3_emulator_rules_eval); OLD = all
EXACT_PROTO_OLD on U2 = homogeneous K1 PLAIN (exact); ZTEAM = run_z.  Per-agent queues sum to the step queue."""
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
import models.marl_delivery_music as MUSIC
from models.marl_relay_v2 import AGE_CAP_STEPS
import models.marl_relay_v2 as RV2
import scripts.MARL_e3_continuation_labels as CLAB
import scripts.MARL_e3_fallback_eval_v2 as FB2
import scripts.MARL_e3_p2_nesting_replay as NR
import scripts.MARL_e3_repair_panel_eval_v2 as RP2
import scripts.MARL_e3_repair_panel_eval as RP
import scripts.MARL_e3_mixed_fleet_eval as MF1
import scripts.MARL_e3_emulator_rules_eval as ERE
from scripts.MARL_e3_emulator_variants import ExactV
from envs.external.cityflow_budgeted import CacheEntry

SOURCES = ['scripts/MARL_e3_mixed_fleet_eval_v2.py', 'scripts/MARL_e3_mixed_fleet_eval.py', 'scripts/MARL_e3_emulator_variants.py',
           'scripts/MARL_e3_emulator_rules_eval.py', 'scripts/MARL_e3_repair_panel_eval_v2.py', 'scripts/MARL_e3_repair_panel_eval.py',
           'scripts/MARL_e3_fallback_eval_v2.py', 'scripts/MARL_e3_p2_nesting_replay.py', 'models/marl_delivery_music.py', 'models/marl_relay_v2.py',
           'models/marl_relay_v3.py', 'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py',
           'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py', 'scripts/MARL_grid_relay_wrapper.py']
PKT = 25


class ExactVO(ExactV):
    """ExactV with counters restricted to the receivers in `only` (the OLD group).  The views are built by exactly ExactV's rule
    (code mirrored from scripts/MARL_e3_emulator_variants.ExactV.views, which is frozen for wave 1); the first-episode identity
    (OLD = all == the homogeneous packet-only run) checks the mirror."""

    def __init__(self, m, iv, only, rule='older', packet_only=True):
        super().__init__(m, iv, rule, packet_only); self.only = set(only)

    def views(self, mv, t, now):
        self.legacy.step(now); out = {}; tab = self.legacy.mirror.table
        for i in range(self.m):
            ents = []; cur = {e.sender: e for e in mv[i].inbox}; cnt = i in self.only
            for j in range(self.m):
                ms = tab[i, j]
                if j == i or ms <= MUSIC.NEVER / 2:
                    continue
                key = (j, float(ms))
                if cnt:
                    self.cnt['entries'] += 1
                    if key in self.seen[i] and self.minage[i].get(key, 10 ** 9) >= AGE_CAP_STEPS:
                        self.cnt['ambiguous'] += 1
                if self.usable(i, key):
                    p = self.seen[i][key]
                else:
                    if cnt:
                        self.cnt['missing'] += 1
                    if self.rule == 'absent':
                        continue
                    if self.rule == 'fresh':
                        if j in cur:
                            ents.append(cur[j])
                        continue
                    olds = [k for k in self.seen[i] if k[0] == j and k[1] < ms and self.usable(i, k)]
                    if not olds:
                        continue
                    ms = max(olds)[1]; p = self.seen[i][(j, ms)]
                    if cnt:
                        self.cnt['substituted'] += 1
                age = 0.0 if ms == now else min(AGE_CAP_STEPS, int(round((now - ms) / self.iv))) * self.iv
                ents.append(CacheEntry(j, p, ms, age, int(t)))
            out[i] = replace(mv[i], inbox=tuple(ents), cache=())
        return out


def layout(env, name):
    return MF1.layout(env, name)


def mixed(sc, seed, load, cks, ck_new, ckz, book, arm, lay, gates):
    """arm = CHAN/WHAT[@ALT]; cks = {'CK1': ck, 'FT': ck, ...}."""
    base, _, alt = arm.partition('@'); chan, what = base.split('/'); ck_old = cks[alt or 'CK1']
    env, pol_old = FB2.relay_env(sc, seed, load, ck_old, book, 1 if chan == 'K1' else 0); m = env.n_agents; iv = env.action_interval
    pol_new = CLAB.Policy(ck_new, {i: env.public_topology(i) for i in range(m)}, iv)
    O = layout(env, lay); zp = FB2.z_policy(ckz, env) if what in ('FB_OLD', 'FBR_OLD') else None
    gate = gates.get('FB_S+') if what == 'FB_OLD' else (gates.get('FB_Mr-') if what == 'FBR_OLD' else None)
    deliv = NR.NestedDelivery() if chan == 'U2' else MusicDelivery('agefirst')
    if chan != 'U2':
        deliv.mode = 'prefix'
    ex = None; envk = None
    if what == 'EMU_OLD':
        ex = ExactVO(m, iv, O, 'older', True)
    if what == 'EXACT_PROTO_OLD':
        assert chan == 'U2', 'the legacy-state protocol is defined on the order-preserving channel'
        envk, _ = FB2.relay_env(sc, seed, load, ck_old, book, 1); dk = MusicDelivery('agefirst'); dk.mode = 'prefix'; prevk = None
    prev = None; q = 0.0; qa = np.zeros(m); st = dict(delivered=0, unique=0, base_delivered=0, base_unique=0, flags=0, legacy_entries=0)
    t0 = time.perf_counter(); oc = dict(entries=0, missing=0, substituted=0, ambiguous=0)
    for t in range(N_DEC):
        with no_oracle_access(env):
            sets = deliv(env, seed, load, t); st['delivered'] += sum(len(x) for x in sets); st['unique'] += len(set().union(*sets))
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = RV2.merge_views(views, prev, t, iv, 'age'); now = float(env._now())
        ov = mv
        if ex is not None:
            ex.observe(views, prev); ov = ex.views(mv, t, now)
        if envk is not None:
            with no_oracle_access(envk):
                sk = dk(envk, seed, load, t); vk = envk.transmit(); envk.verify_mirror()
                bad = envk.check_access_invariants(vk)
                if bad:
                    raise AssertionError(f'access invariant (legacy): {bad[:3]}')
                mvk = RV2.merge_views(vk, prevk, t, iv, 'age'); prevk = mvk
            st['base_unique'] += len(set().union(*sk)); st['base_delivered'] += sum(len(sk[i]) for i in O)
            st['legacy_entries'] = max(st['legacy_entries'], sum(len(mvk[k].inbox) for k in range(m)))
            for i in range(m):
                if not np.array_equal(np.asarray(views[i].lane_vehicles), np.asarray(vk[i].lane_vehicles)):
                    raise AssertionError(f'legacy environment diverged physically at t={t}')
            ov = mvk
        prev = mv
        a_old = FB2.act_relay(pol_old, ov); a_new = FB2.act_relay(pol_new, mv)
        if gate is not None:
            az = FB2.act_z(zp, mv); fl = {i: bool(gate(FB2.view_stats(mv[i], t, iv, m - 1)[0])) for i in O}; st['flags'] += sum(fl.values())
        acts = {i: (int(az[i]) if (gate is not None and fl[i]) else int(a_old[i])) if i in O else int(a_new[i]) for i in range(m)}
        with no_oracle_access(env):
            _, _, rec = env.step(acts); per = MF1.agent_q(env)
        if envk is not None:
            with no_oracle_access(envk):
                _, _, reck = envk.step(acts)
            if reck['queue'] != rec['queue']:
                raise AssertionError(f'legacy environment queue diverged at t={t}')
        if abs(sum(per) - float(rec['queue'])) > 1e-6:
            raise AssertionError('per-agent queues do not sum to the step queue')
        q += float(rec['queue']); qa += np.asarray(per)
    out = dict(queue_sum=q, q_agents=qa.tolist(), seconds=time.perf_counter() - t0, old=sorted(O), **st)
    if ex is not None:
        out.update({f'emu_{k}': v for k, v in ex.cnt.items()}); out['buffer_old'] = sum(len(ex.seen[i]) for i in O)
    return out


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1); FB2.KEY_SLOTS['n'] = 8
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}; sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    book = json.loads((ROOT / a.codebook).read_text()); sc = Scenarios(out); t0 = time.perf_counter()
    cks = {'CK1': torch.load(a.old, weights_only=False)}; shas = {'CK1': sha(a.old)}
    for spec in a.alt:
        k, pth = spec.split('='); cks[k] = torch.load(pth, weights_only=False); shas[k] = sha(pth)
    ck_new = torch.load(a.new, weights_only=False); ckz = torch.load(a.z, weights_only=False); gates = {}
    if a.detectors:
        det = json.loads(Path(a.detectors).read_text())
        if det['relay_sha256'] != shas['CK1']:
            raise SystemExit('detectors belong to another checkpoint')
        gates = {n: RP2.gate_of(det['detectors'][n]) for n in ('FB_S+', 'FB_Mr-') if n in det['detectors']}
    rows = []; ids = {}
    for s in a.traffic_seeds:
        for h in a.headways:
            ep = f'seed{s}_load{h:g}'
            if not rows:
                ck = cks['CK1']
                ids['zteam'] = (MF1.zteam(sc, s, h, ckz)['queue_sum'], FB2.run_z(sc, s, h, ckz))
                ids['old_all'] = (mixed(sc, s, h, cks, ck_new, ckz, book, 'U1/PLAIN', 'ALL', gates)['queue_sum'], RP.run_arm(sc, s, h, ck, ckz, book, 0, 'PLAIN')['queue_sum'])
                ids['old_none'] = (mixed(sc, s, h, cks, ck_new, ckz, book, 'U1/PLAIN', 'NONE', gates)['queue_sum'], RP.run_arm(sc, s, h, ck_new, ckz, book, 0, 'PLAIN')['queue_sum'])
                ids['emu_all'] = (mixed(sc, s, h, cks, ck_new, ckz, book, 'U2/EMU_OLD', 'ALL', gates)['queue_sum'], ERE.episode(sc, s, h, ck, book, 'U2', 'EXACT_PACKET')[0]['queue_sum'])
                ids['proto_all'] = (mixed(sc, s, h, cks, ck_new, ckz, book, 'U2/EXACT_PROTO_OLD', 'ALL', gates)['queue_sum'], RP.run_arm(sc, s, h, ck, ckz, book, 1, 'PLAIN')['queue_sum'])
                bad = {k: v for k, v in ids.items() if abs(v[0] - v[1]) > 1e-6}
                if bad:
                    raise SystemExit(f'SELF-CHECK FAIL: first-episode identities {bad}')
            if a.refs:
                todo = [('ZTEAM', None), ('ALLOLD', ('K1/PLAIN', 'ALL')), ('ALLNEW', ('U1/PLAIN', 'NONE'))]
            else:
                todo = [(arm, (arm, a.layout)) for arm in a.arms]
            for name, spec in todo:
                r = MF1.zteam(sc, s, h, ckz) if spec is None else mixed(sc, s, h, cks, ck_new, ckz, book, spec[0], spec[1], gates)
                rows.append(dict(arm=name, layout=None if a.refs else a.layout, episode=ep, **r))
        print(f'[{time.perf_counter() - t0:.0f}s] seed {s}: ' + ', '.join(f"{r['arm']} {r['queue_sum']:.0f}" for r in rows if r['episode'] == f'seed{s}_load{a.headways[-1]:g}'), flush=True)
        (out / 'rows.json').write_text(json.dumps(rows))
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', identities=ids, args=vars(a), checkpoint_sha256=shas,
                                                       new_sha256=sha(a.new), z_sha256=sha(a.z), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--old', required=True); p.add_argument('--new', required=True); p.add_argument('--z', required=True)
    p.add_argument('--alt', nargs='*', default=[], help='NAME=checkpoint for arms CHAN/WHAT@NAME'); p.add_argument('--detectors')
    p.add_argument('--layout', choices=['D', 'C', 'ALL'], default='D')
    p.add_argument('--arms', nargs='+', default=['U1/PLAIN', 'U2/PLAIN', 'U2/EMU_OLD', 'U2/EXACT_PROTO_OLD', 'U1/FB_OLD', 'U1/FBR_OLD', 'K1/ROLLBACK'])
    p.add_argument('--refs', action='store_true'); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
