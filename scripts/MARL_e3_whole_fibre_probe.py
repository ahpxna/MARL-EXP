#!/usr/bin/env python3
"""WHOLE-FIBRE PROBE (01/10/2026 10:5x EDT; PROTOCOL_E3_WHOLE_FIBRE_PILOT_20261001.md).  DIAGNOSTIC ORACLE: it replays the
simulator to build alternative worlds and to value actions; no oracle quantity ever chooses an executed action.

Executed system = the V-D10 system: relay6Cage_st_s<s> closed loop, age-first order, capacity low, relay v2 merge, 3 B
codebook.  For each sampled receiver-state (episode, t, i):
  * ALTERNATIVE WORLDS: force one remote agent j != i to another valid phase at step t - delta (delta in {1, 2}), replay
    deterministically to step t, keep the world iff i's LOCAL observation at t is byte-identical; at most 11 kept, in the
    order (delta, round-robin over j by phase rank, j).  F = {original} + kept.
  * VALUES: for every world in F and every valid action a of i, V = -sum(queue_t .. queue_end) with i forced to a at t.
  * SPLITS: per world, per sender j, hashes of j's raw full-view block and of its 3 B quantised block at t (the receiver
    would see these if it decoded j fresh).
  * TEACHER PROXY at the original world: teacher logits on the full fresh view, on the zero-fresh CACHE-base view (the N_s
    definition) and on the view stripped to the local observation.
SELF-CHECKS (abort): the unforced replay of the original world equals the satrot row's episode waiting; forcing i to its
executed action reproduces the unforced value; every kept world has an identical local observation.
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
import scripts.MARL_e3_continuation_labels as CLAB
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery
from scripts.MARL_e3_theory_probe import net_of, empty_view

SOURCES = ['scripts/MARL_e3_whole_fibre_probe.py', 'scripts/MARL_e3_theory_probe.py', 'models/marl_relay_v2.py',
           'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py',
           'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py']
MAX_ALT = 11


def local_key(v):
    return hashlib.sha256(np.asarray(v.lane_vehicles).tobytes() + np.asarray(v.lane_waiting).tobytes() +
                          repr((int(v.own_phase), float(v.own_phase_elapsed), int(v.decision_step))).encode()).hexdigest()


def blocks(adapter, view, i, m):
    x = adapter.encode(view, 'actual'); own = adapter.own_dim + m; out = {}
    js = [j for j in range(m) if j != i]
    for n, j in enumerate(js):
        b = x[own + n * adapter.blk_dim: own + (n + 1) * adapter.blk_dim]
        out[j] = hashlib.sha256(np.round(b.astype(np.float64), 6).tobytes()).hexdigest()[:16]
    return out


class System:
    def __init__(self, sc, cks, book):
        CLAB.ActorNet = SetActorNet
        CLAB.CommAdapter = quantized(CommAdapter, book, 4)
        self.sc, self.cks = sc, cks
        self.teacher = None

    def episode(self, seed, load, force, cap_t=None, cap_i=None, stop_at_capture=False):
        """Closed loop with forced actions force[t][agent] = action; optional capture at (cap_t, receiver cap_i)."""
        env, pol = make(self.sc, seed, load, self.cks['relay'], 'low')
        m = env.n_agents
        if self.teacher is None:
            self.raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
            self.teacher = net_of(self.cks['teacher'], self.raw.dim); self.mask = torch.as_tensor(self.raw.valid_mask())
        mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; prev = None; Q = []; acts_log = []; cap = None
        for t in range(N_DEC):
            with no_oracle_access(env):
                mus(env, seed, load, t)
            if cap_t == t:
                cap = self.capture(env, cap_i, pol, m)                      # DIAGNOSTIC oracle
                if stop_at_capture:
                    return Q, acts_log, cap
            with no_oracle_access(env):
                views = env.transmit(); env.verify_mirror()
                bad = env.check_access_invariants(views)
                if bad:
                    raise AssertionError(f'access invariant: {bad[:3]}')
                mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
                X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
                with torch.no_grad():
                    L = pol.actor(torch.as_tensor(X), pol.mask).numpy()
                acts = {i: int(a) for i, a in enumerate(L.argmax(-1))}
                acts_log.append(dict(acts))
                if t in force:
                    acts.update(force[t])
                _, _, rec = env.step(acts)
            Q.append(float(rec['queue']))
        return Q, acts_log, cap

    def capture(self, env, i, pol, m):
        N = list(env.neighbours[i])
        v0 = env.counterfactual_view(i, [])            # zero fresh senders, cache kept (the N_s base)
        vf = env.counterfactual_view(i, N)             # every neighbour fresh
        ve = empty_view(v0)                             # local observation only
        with torch.no_grad():
            L = self.teacher(torch.as_tensor(np.stack([self.raw.encode(v, 'actual') for v in (vf, v0, ve)])),
                             self.mask[i:i + 1].expand(3, -1)).numpy()
        return dict(local=local_key(v0), raw=blocks(self.raw, vf, i, m), quant=blocks(pol.adapter, vf, i, m),
                    L_full=[round(float(x), 5) for x in L[0]], L_cache=[round(float(x), 5) for x in L[1]],
                    L_empty=[round(float(x), 5) for x in L[2]])


def probe_state(S, seed, load, t, i, valid):
    Q0, acts0, cap0 = S.episode(seed, load, {}, cap_t=t, cap_i=i)
    worlds = [dict(force={}, cap=cap0, acts=acts0)]
    cands = []
    for delta in (1, 2):
        if t - delta < 0:
            continue
        per_j = {j: [int(ph) for ph in valid[j] if int(ph) != acts0[t - delta][j]] for j in range(len(valid)) if j != i}
        depth = max(len(v) for v in per_j.values())
        for r in range(depth):
            for j in sorted(per_j):
                if r < len(per_j[j]):
                    cands.append((delta, j, per_j[j][r]))
    tried = 0
    for delta, j, ph in cands:
        if len(worlds) > MAX_ALT:
            break
        tried += 1
        f = {t - delta: {j: ph}}
        _, acts, cap = S.episode(seed, load, f, cap_t=t, cap_i=i, stop_at_capture=True)
        if cap['local'] == cap0['local']:
            worlds.append(dict(force=f, cap=cap, acts=acts))
    out_worlds = []
    for w in worlds:
        Vs = {}
        for a in valid[i]:
            f = {k: dict(v) for k, v in w['force'].items()}; f.setdefault(t, {})[i] = int(a)
            Q, acts, _ = S.episode(seed, load, f)
            Vs[int(a)] = -float(sum(Q[t:]))
            a_exec = acts[t][i]
        out_worlds.append(dict(force={str(k): {str(a): b for a, b in v.items()} for k, v in w['force'].items()},
                               V=Vs, a_exec=int(a_exec), raw=w['cap']['raw'], quant=w['cap']['quant'], local=w['cap']['local']))
        if w['cap']['local'] != cap0['local']:
            raise SystemExit('SELF-CHECK FAIL: kept world with a different local observation')
    v_unforced = -float(sum(Q0[t:]))
    if abs(out_worlds[0]['V'][out_worlds[0]['a_exec']] - v_unforced) > 1e-9:
        raise SystemExit(f'SELF-CHECK FAIL: forcing the executed action changes the value {seed}/{load}/t{t}/i{i}')
    return dict(episode=f'seed{seed}_load{load:g}', t=t, i=i, tried=tried, n_alt=len(worlds) - 1, worlds=out_worlds,
                teacher=dict(L_full=cap0['L_full'], L_cache=cap0['L_cache'], L_empty=cap0['L_empty'])), sum(Q0)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    cks = {'relay': torch.load(Path(a.relay), weights_only=False), 'teacher': torch.load(Path(a.teacher), weights_only=False)}
    ck_sha = {k: hashlib.sha256(Path(p).read_bytes()).hexdigest() for k, p in (('relay', a.relay), ('teacher', a.teacher))}
    sc = Scenarios(out); S = System(sc, cks, book)
    parity = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text()) if r['rule'] == 'prefix'}
    rng = np.random.default_rng(20261001 + a.seed)
    eps = [(s, h) for s in range(901, 933) for h in (8.0, 16.0)]
    plan = [(s, h, int(rng.integers(4, 22)), int(rng.integers(0, 9))) for s, h in eps]
    plan = plan[a.shard::a.nshards][:a.limit or None]
    rows_path = out / f'rows_shard{a.shard}.json'
    rows = json.loads(rows_path.read_text()) if rows_path.exists() else []
    done = {(r['episode'], r['t'], r['i']) for r in rows}; t0 = time.perf_counter()
    valid = None
    for seed, load, t, i in plan:
        key = (f'seed{seed}_load{load:g}', t, i)
        if key in done:
            continue
        if valid is None:
            S.episode(seed, load, {}, cap_t=0, cap_i=0, stop_at_capture=True)
            M = S.raw.valid_mask(); valid = [list(np.where(M[k])[0]) for k in range(M.shape[0])]
        row, q0 = probe_state(S, seed, load, t, i, valid)
        ep = key[0]
        if ep in parity and abs(parity[ep] - q0) > 1e-6:
            raise SystemExit(f'SELF-CHECK FAIL: {ep} replay waiting {q0} != satrot row {parity[ep]}')
        row['parity_checked'] = ep in parity
        rows.append(row); rows_path.write_text(json.dumps(rows))
        print(f'[{time.perf_counter() - t0:.0f}s] {ep} t{t} i{i}: tried {row["tried"]} kept {row["n_alt"]} '
              f'| {len(rows)}/{len(plan)}', flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / f'manifest_shard{a.shard}.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a),
        states=len(rows), parity_checked=sum(r['parity_checked'] for r in rows), checkpoint_sha256=ck_sha, source_hashes=h0,
        max_alt=MAX_ALT, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--seed', type=int, required=True); p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True)
    p.add_argument('--parity', required=True); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1)
    p.add_argument('--limit', type=int, default=0, help='smoke only: states'); p.add_argument('--out', required=True)
    main(p.parse_args())
