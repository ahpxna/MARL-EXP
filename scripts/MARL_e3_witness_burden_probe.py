#!/usr/bin/env python3
"""WITNESS-BURDEN probe (01/10/2026 21:4x EDT; PROTOCOL_E3_COMPAT_MAP_20261001.md Part C, EXPLORATORY).
The closed loop of MARL_e3_viewstats_probe_v3.py (relay6Cage_st_s<s>, relay v2 merge, 3 B codebook; --order, --capacity,
--K), with queue sums AND the need / zok / protoS flags required to equal --parity-dir (the existing order-dose / viewstats
flags), plus, per receiver-step and per RELAYED entry j of the merged view (age a >= 1):
  witness_j = the teacher's argmax changes when, in the full fresh counterfactual view, j's entry alone is replaced by the
              receiver's copy of j (its payload, age label 0 so the teacher stays in its own training format).
DIAGNOSTIC ORACLE (teacher, counterfactual views): recorded only; the executed actions are the relay student's.
D = sum_j witness_j (a_j - 3)+ is computed by the report.
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
from scripts.MARL_e3_theory_probe import net_of
from scripts.MARL_e3_negflip_probe import ZPol, pre_flags, EPS, SOURCES as NF_SOURCES

SOURCES = ['scripts/MARL_e3_witness_burden_probe.py', 'scripts/MARL_e3_viewstats_probe_v3.py'] + NF_SOURCES
COLS = ('ep', 't', 'recv', 'sender', 'age', 'witness', 'bad')


def run(sc, seed, load, cks, book, K, zpol, order, cap, ep):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    kind = cap if cap in ('iid', 'low', 'high', 'bursty') else 'iid'
    env, pol = make(sc, seed, load, cks['relay'], kind)
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    mus = MusicDelivery(order); mus.mode = cap if cap.startswith('cap') else 'prefix'; m = env.n_agents; prev = None; q = 0.0
    flags = []; rows = []; iv = float(env.action_interval)
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        pre = [pre_flags(env, i, teacher, raw, mask, zpol) for i in range(m)]                   # DIAGNOSTIC oracle
        vf = [env.counterfactual_view(i, sorted(int(j) for j in env.neighbours[i])) for i in range(m)]
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            X = np.stack([pol.adapter.encode(mv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                acts = {i: int(a) for i, a in enumerate(pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
        Xw, idx = [], []
        for i in range(m):
            need, zok, full, top = pre[i]
            flags.append((need, zok, bool(full[acts[i]] >= top - EPS - 1e-9)))
            Xw.append(raw.encode(vf[i], 'actual')); idx.append((i, -1, -1))
            for e in mv[i].inbox:
                a = int(round(float(e.age) / iv))
                if a < 1:
                    continue
                v = replace(vf[i], inbox=tuple(replace(x, payload=e.payload, measured_at=e.measured_at, age=0.0) if x.sender == e.sender else x
                                               for x in vf[i].inbox))
                Xw.append(raw.encode(v, 'actual')); idx.append((i, int(e.sender), a))
        M = torch.stack([mask[i] for i, _, _ in idx])
        with torch.no_grad():
            L = teacher(torch.as_tensor(np.stack(Xw)), M).numpy()
        base = {}
        for k, (i, j, a) in enumerate(idx):
            if j < 0:
                base[i] = (int(L[k].argmax()), L[k])
        for k, (i, j, a) in enumerate(idx):
            if j >= 0:
                b, Lb = base[i]; aj = int(L[k].argmax())
                rows.append((ep, t, i, j, a, int(aj != b), int(Lb[aj] < Lb.max() - EPS - 1e-9)))
    return q, flags, rows


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in (('relay', a.relay), ('teacher', a.teacher), ('z', a.z))}
    sc = Scenarios(out); pdir = Path(a.parity_dir)
    par = {r['episode']: r['queue_sum'] for r in json.loads((pdir / 'rows.json').read_text())}; pf = np.load(pdir / 'flags.npz')
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    _, zp0 = make(sc, a.traffic_seeds[0], a.headways[0], cks['z'], 'iid'); zpol = ZPol(cks['z'], zp0.adapter.topos, zp0.adapter.interval)
    allf, allr, t0 = [], [], time.perf_counter(); ep = 0
    for seed in a.traffic_seeds:
        for load in a.headways:
            name = f'seed{seed}_load{load:g}'; q, fl, rr = run(sc, seed, load, cks, book, a.K, zpol, a.order, a.capacity, ep)
            if name not in par or abs(par[name] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: {name} waiting {q} != parity row {par.get(name)}')
            allf += fl; allr += rr; ep += 1
    F = np.array(allf, bool)
    for n, k in enumerate(('need', 'zok', 'protoS')):
        if not np.array_equal(F[:, n], pf[k].astype(bool)):
            raise SystemExit(f'SELF-CHECK FAIL: flag {k} differs from {pdir}')
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    arr = np.array(allr, np.int64).reshape(-1, len(COLS))
    np.savez_compressed(out / 'witness.npz', **{k: arr[:, n] for n, k in enumerate(COLS)})
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), entries=len(allr), episodes=ep,
        source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, len(allr), 'relayed entries', f'{time.perf_counter() - t0:.0f}s', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--z', required=True)
    p.add_argument('--parity-dir', required=True); p.add_argument('--K', type=int, default=0)
    p.add_argument('--order', choices=['agefirst', 'prefix'], default='agefirst'); p.add_argument('--capacity', default='iid')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
