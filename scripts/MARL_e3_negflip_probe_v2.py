#!/usr/bin/env python3
"""v2 (01/10/2026 12:2x EDT; PROTOCOL_E3_G4_REPLICATION_ADDENDUM2_20261001.md): MARL_e3_negflip_probe.py with --capacity
{iid, fixed, high, low, bursty, const<k>} (the relay v6 evaluator's capacity processes) instead of --K.  Everything else —
flags, Z parity at every step against a Z no-delivery development run (--zrows), oracle labelling — is v1's code, imported.
With --capacity const<k> this is v1 --K k; with iid it is v1 --K 0.  Runs on any grid through scripts/MARL_grid_relay_wrapper.py.
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
import scripts.MARL_e3_negflip_probe as V1

SOURCES = ['scripts/MARL_e3_negflip_probe_v2.py'] + V1.SOURCES


def run(sc, seed, load, cks, book, cap, zpol):
    """v1.run with the capacity process `cap` (make(..., cap) for the trace kinds, a constant trace for const<k>)."""
    orig = V1.make
    if cap.startswith('const'):
        return V1.run(sc, seed, load, cks, book, int(cap[5:]), zpol)
    V1.make = lambda sc_, s_, l_, ck_, _c: orig(sc_, s_, l_, ck_, cap)
    try:
        return V1.run(sc, seed, load, cks, book, 0, zpol)
    finally:
        V1.make = orig


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    paths = (('relay', a.relay), ('teacher', a.teacher), ('z', a.z))
    cks = {k: torch.load(Path(v), weights_only=False) for k, v in paths}
    ck_sha = {k: hashlib.sha256(Path(p).read_bytes()).hexdigest() for k, p in paths}
    sc = Scenarios(out)
    zrows = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.zrows).read_text()) if r['rule'] == 'none'}
    rpar = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text()) if r.get('rule', 'prefix') == 'prefix'} if a.parity else {}
    rows = []; allrec = []; t0 = time.perf_counter(); zpol = None
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'
            if zpol is None:
                CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
                _, zp0 = make(sc, seed, load, cks['z'], 'iid'); zpol = V1.ZPol(cks['z'], zp0.adapter.topos, zp0.adapter.interval)
            qz = V1.z_parity(sc, seed, load, cks['z'], zpol)
            if ep not in zrows or abs(zrows[ep] - qz) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: Z {ep} waiting {qz} != Z development row {zrows.get(ep)}')
            q, rr = run(sc, seed, load, cks, book, a.capacity, zpol)
            if ep in rpar and abs(rpar[ep] - q) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: relay {ep} waiting {q} != relay evaluator row {rpar[ep]}')
            rows.append(dict(episode=ep, queue_sum=q, z_queue_sum=qz))
            allrec += [dict(seed=seed, load=load, **r) for r in rr]
            print(f'[{time.perf_counter() - t0:.0f}s] {ep} done (Z parity ok)', flush=True)
    keys = ['seed', 'load', 't', 'recv', 'need', 'zok', 'protoS', 'n_ent', 'mean_age', 'max_age']
    np.savez_compressed(out / 'flags.npz', **{k: np.array([r[k] for r in allrec]) for k in keys})
    (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', eps=V1.EPS, capacity=a.capacity, args=vars(a),
        z_parity_episodes=len(rows), relay_parity_episodes=sum(r['episode'] in rpar for r in rows), checkpoint_sha256=ck_sha, source_hashes=h0, records=len(allrec),
        seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--z', required=True)
    p.add_argument('--zrows', required=True); p.add_argument('--capacity', required=True); p.add_argument('--parity', default=None, help='relay evaluator rows (rule prefix) to reproduce')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    a = p.parse_args()
    if not (a.capacity in ('iid', 'fixed', 'high', 'low', 'bursty') or (a.capacity.startswith('const') and a.capacity[5:].isdigit())):
        raise SystemExit(f'unknown capacity {a.capacity}')
    main(a)
