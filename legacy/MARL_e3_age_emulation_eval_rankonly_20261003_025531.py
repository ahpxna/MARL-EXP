#!/usr/bin/env python3
"""AGE EMULATION closed-loop evaluator (03/10/2026 03:0x EDT; PROTOCOL_E3_AGE_EMULATION_20261003.md; reviewer G2 / our H1).

The receiver-side analogue of the RI testbed's "minimal emulation" (L-263): a relay receiver trained on a poorer channel is
deployed on an upgraded one; before the ACTOR reads its merged view, entries that are fresher than the receiver's TRAINING
support are replaced by the TRUE older copy the receiver itself held earlier, with that copy's TRUE age (payload and age stay
coupled, a Blackwell garbling).  Control arm LAB: the same entries, the same displayed ages, but the FRESH payload kept (a
relabel — the age-remap type of edit that failed in L-266).  H1 predicts EMU > LAB.
Support = rank-wise age floors: sort a view's relayed entries by age (steps); floor[r] = the q-quantile (q = 0.05) of the r-th
smallest age over the receiver's own training-channel episodes (calibration seeds 301-332 × headways, plain relay).  An entry
of rank r with age < floor[r] is replaced by the most recent own-held copy of the same sender with true age >= floor[r]; if no
such copy exists the entry is kept (counted as 'missing').
The protocol state (what each node relays next step) is the unmodified merged view, exactly as in MARL_e3_ageclip_eval.py;
only the actor's input changes.  Deployable: uses only the receiver's own past merged views and offline training statistics.
SELF-CHECKS: (1) --parity rows.json reproduces plain episodes exactly; (2) with all floors 0 EMU and LAB equal PLAIN exactly
(--zero-floor-check on the first episode); (3) every substituted copy has measured_at <= the current copy's and an age equal
to its true age (assert).
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
from models.marl_relay_v2 import merge_views as merge_views_v2, AGE_CAP_STEPS
from models.marl_delivery_music import MusicDelivery

SOURCES = ['scripts/MARL_e3_age_emulation_eval.py', 'models/marl_relay_v2.py', 'models/marl_delivery_music.py',
           'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py',
           'scripts/MARL_e3_zero_loss_truncation.py', 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']
Q_FLOOR = 0.05
BUF_STEPS = AGE_CAP_STEPS + 2


def steps_of(v, e, interval):
    return min(AGE_CAP_STEPS, int(round((float(v.sim_time) - float(e.measured_at)) / float(interval))))


def emulate(v, buf, floors, interval, mode):
    """(view the actor reads, n substituted, n missing).  mode 'plain' | 'emu' | 'lab'."""
    if mode == 'plain' or not floors:
        return v, 0, 0
    ents = list(v.inbox); order = sorted(range(len(ents)), key=lambda k: (ents[k].age, ents[k].sender))
    n_sub = n_miss = 0
    for r, k in enumerate(order):
        if r >= len(floors):
            break
        e = ents[k]; a = steps_of(v, e, interval); f = int(floors[r])
        if a >= f:
            continue
        old = [c for c in buf.get(e.sender, ()) if steps_of(v, c, interval) >= f]
        if not old:
            n_miss += 1; continue
        c = max(old, key=lambda c: c.measured_at)
        assert c.measured_at <= e.measured_at, 'buffer copy newer than the current copy'
        sa = steps_of(v, c, interval) * float(interval)
        ents[k] = replace(c, age=sa, delivered_step=e.delivered_step) if mode == 'emu' else replace(e, age=sa)
        n_sub += 1
    return replace(v, inbox=tuple(ents)), n_sub, n_miss


def push(buf, v, interval):
    for e in v.inbox:
        lst = buf.setdefault(e.sender, [])
        if not lst or lst[-1].measured_at != e.measured_at:
            lst.append(e)
        cut = float(v.sim_time) - BUF_STEPS * float(interval)
        while lst and float(lst[0].measured_at) < cut:
            lst.pop(0)


def run(sc, seed, load, ck, book, K, mode, floors, record=None):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, ck, 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; ns = nm = 0
    bufs = [dict() for _ in range(m)]
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            rv = []
            for i in range(m):
                w, a, b = emulate(mv[i], bufs[i], floors, env.action_interval, mode); rv.append(w); ns += a; nm += b
                if record is not None:
                    record.append(sorted(steps_of(mv[i], e, env.action_interval) for e in mv[i].inbox))
                push(bufs[i], mv[i], env.action_interval)
            X = np.stack([pol.adapter.encode(rv[i], 'actual') for i in range(m)])
            with torch.no_grad():
                acts = {i: int(a) for i, a in enumerate(pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1))}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
    return q, ns, nm


def calibrate(sc, ck, book, K, seeds, loads):
    rec = []
    for s in seeds:
        for ld in loads:
            run(sc, s, ld, ck, book, K, 'plain', [], record=rec)
    R = max(len(x) for x in rec)
    floors = []
    for r in range(R):
        col = [x[r] for x in rec if len(x) > r]
        floors.append(int(np.floor(np.quantile(col, Q_FLOOR))) if col else 0)
    return floors, len(rec)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text()); ck = torch.load(Path(a.relay), weights_only=False)
    ck_sha = hashlib.sha256(Path(a.relay).read_bytes()).hexdigest()
    sc = Scenarios(out); t0 = time.perf_counter()
    if a.calibrate:
        floors, n = calibrate(sc, ck, book, a.calib_K, range(a.calib_lo, a.calib_hi + 1), a.headways)
        (out / 'floors.json').write_text(json.dumps(dict(floors=floors, q=Q_FLOOR, n_views=n, calib_K=a.calib_K,
            calib_seeds=[a.calib_lo, a.calib_hi], checkpoint_sha256=ck_sha)))
        print(f'[{time.perf_counter() - t0:.0f}s] floors {floors} from {n} views', flush=True)
    else:
        fl = json.loads(Path(a.floors).read_text())
        if fl['checkpoint_sha256'] != ck_sha:
            raise SystemExit('floors were calibrated on a different checkpoint')
        floors = fl['floors']
        par = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text())} if a.parity else {}
        rows = []; first = True
        for seed in a.traffic_seeds:
            for load in a.headways:
                ep = f'seed{seed}_load{load:g}'
                res = {md: run(sc, seed, load, ck, book, a.K, md, floors) for md in a.modes}
                if first and a.zero_floor_check:
                    z = {md: run(sc, seed, load, ck, book, a.K, md, [0] * len(floors))[0] for md in ('emu', 'lab')}
                    if any(abs(z[md] - res['plain'][0]) > 1e-6 for md in z):
                        raise SystemExit(f'SELF-CHECK FAIL: zero floors differ from plain {z} vs {res["plain"][0]}')
                    first = False
                if ep in par and abs(par[ep] - res['plain'][0]) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: {ep} plain {res["plain"][0]} != parity row {par[ep]}')
                for md, (q, ns, nm) in res.items():
                    rows.append(dict(actor=a.tag, mode=md, K=a.K, episode=ep, queue_sum=q, substituted=ns, missing=nm,
                                     parity_checked=ep in par and md == 'plain'))
            print(f'[{time.perf_counter() - t0:.0f}s] seed {seed}: ' + ', '.join(
                f'{md} {res[md][0]:.0f}/{res[md][1]}' for md in a.modes), flush=True)
            (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), checkpoint_sha256=ck_sha,
        source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--tag', required=True)
    p.add_argument('--calibrate', action='store_true'); p.add_argument('--calib-K', type=int, default=1)
    p.add_argument('--calib-lo', type=int, default=301); p.add_argument('--calib-hi', type=int, default=332)
    p.add_argument('--floors', default=None); p.add_argument('--K', type=int, default=0, help='constant K; 0 = iid')
    p.add_argument('--modes', nargs='+', default=['plain', 'emu', 'lab']); p.add_argument('--zero-floor-check', action='store_true')
    p.add_argument('--parity', default=None); p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
