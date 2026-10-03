#!/usr/bin/env python3
"""SAFEEDIT probe (01/10/2026 20:5x EDT; PROTOCOL_E3_SAFEEDIT_PROBE_20261001.md, EXPLORATORY; subagent A, H5).
Closed loop of MARL_e3_age_cf_probe.py: relay6Cage_st_s<s> acts on its actual merged view (age-first, relay v2, 3 B codebook),
const K (K = 0: iid); queue sums must equal --parity rows.
DIAGNOSTIC ORACLE, recorded only: the teacher's logits on the full fresh counterfactual view (pre_flags) and Z's action on the
empty view (its acceptability flag must equal pre_flags').  Per receiver-step: relay logits on the actual view and on 11
synthetic views in which every relayed inbox entry (age > 0) is relabelled to a common age a = 0..10 (content unchanged);
b3 = sum (age - 3)+ over the inbox ages in decision steps (the gate statistic), relayed / fresh / never-heard counts.
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
from scripts.MARL_e3_negflip_probe import ZPol, pre_flags, empty_view, EPS, SOURCES as NF_SOURCES

SOURCES = ['scripts/MARL_e3_safeedit_probe.py'] + NF_SOURCES
AGES = list(range(11))


def run(sc, seed, load, cks, book, K, zpol):
    CLAB.ActorNet = SetActorNet
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, cks['relay'], 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    raw = CommAdapter(pol.adapter.topos, pol.adapter.n_dec, pol.adapter.interval)
    if raw.dim != pol.adapter.dim or raw.dim != zpol.adapter.dim:
        raise AssertionError('teacher, relay and Z encodings differ in dimension')
    teacher = net_of(cks['teacher'], raw.dim); mask = torch.as_tensor(raw.valid_mask())
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; R = []
    iv = float(env.action_interval)
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        pre = [pre_flags(env, i, teacher, raw, mask, zpol) for i in range(m)]                   # DIAGNOSTIC oracle
        xz = np.stack([zpol.adapter.encode(empty_view(env, i), 'actual') for i in range(m)])
        with torch.no_grad():
            az = zpol.actor(torch.as_tensor(xz), zpol.mask).numpy().argmax(-1)
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            X = [pol.adapter.encode(mv[i], 'actual') for i in range(m)]
            for a in AGES:
                X += [pol.adapter.encode(replace(mv[i], inbox=tuple(replace(e, age=a * iv) if float(e.age) > 0 else e for e in mv[i].inbox)),
                                         'actual') for i in range(m)]
            with torch.no_grad():
                Lr = pol.actor(torch.as_tensor(np.stack(X)), pol.mask.repeat(len(AGES) + 1, 1)).numpy()
            acts = {i: int(a) for i, a in enumerate(Lr[:m].argmax(-1))}
            stats = []
            for i in range(m):
                ages = [float(e.age) / iv for e in mv[i].inbox]
                stats.append((sum(max(x - 3.0, 0.0) for x in ages), sum(x > 0 for x in ages), sum(x == 0 for x in ages),
                              len(mv[i].neighbours) - len(ages)))
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
        for i in range(m):
            need, zok, full, top = pre[i]
            if bool(full[int(az[i])] >= top - EPS - 1e-9) != bool(zok):
                raise AssertionError(f'Z action re-derivation differs from pre_flags at t={t} receiver {i}')
            R.append(dict(t=t, recv=i, T=np.asarray(full, np.float32), mask=raw.valid_mask()[i].astype(bool), az=int(az[i]),
                          L=np.stack([Lr[k * m + i] for k in range(len(AGES) + 1)]).astype(np.float32),
                          b3=stats[i][0], nrel=stats[i][1], nfresh=stats[i][2], nev=stats[i][3]))
    return q, R


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    cks = {k: torch.load(Path(getattr(a, k)), weights_only=False) for k in ('relay', 'teacher', 'z')}
    sc = Scenarios(out); par = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity).read_text())}
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    _, zp0 = make(sc, a.traffic_seeds[0], a.headways[0], cks['z'], 'iid'); zpol = ZPol(cks['z'], zp0.adapter.topos, zp0.adapter.interval)
    rows = []; allr = []; t0 = time.perf_counter(); n_par = 0
    for seed in a.traffic_seeds:
        for load in a.headways:
            ep = f'seed{seed}_load{load:g}'; q, rr = run(sc, seed, load, cks, book, a.K, zpol)
            if ep in par:
                if abs(par[ep] - q) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: {ep} waiting {q} != parity row {par[ep]}')
                n_par += 1
            elif not a.allow_unchecked:
                raise SystemExit(f'SELF-CHECK FAIL: no parity row for {ep}')
            rows.append(dict(episode=ep, queue_sum=q)); allr += [dict(ep=len(rows) - 1, **r) for r in rr]
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    np.savez_compressed(out / 'records.npz', **{k: np.stack([r[k] for r in allr]) for k in
                        ('ep', 't', 'recv', 'T', 'mask', 'az', 'L', 'b3', 'nrel', 'nfresh', 'nev')}, ages=np.array(AGES))
    (out / 'rows.json').write_text(json.dumps(rows))
    sha = {k: hashlib.sha256(Path(getattr(a, k)).read_bytes()).hexdigest() for k in ('relay', 'teacher', 'z')}
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', eps=EPS, K=a.K, args=vars(a), records=len(allr),
        parity_episodes=n_par, checkpoint_sha256=sha, source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, len(allr), 'records', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay', required=True); p.add_argument('--teacher', required=True); p.add_argument('--z', required=True)
    p.add_argument('--parity', required=True); p.add_argument('--K', type=int, required=True)
    p.add_argument('--allow-unchecked', action='store_true', help='smoke only: episodes without a parity row')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
