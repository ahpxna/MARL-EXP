#!/usr/bin/env python3
"""CROSS-CHANNEL FLIP probe (03/10/2026 04:0x EDT; PROTOCOL_E3_CROSSCHANNEL_FLIP_20261003.md; EXPLORATORY, development episodes).
Bansal / PCT / Srivastava-style compatibility of a FROZEN receiver across channels on IDENTICAL states: the zero-byte student Z
drives every intersection from its LOCAL view only, so the world trajectory of an episode is the same under every channel; each
channel (const1, const2, const3, iid; age-first prefix delivery, relay v2 merge) builds its own merged views, and every receiver
(relay students) is evaluated — never executed — on them.  Acceptability = A_0.25 of the teacher on the full fresh
counterfactual view (DIAGNOSTIC oracle, recorded only; as in MARL_e3_negflip_probe.py).  Per receiver and channel pair (A -> B):
negative flips NF = P(acc_A & not acc_B), positive flips PF, BTC = P(acc_B | acc_A), action agreement.
SELF-CHECKS: Z's queue sum is identical under every channel (the channel cannot reach the world); the teacher's acceptable sets
are identical under every channel at every (t, receiver); evaluator mirror and access invariants.
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
import scripts.MARL_e3_continuation_labels as CLAB
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery
from scripts.MARL_e3_negflip_probe import ZPol, EPS
from scripts.MARL_e3_theory_probe import net_of

SOURCES = ['scripts/MARL_e3_crosschannel_flip_probe.py', 'scripts/MARL_e3_negflip_probe.py', 'scripts/MARL_e3_theory_probe.py',
           'scripts/MARL_e3_continuation_labels.py', 'models/marl_relay_v2.py', 'models/marl_delivery_music.py',
           'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py',
           'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']
CAPS = ('const1', 'const2', 'const3', 'iid')


def local_only(v):
    """Z's input: its local view only (as in MARL_e3_staleness_meaning_probe.py), so its actions cannot depend on the channel."""
    return replace(v, inbox=(), cache=(), never_heard=tuple(sorted(int(j) for j in v.neighbours)))


def run(sc, seed, load, cap, zck, recv, tck, book, need_acc):
    """Z drives; returns (queue sum, {tag: actions (T, m)}, acceptable (T, m, A) bool or None)."""
    env, topo, _, _ = sc.env(seed, load)
    if cap.startswith('const'):
        env._trace = np.full_like(np.asarray(env._trace), int(cap[5:]))
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    zpol = ZPol(zck, topo, env.action_interval)
    raw = CommAdapter(topo, N_DEC, env.action_interval); mask = torch.as_tensor(raw.valid_mask()); teacher = net_of(tck, raw.dim)
    CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    pols = {tag: CLAB.Policy(ck, topo, env.action_interval) for tag, ck in recv.items()}
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0
    acts = {tag: np.zeros((N_DEC, m), np.int64) for tag in recv}; acc = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
        if need_acc:                                                                     # DIAGNOSTIC oracle, recorded only
            rows = []
            for i in range(m):
                N = sorted(int(j) for j in env.neighbours[i]); vf = env.counterfactual_view(i, N)
                with torch.no_grad():
                    L = teacher(torch.as_tensor(raw.encode(vf, 'actual')[None]), mask[i:i + 1]).numpy()[0]
                rows.append(L >= L.max() - EPS - 1e-9)
            acc.append(np.stack(rows))
        with no_oracle_access(env):
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            for tag, pol in pols.items():
                acts[tag][t] = pol.logits([mv[i] for i in range(m)]).argmax(-1)
            az = zpol.act_views([local_only(mv[i]) for i in range(m)])
            _, _, rec = env.step({i: int(az[i]) for i in range(m)})
        q += float(rec['queue'])
    return q, acts, (np.stack(acc) if need_acc else None)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    zck = torch.load(Path(a.z), weights_only=False); tck = torch.load(Path(a.teacher), weights_only=False)
    recv = {}; sha = {}
    for spec in a.receivers:
        tag, path = spec.split('=', 1); recv[tag] = torch.load(Path(path), weights_only=False)
        sha[tag] = hashlib.sha256(Path(path).read_bytes()).hexdigest()
    sc = Scenarios(out); t0 = time.perf_counter(); A = {c: {tag: [] for tag in recv} for c in a.caps}; ACC = []; eps = []
    for seed in a.traffic_seeds:
        for load in a.headways:
            qs = {}; acc0 = None
            for c in a.caps:
                q, acts, acc = run(sc, seed, load, c, zck, recv, tck, book, need_acc=True)
                qs[c] = q
                if acc0 is None:
                    acc0 = acc
                elif not np.array_equal(acc0, acc):
                    raise SystemExit(f'SELF-CHECK FAIL: seed{seed}_load{load:g}: teacher acceptable sets differ under {c}')
                for tag in recv:
                    A[c][tag].append(acts[tag])
            if max(qs.values()) - min(qs.values()) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: seed{seed}_load{load:g} Z queue sums differ across channels: {qs}')
            ACC.append(acc0); eps.append(f'seed{seed}_load{load:g}')
        print(f'[{time.perf_counter() - t0:.0f}s] seed {seed} done', flush=True)
    acc = np.concatenate(ACC)                                                             # (E*T, m, A)
    summ = {}
    for tag in recv:
        act = {c: np.concatenate(A[c][tag]) for c in a.caps}                              # (E*T, m)
        ok = {c: np.take_along_axis(acc, act[c][..., None], -1)[..., 0] for c in a.caps}
        summ[tag] = dict(acc={c: float(ok[c].mean()) for c in a.caps}, pairs={})
        for ca in a.caps:
            for cb in a.caps:
                if ca == cb:
                    continue
                nf = float((ok[ca] & ~ok[cb]).mean()); pf = float((~ok[ca] & ok[cb]).mean())
                btc = float((ok[ca] & ok[cb]).sum() / max(1, ok[ca].sum())); agree = float((act[ca] == act[cb]).mean())
                summ[tag]['pairs'][f'{ca}->{cb}'] = dict(nf=nf, pf=pf, net=pf - nf, btc=btc, agree=agree)
        np.savez_compressed(out / f'acts_{tag}.npz', **{c: act[c] for c in a.caps})
    np.savez_compressed(out / 'acceptable.npz', acc=acc)
    (out / 'summary.json').write_text(json.dumps(summ, indent=1))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), episodes=eps,
        receiver_sha256=sha, z_sha256=hashlib.sha256(Path(a.z).read_bytes()).hexdigest(),
        teacher_sha256=hashlib.sha256(Path(a.teacher).read_bytes()).hexdigest(), source_hashes=h0,
        seconds=time.perf_counter() - t0), indent=1, default=str))
    for tag, s in summ.items():
        print(tag, 'acc', {c: round(v, 3) for c, v in s['acc'].items()}, '| const1->iid',
              {k: round(v, 3) for k, v in s['pairs']['const1->iid'].items()} if 'const1->iid' in s['pairs'] else '', flush=True)
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--z', required=True); p.add_argument('--teacher', required=True)
    p.add_argument('--receivers', nargs='+', required=True, help='tag=path/ckpt_best.pt')
    p.add_argument('--caps', nargs='+', default=list(CAPS))
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
