#!/usr/bin/env python3
"""Support monitor + fallback to the compiled-silent student (02/10/2026 22:2x EDT; PROTOCOL_E3_SUPPORT_FALLBACK_20261002.md).

Two modes.
  --calibrate : the relay receiver in closed loop under its TRAINING channel (read from its config: iid / const<K> / mix
                regimes in rotation) on calibration episodes; records, per agent-decision, the support key and the mean age of
                the merged view it reads, and writes the monitor tables (key counts, per-time-bin quantiles, leave-one-episode-out
                false-alarm rates) to <out>/calib.json.
  (default)   : on the panel, deployment channel --K (0 = iid), five systems per episode:
                RELAY (the age-clip evaluator's code path with --A -1), Z (the zero-byte student under delivery 'none', the
                code path of MARL_e3_delivery_eval_v6.py), and FB_S / FB_F / FB_R: the relay system in which every agent whose
                merged view is flagged by the monitor acts with Z (Z reads the same view with every message removed, which is
                what it sees under delivery 'none') — the relay protocol state is untouched.  Sensitivity FB_S1 / FB_S10.
Monitors read only the receiver's own merged view (the ages it already holds) and the calibration file; no oracle call.
SELF-CHECKS (refuse to write a manifest otherwise): on the first episode, the fallback system with a never-firing monitor equals
RELAY and with an always-firing monitor equals Z exactly; --parity-relay / --parity-z rows are reproduced exactly where given;
access invariants and the oracle guard at every step; source hashes unchanged.
Run under scripts/MARL_grid_relay_wrapper.py for grids other than 3x3 (as the age-clip evaluator).
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from collections import Counter, defaultdict
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios, TRAIN
from scripts.MARL_e3_zero_loss_truncation import make
import scripts.MARL_e3_continuation_labels as CLAB
import scripts.MARL_e3_actor_train_delivery_v7 as DV
from models.marl_comm_actor import CommAdapter
from models.marl_comm_actor_set import SetActorNet
from models.marl_comm_actor_quant import quantized
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery

SOURCES = ['scripts/MARL_e3_fallback_eval.py', 'scripts/MARL_e3_ageclip_eval.py', 'scripts/MARL_e3_delivery_eval_v6.py',
           'models/marl_relay_v2.py', 'models/marl_relay_v3.py', 'models/marl_delivery_music.py', 'models/marl_comm_actor_quant.py',
           'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py', 'scripts/MARL_e3_zero_loss_truncation.py',
           'scripts/MARL_e3_actor_train_delivery_v7.py', 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']
MISSING = 15
BINS = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 5), (6, 8), (9, 14)]


def tbin(t):
    return 0 if t <= 4 else (1 if t <= 12 else 2)


KEY_SLOTS = {'n': None}                                        # None: raw counts; 8: counts rescaled to 8 proportional slots


def view_stats(v, t, interval, n_slots, hist=None):
    """(support key, mean age) of one merged view: ages in decision steps, an agent with no entry = missing.  With
    KEY_SLOTS['n'] = 8 every count c becomes round(8 c / n_slots) (identical to the raw counts when n_slots = 8).  hist (a
    list of 16 ints: ages 0..14, missing) accumulates the raw ages."""
    ages = [int(round(float(e.age) / float(interval))) for e in v.inbox]
    if len(ages) > n_slots:
        raise AssertionError(f'{len(ages)} entries > {n_slots} slots')
    c = [sum(lo <= a <= hi for a in ages) for lo, hi in BINS]
    if sum(c) != len(ages):
        raise AssertionError(f'age outside the bins: {ages}')
    miss = n_slots - len(ages)
    if hist is not None:
        for a_ in ages:
            hist[a_] += 1
        hist[15] += miss
    cc = c + [miss]
    if KEY_SLOTS['n']:
        cc = [int(round(KEY_SLOTS['n'] * x / n_slots)) for x in cc]
    return (tbin(t), *cc), float((sum(ages) + MISSING * miss) / n_slots)


def channel_of(ck):
    cfg = ck['config']; cap = cfg.get('capacity', 'iid')
    regs = cfg['mix_regimes'] if cap == 'mix' else [cap]
    return [0 if r == 'iid' else int(r.replace('const', '')) for r in regs]


def z_policy(ckz, env):
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    return CLAB.Policy(ckz, {i: env.public_topology(i) for i in range(env.n_agents)}, env.action_interval)


def relay_env(sc, seed, load, ck, book, K):
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = quantized(CommAdapter, book, 4)
    env, pol = make(sc, seed, load, ck, 'iid')
    if K > 0:
        env._trace = np.full_like(np.asarray(env._trace), int(K))
    return env, pol


def act_relay(pol, views):
    X = np.stack([pol.adapter.encode(views[i], 'actual') for i in range(len(views))])
    with torch.no_grad():
        return pol.actor(torch.as_tensor(X), pol.mask).numpy().argmax(-1)


def act_z(zp, views):
    X = np.stack([zp.adapter.encode(views[i], 'none') for i in range(len(views))])
    with torch.no_grad():
        return zp.actor(torch.as_tensor(X), zp.mask).numpy().argmax(-1)


def run_relay(sc, seed, load, ck, ckz, book, K, monitor, n_slots, record=None, hist=None):
    """The relay system; monitor(key, mean_age, t) -> True makes that agent act with Z.  Returns (queue_sum, flags, decisions)."""
    env, pol = relay_env(sc, seed, load, ck, book, K); zp = z_policy(ckz, env) if monitor is not None else None
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; m = env.n_agents; prev = None; q = 0.0; nf = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            ar = act_relay(pol, mv)
            if monitor is not None or record is not None or hist is not None:
                st = [view_stats(mv[i], t, env.action_interval, n_slots, hist) for i in range(m)]
                if record is not None:
                    record.extend(st)
            if monitor is not None:
                az = act_z(zp, mv); fl = [bool(monitor(k, a, t)) for k, a in st]; nf += sum(fl)
                acts = {i: int(az[i] if fl[i] else ar[i]) for i in range(m)}
            else:
                acts = {i: int(ar[i]) for i in range(m)}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
    return q, nf, N_DEC * m


def run_z(sc, seed, load, ckz):
    """MARL_e3_delivery_eval_v6.run with delivery 'none', capacity iid, the set actor and the default adapter."""
    CLAB.ActorNet = SetActorNet; CLAB.CommAdapter = CommAdapter
    env, pol = make(sc, seed, load, ckz, 'iid'); DV.DELIVERY['mode'] = 'none'; q = 0.0
    for t in range(N_DEC):
        with no_oracle_access(env):
            DV.deliver(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            acts = pol.act(views)
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
    return q


def calibrate(a, sc, ck, book, n_slots):
    regs = channel_of(ck); eps = [(s, h) for (s, h) in TRAIN if a.calib_lo <= s <= a.calib_hi]
    cnt = Counter(); per_ep = defaultdict(Counter); means = defaultdict(list); t0 = time.perf_counter(); ep_of = []; hist = [0] * 16
    for e, (s, h) in enumerate(eps):
        K = regs[e % len(regs)]; rec = []
        run_relay(sc, s, h, ck, None, book, K, None, n_slots, record=rec, hist=hist)
        for k, mean in rec:
            cnt[k] += 1; per_ep[e][k] += 1; means[k[0]].append(mean); ep_of.append((e, k, mean))
        if e % 8 == 7:
            print(f'[{time.perf_counter() - t0:.0f}s] calibration episode {e + 1}/{len(eps)}', flush=True)
    q = {str(b): dict(q025=float(np.percentile(v, 2.5)), q95=float(np.percentile(v, 95)), q975=float(np.percentile(v, 97.5)), n=len(v))
         for b, v in means.items()}
    loo = {n: float(np.mean([cnt[k] - per_ep[e][k] < n for e, k, _ in ep_of])) for n in (1, 3, 10)}
    fa_f = float(np.mean([mn > q[str(k[0])]['q95'] for _, k, mn in ep_of]))
    fa_r = float(np.mean([not (q[str(k[0])]['q025'] <= mn <= q[str(k[0])]['q975']) for _, k, mn in ep_of]))
    return dict(regimes=regs, episodes=eps, n_views=len(ep_of), n_keys=len(cnt), key_slots=KEY_SLOTS['n'], age_hist=hist,
                counts=[[list(k), c] for k, c in sorted(cnt.items())],
                quantiles=q, false_alarm=dict(S_loo={str(n): v for n, v in loo.items()}, F=fa_f, R=fa_r))


def monitors(cal):
    cnt = {tuple(k): c for k, c in cal['counts']}; q = cal['quantiles']
    S = lambda n: (lambda k, mn, t: cnt.get(tuple(k), 0) < n)
    F = lambda k, mn, t: mn > q[str(k[0])]['q95']
    R = lambda k, mn, t: not (q[str(k[0])]['q025'] <= mn <= q[str(k[0])]['q975'])
    return {'FB_S': S(3), 'FB_S1': S(1), 'FB_S10': S(10), 'FB_F': F, 'FB_R': R}


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text())
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    sc = Scenarios(out); t0 = time.perf_counter()
    if a.z_only:
        ckz = torch.load(Path(a.z), weights_only=False); rows = []
        pz = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity_z).read_text()) if r.get('rule', 'none') == 'none'} if a.parity_z else {}
        for seed in a.traffic_seeds:
            for load in a.headways:
                ep = f'seed{seed}_load{load:g}'; qz = run_z(sc, seed, load, ckz)
                if ep in pz and abs(pz[ep] - qz) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: Z {ep} {qz} != parity {pz[ep]}')
                rows.append(dict(system='Z', episode=ep, queue_sum=qz))
        (out / 'rows.json').write_text(json.dumps(rows))
        man = dict(status='COMPLETE', self_check='PASS', mode='z_only', args=vars(a), z_sha256=sha(a.z), traffic_seeds=a.traffic_seeds,
                   parity_z=sum(r['episode'] in pz for r in rows), source_hashes=h0)
        if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
            raise RuntimeError('source changed during run')
        man['seconds'] = time.perf_counter() - t0; (out / 'manifest.json').write_text(json.dumps(man, indent=1, default=str))
        print('COMPLETE', out, flush=True); return
    ck = torch.load(Path(a.relay), weights_only=False); KEY_SLOTS['n'] = a.key_slots
    env0, _ = relay_env(sc, a.traffic_seeds[0] if a.traffic_seeds else 301, 8.0, ck, book, 0); m = env0.n_agents; n_slots = m - 1
    if a.calibrate:
        cal = calibrate(a, sc, ck, book, n_slots); cal.update(relay=a.relay, relay_sha256=sha(a.relay), n_slots=n_slots)
        (out / 'calib.json').write_text(json.dumps(cal))
        man = dict(status='COMPLETE', self_check='PASS', mode='calibrate', args=vars(a), relay_sha256=sha(a.relay), source_hashes=h0,
                   n_views=cal['n_views'], n_keys=cal['n_keys'], false_alarm=cal['false_alarm'], regimes=cal['regimes'])
    else:
        cal = json.loads(Path(a.calib).read_text()); KEY_SLOTS['n'] = cal.get('key_slots')
        if cal['relay_sha256'] != sha(a.relay):
            raise SystemExit('calibration file is for another receiver checkpoint')
        ckz = torch.load(Path(a.z), weights_only=False); mons = {k: v for k, v in monitors(cal).items() if k in a.systems}
        pr = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity_relay).read_text())} if a.parity_relay else {}
        pz = {r['episode']: r['queue_sum'] for r in json.loads(Path(a.parity_z).read_text()) if r.get('rule', 'none') == 'none'} if a.parity_z else {}
        rows = []; checked = 0
        for seed in a.traffic_seeds:
            for load in a.headways:
                ep = f'seed{seed}_load{load:g}'
                hist = [0] * 16; qr, _, n = run_relay(sc, seed, load, ck, ckz, book, a.K, None, n_slots, hist=hist)
                qz = run_z(sc, seed, load, ckz) if (a.z_each or not rows) else None
                if ep in pr and abs(pr[ep] - qr) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: RELAY {ep} {qr} != parity {pr[ep]}')
                if qz is not None and ep in pz and abs(pz[ep] - qz) > 1e-6:
                    raise SystemExit(f'SELF-CHECK FAIL: Z {ep} {qz} != parity {pz[ep]}')
                if not rows:
                    qn = run_relay(sc, seed, load, ck, ckz, book, a.K, lambda k, mn, t: False, n_slots)[0]
                    qa = run_relay(sc, seed, load, ck, ckz, book, a.K, lambda k, mn, t: True, n_slots)[0]
                    if abs(qn - qr) > 1e-6 or abs(qa - qz) > 1e-6:
                        raise SystemExit(f'SELF-CHECK FAIL: never-firing {qn} vs RELAY {qr}; always-firing {qa} vs Z {qz}')
                    checked += 1
                rows.append(dict(system='RELAY', episode=ep, queue_sum=qr, flags=0, decisions=n, age_hist=hist))
                if qz is not None:
                    rows.append(dict(system='Z', episode=ep, queue_sum=qz, flags=n, decisions=n))
                for name, mon in mons.items():
                    q, nf, n = run_relay(sc, seed, load, ck, ckz, book, a.K, mon, n_slots)
                    rows.append(dict(system=name, episode=ep, queue_sum=q, flags=nf, decisions=n))
            print(f'[{time.perf_counter() - t0:.0f}s] seed {seed}: ' + ', '.join(f"{r['system']} {r['queue_sum']:.0f}/{r['flags']}" for r in rows if r['episode'] == f'seed{seed}_load8'), flush=True)
            (out / 'rows.json').write_text(json.dumps(rows))
        man = dict(status='COMPLETE', self_check='PASS', mode='eval', K=a.K, args=vars(a), relay_sha256=sha(a.relay), z_sha256=sha(a.z),
                   calib_sha256=sha(a.calib), never_always_checked=checked, parity_relay=sum(e in pr for e in {r['episode'] for r in rows}),
                   parity_z=sum(e in pz for e in {r['episode'] for r in rows if r['system'] == 'Z'}), traffic_seeds=a.traffic_seeds, source_hashes=h0)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    man['seconds'] = time.perf_counter() - t0
    (out / 'manifest.json').write_text(json.dumps(man, indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay'); p.add_argument('--z'); p.add_argument('--calib')
    p.add_argument('--z-only', action='store_true', help='Z under delivery none on every episode (one run per seed; the cells reuse it)')
    p.add_argument('--z-each', action='store_true', help='also run Z on every episode of a cell (default: first episode only, for the self-check)')
    p.add_argument('--systems', nargs='+', default=['FB_S', 'FB_S1', 'FB_S10', 'FB_F', 'FB_R'])
    p.add_argument('--calibrate', action='store_true'); p.add_argument('--calib-lo', type=int, default=301); p.add_argument('--calib-hi', type=int, default=332)
    p.add_argument('--K', type=int, default=0, help='deployment K; 0 = iid')
    p.add_argument('--key-slots', type=int, default=8, help='support key resolution (calibration; the eval reads it from calib.json); 0 = raw counts')
    p.add_argument('--parity-relay'); p.add_argument('--parity-z')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='*', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
