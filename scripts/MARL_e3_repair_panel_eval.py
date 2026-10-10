#!/usr/bin/env python3
"""PAIRED REPAIR PANEL evaluator (03/10/2026 18:1x EDT; PROTOCOL_E3_REPAIR_PANEL_20261003.md; external audit P1).
One process = one receiver checkpoint x one deployment channel K; every requested arm runs on the same episodes (same scenario
files, same exogenous capacity trace, same delivery rule), so the arms are paired.  The arm code paths are the existing ones,
imported, not re-implemented:
  PLAIN / FB_*  : MARL_e3_fallback_eval_v2 (relay_env, act_relay, act_z, z_policy, view_stats, run_z, run_relay for calibration);
  EMU           : MARL_e3_age_emulation_eval (emulate mode 'emu', push; per-slot floors);
  THR / MASK    : MARL_e3_joint_throttle_eval (choose, shadow_merge, masked) — THR is input-only (prev / mirror unthrottled).
Detectors (the audit's §4.4 fix): ONE distance function d2() for calibration thresholds and runtime decisions, rounded to 1e-9
(deterministic tie grouping), flag iff d2 > threshold; time bin as CONDITIONING ('+': one table / Gaussian / threshold per bin)
or pooled ('-').  FB_S± count < 3; FB_M± chi2_0.99(rank); FB_Mq± empirical 0.99 (smallest calibration value with weighted mass
<= it >= level, exact rational comparison).  No false-alarm guarantee is claimed; leave-one-episode-out rates are estimates.
Modes:
  --calibrate : rerun the receiver's training-channel calibration episodes with run_relay(record=...) of fallback v2, keep the
                counts PER EPISODE, assert their sum equals --calib-old exactly, build and freeze the six detectors in
                detectors.json (+ in-sample / leave-one-episode-out false alarm, and the change list vs the old v2 FB_Mq).
  --z-only    : Z (delivery none) on every episode.
  (default)   : the arms on the panel.
SELF-CHECKS (no manifest otherwise): calibration parity (above); runtime gates rebuilt from detectors.json reproduce the stored
calibration decisions on every key; on the first episode of each cell a never-firing gate = PLAIN, an always-firing gate = Z,
EMU with zero floors = PLAIN, THR with k = infinity = PLAIN (all exact); --parity-plain / --parity-arm rows reproduced at 1e-6;
access invariants and the oracle guard at every step; source hashes unchanged.
Run under scripts/MARL_grid_relay_wrapper.py for grids other than 3x3.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios, TRAIN
from models.marl_delivery_music import MusicDelivery
import models.marl_relay_v2 as RV2
import scripts.MARL_e3_fallback_eval_v2 as FB2
import scripts.MARL_e3_age_emulation_eval as EMM
import scripts.MARL_e3_joint_throttle_eval as JTM

SOURCES = ['scripts/MARL_e3_repair_panel_eval.py', 'scripts/MARL_e3_fallback_eval_v2.py', 'scripts/MARL_e3_age_emulation_eval.py',
           'scripts/MARL_e3_joint_throttle_eval.py', 'models/marl_relay_v2.py', 'models/marl_relay_v3.py', 'models/marl_delivery_music.py',
           'models/marl_comm_actor_quant.py', 'models/marl_comm_actor_set.py', 'models/marl_comm_actor.py',
           'scripts/MARL_e3_zero_loss_truncation.py', 'scripts/MARL_e3_actor_train_delivery_v7.py', 'envs/external/cityflow_budgeted.py',
           'envs/external/cityflow_hetero.py']
BIG = 10 ** 6
LEVEL = 0.99
N_MIN = 3
DETECTORS = ['FB_S+', 'FB_S-', 'FB_M+', 'FB_M-', 'FB_Mq+', 'FB_Mq-']


# ---------------------------------------------------------------- detectors (shared distance, deterministic ties)
def d2(x, mu, P):
    """THE distance: calibration thresholds and runtime decisions both call this (and nothing else)."""
    d = np.asarray(x, np.float64) - mu
    return round(float(d @ (P @ d)), 9)


def fit_gauss(feats, w):
    X = np.array(feats, np.float64); w = np.asarray(w, np.float64); w = w / w.sum()
    mu = (w[:, None] * X).sum(0); C = ((X - mu).T * w) @ (X - mu)
    return mu, np.linalg.pinv(C, rcond=1e-10), int(np.linalg.matrix_rank(C, tol=1e-10))


def emp_threshold(vals, cnts, level):
    """Smallest value v with (integer) mass{d2 <= v} >= level * total, exact rational comparison; equal values grouped."""
    L = Fraction(str(level)); agg = defaultdict(int)
    for v, c in zip(vals, cnts):
        agg[v] += int(c)
    tot = sum(agg.values()); cum = 0
    for v in sorted(agg):
        cum += agg[v]
        if cum * L.denominator >= L.numerator * tot:
            return v
    return max(agg)


def build(name, counts):
    """counts: {key tuple (tbin, 8 slots): integer count}.  Returns a JSON-serialisable spec."""
    cond = name.endswith('+'); fam = name[3:-1]
    if fam == 'S':
        tab = Counter()
        for k, c in counts.items():
            tab[tuple(k) if cond else tuple(k[1:])] += c
        return dict(name=name, kind='S', cond=cond, n=N_MIN, table=[[list(k), c] for k, c in sorted(tab.items())])
    groups = defaultdict(list)
    for k, c in counts.items():
        groups[str(k[0]) if cond else 'all'].append((tuple(k[1:]), c))
    prm = {}
    for b, kc in sorted(groups.items()):
        feats = [f for f, _ in kc]; cn = [c for _, c in kc]; mu, P, r = fit_gauss(feats, cn)
        if fam == 'M':
            from scipy.stats import chi2
            thr = round(float(chi2.ppf(LEVEL, max(r, 1))), 9)
        else:
            thr = emp_threshold([d2(f, mu, P) for f in feats], cn, LEVEL)
        prm[b] = dict(mu=mu.tolist(), P=P.tolist(), rank=r, thr=thr, n_keys=len(feats))
    return dict(name=name, kind='M', cond=cond, level=LEVEL, empirical=fam == 'Mq', params=prm)


def gate_of(spec):
    if spec['kind'] == 'S':
        tab = {tuple(k): c for k, c in spec['table']}; n = spec['n']
        if spec['cond']:
            return lambda key: tab.get(tuple(key), 0) < n
        return lambda key: tab.get(tuple(key[1:]), 0) < n
    prm = {b: (np.array(p['mu'], np.float64), np.array(p['P'], np.float64), p['thr']) for b, p in spec['params'].items()}
    cond = spec['cond']

    def g(key):
        b = str(key[0]) if cond else 'all'
        if b not in prm:                                  # a time bin never seen in calibration: out of support
            return True
        mu, P, thr = prm[b]
        return d2(key[1:], mu, P) > thr
    return g


def false_alarm(name, per_ep):
    """(in-sample weighted share flagged, leave-one-episode-out share): per_ep = list of Counters of keys."""
    tot = Counter()
    for c in per_ep:
        tot.update(c)
    g = gate_of(build(name, tot)); n = sum(tot.values())
    ins = sum(c for k, c in tot.items() if g(k)) / n
    fl = 0
    for c in per_ep:
        rest = tot.copy(); rest.subtract(c); rest = Counter({k: v for k, v in rest.items() if v > 0})
        ge = gate_of(build(name, rest)); fl += sum(v for k, v in c.items() if ge(k))
    return ins, fl / n


# ---------------------------------------------------------------- one episode of one arm
def run_arm(sc, seed, load, ck, ckz, book, K, arm, gate=None, floors=None, ktrain=1, n_slots=None):
    """Returns dict(queue_sum, ...).  arm: PLAIN | MASK | EMU | THR | FB (with gate(key) -> bool)."""
    env, pol = FB2.relay_env(sc, seed, load, ck, book, K); m = env.n_agents; iv = env.action_interval
    zp = FB2.z_policy(ckz, env) if arm == 'FB' else None
    mus = MusicDelivery('agefirst'); mus.mode = 'prefix'; prev = None; q = 0.0
    st = Counter(); caches = [dict() for _ in range(m)]; bufs = [dict() for _ in range(m)]; mem = 0; t0 = time.perf_counter()
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            mv = RV2.merge_views(views, prev, t, iv, 'age')
            st['delivered'] += sum(len({e.sender for e in views[i].inbox}) for i in range(m))
            if arm in ('PLAIN', 'FB'):
                rv = [mv[i] for i in range(m)]
            elif arm == 'MASK':
                rv = [JTM.masked(mv[i]) for i in range(m)]
            elif arm == 'EMU':
                rv = []
                for i in range(m):
                    w, a_, b_ = EMM.emulate(mv[i], bufs[i], floors['slot'].get(i, {}), iv, 'emu'); rv.append(w)
                    st['substituted'] += a_; st['missing'] += b_
                    EMM.push(bufs[i], mv[i], iv)
                mem = max(mem, sum(len(l) for b in bufs for l in b.values()))
            elif arm == 'THR':
                rv = []
                for i in range(m):
                    keep = JTM.choose(views[i], caches[i], ktrain)
                    st['dropped'] += len({e.sender for e in views[i].inbox}) - len(keep); st['accepted'] += len(keep)
                    rv.append(JTM.shadow_merge(views[i], i, keep, prev, caches[i], t, iv))
                    for e in views[i].inbox:
                        if e.sender in keep:
                            caches[i][e.sender] = e
                mem = max(mem, sum(len(c) for c in caches))
            else:
                raise ValueError(arm)
            prev = mv
            ar = FB2.act_relay(pol, rv)
            if arm == 'FB':
                fl = [bool(gate(FB2.view_stats(mv[i], t, iv, n_slots)[0])) for i in range(m)]; st['flags'] += sum(fl)
                az = FB2.act_z(zp, mv)
                acts = {i: int(az[i] if fl[i] else ar[i]) for i in range(m)}
            else:
                acts = {i: int(ar[i]) for i in range(m)}
            _, _, rec = env.step(acts)
        q += float(rec['queue'])
    return dict(queue_sum=q, decisions=N_DEC * m, seconds=time.perf_counter() - t0, mem_max=mem, **st)


# ---------------------------------------------------------------- modes
def calibrate(a, sc, ck, book, n_slots):
    regs = FB2.channel_of(ck); eps = [(s, h) for (s, h) in TRAIN if a.calib_lo <= s <= a.calib_hi]; per_ep = []
    for e, (s, h) in enumerate(eps):
        rec = []; FB2.run_relay(sc, s, h, ck, None, book, regs[e % len(regs)], None, n_slots, record=rec)
        per_ep.append(Counter(k for k, _ in rec))
    tot = Counter()
    for c in per_ep:
        tot.update(c)
    old = json.loads(Path(a.calib_old).read_text())
    if {tuple(k): c for k, c in old['counts']} != dict(tot):
        raise SystemExit('SELF-CHECK FAIL: calibration counts differ from the #3 calibration file')
    specs = {n: build(n, tot) for n in DETECTORS}; fa = {}
    for n in DETECTORS:
        ins, loo = false_alarm(n, per_ep); fa[n] = dict(in_sample=ins, loo_episode=loo)
    gate_new = gate_of(specs['FB_Mq-']); gate_old = FB2.mahalanobis_gate(old, LEVEL, True); n = sum(tot.values())
    changed = [[list(k), c, bool(gate_old(k, 0, 0)), bool(gate_new(k))] for k, c in sorted(tot.items()) if bool(gate_old(k, 0, 0)) != bool(gate_new(k))]
    flags = {n_: {json.dumps(list(k)): bool(gate_of(specs[n_])(k)) for k in tot} for n_ in DETECTORS}
    return dict(regimes=regs, episodes=eps, n_views=n, n_keys=len(tot), key_slots=FB2.KEY_SLOTS['n'], detectors=specs,
                false_alarm=fa, calibration_flags=flags,
                change_vs_old_FB_Mq=dict(keys=changed, mass=sum(c for _, c, _, _ in changed) / n,
                                         old_in_sample=sum(c for k, c in tot.items() if gate_old(k, 0, 0)) / n),
                per_episode_counts=[[[list(k), c] for k, c in sorted(ce.items())] for ce in per_ep])


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}
    book = json.loads((ROOT / a.codebook).read_text()); sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    sc = Scenarios(out); t0 = time.perf_counter(); FB2.KEY_SLOTS['n'] = 8
    eps = [(s, h) for s in a.traffic_seeds for h in a.headways]
    if a.z_only:
        ckz = torch.load(Path(a.z), weights_only=False); rows = []
        for s, h in eps:
            rows.append(dict(arm='Z', episode=f'seed{s}_load{h:g}', queue_sum=FB2.run_z(sc, s, h, ckz)))
        (out / 'rows.json').write_text(json.dumps(rows))
        man = dict(status='COMPLETE', self_check='PASS', mode='z_only', args=vars(a), z_sha256=sha(a.z), source_hashes=h0)
    else:
        ck = torch.load(Path(a.relay), weights_only=False); ck_sha = sha(a.relay)
        env0, _ = FB2.relay_env(sc, a.traffic_seeds[0] if a.traffic_seeds else 301, 8.0, ck, book, 0); n_slots = env0.n_agents - 1
        if a.calibrate:
            cal = calibrate(a, sc, ck, book, n_slots); cal.update(relay=a.relay, relay_sha256=ck_sha, calib_old_sha256=sha(a.calib_old), n_slots=n_slots)
            (out / 'detectors.json').write_text(json.dumps(cal))
            man = dict(status='COMPLETE', self_check='PASS', mode='calibrate', args=vars(a), relay_sha256=ck_sha, source_hashes=h0,
                       n_views=cal['n_views'], n_keys=cal['n_keys'], false_alarm=cal['false_alarm'],
                       change_vs_old_FB_Mq=dict(n_keys=len(cal['change_vs_old_FB_Mq']['keys']), mass=cal['change_vs_old_FB_Mq']['mass'],
                                                old_in_sample=cal['change_vs_old_FB_Mq']['old_in_sample']))
        else:
            gates = {}
            if any(x.startswith('FB_') for x in a.arms):          # detectors only when a gated arm runs (MIX: PLAIN only)
                det = json.loads(Path(a.detectors).read_text())
                if det['relay_sha256'] != ck_sha:
                    raise SystemExit('detectors were calibrated on another receiver checkpoint')
                gates = {n: gate_of(det['detectors'][n]) for n in DETECTORS}
                for n, fl in det['calibration_flags'].items():      # calibration / runtime parity of the decisions
                    for ks, f in fl.items():
                        if bool(gates[n](tuple(json.loads(ks)))) != f:
                            raise SystemExit(f'SELF-CHECK FAIL: {n} runtime decision differs from calibration on key {ks}')
            floors = None
            if 'EMU' in a.arms:
                fj = json.loads(Path(a.floors).read_text())
                if fj['checkpoint_sha256'] != ck_sha:
                    raise SystemExit('floors were calibrated on another checkpoint')
                floors = dict(rank=fj['rank'], slot={int(i): {int(j): f for j, f in d.items()} for i, d in fj['slot'].items()})
            ckz = torch.load(Path(a.z), weights_only=False)
            par = {}
            for spec in a.parity:                                   # ARM=path/rows.json[:key=value]
                arm, rest = spec.split('=', 1); path, _, flt = rest.partition(':'); fk, _, fv = flt.partition('=')
                for r in json.loads(Path(path).read_text()):
                    if not flt or str(r.get(fk)) == fv:
                        par[(arm, r['episode'])] = r['queue_sum']
            rows = []; checked = 0; npar = 0
            for s, h in eps:
                ep = f'seed{s}_load{h:g}'; res = {}
                for arm in a.arms:
                    if arm.startswith('FB_'):
                        res[arm] = run_arm(sc, s, h, ck, ckz, book, a.K, 'FB', gate=gates[arm], n_slots=n_slots)
                    else:
                        res[arm] = run_arm(sc, s, h, ck, ckz, book, a.K, arm, floors=floors, ktrain=a.ktrain, n_slots=n_slots)
                if not rows:                                         # first-episode identities
                    qp = res['PLAIN']['queue_sum']; qz = FB2.run_z(sc, s, h, ckz); ids = {}
                    if any(x.startswith('FB_') for x in a.arms):
                        ids['never'] = (run_arm(sc, s, h, ck, ckz, book, a.K, 'FB', gate=lambda k: False, n_slots=n_slots)['queue_sum'], qp)
                        ids['always'] = (run_arm(sc, s, h, ck, ckz, book, a.K, 'FB', gate=lambda k: True, n_slots=n_slots)['queue_sum'], qz)
                    if 'EMU' in a.arms:
                        zf = dict(rank=[0] * len(floors['rank']), slot={i: {j: 0 for j in d} for i, d in floors['slot'].items()})
                        ids['emu0'] = (run_arm(sc, s, h, ck, ckz, book, a.K, 'EMU', floors=zf, n_slots=n_slots)['queue_sum'], qp)
                    if 'THR' in a.arms:
                        ids['thrinf'] = (run_arm(sc, s, h, ck, ckz, book, a.K, 'THR', ktrain=BIG, n_slots=n_slots)['queue_sum'], qp)
                    bad = {k: v for k, v in ids.items() if abs(v[0] - v[1]) > 1e-6}
                    if bad:
                        raise SystemExit(f'SELF-CHECK FAIL: first-episode identities {bad}')
                    checked = len(ids)
                for arm, r in res.items():
                    if (arm, ep) in par:
                        if abs(par[(arm, ep)] - r['queue_sum']) > 1e-6:
                            raise SystemExit(f'SELF-CHECK FAIL: {arm} {ep} {r["queue_sum"]} != parity row {par[(arm, ep)]}')
                        npar += 1
                    rows.append(dict(arm=arm, receiver=a.tag, K=a.K, episode=ep, parity_checked=(arm, ep) in par, **r))
                if h == a.headways[-1]:
                    print(f'[{time.perf_counter() - t0:.0f}s] seed {s}: ' + ', '.join(f"{k} {v['queue_sum']:.0f}" for k, v in res.items()), flush=True)
                    (out / 'rows.json').write_text(json.dumps(rows))
            (out / 'rows.json').write_text(json.dumps(rows))
            man = dict(status='COMPLETE', self_check='PASS', mode='eval', K=a.K, args=vars(a), relay_sha256=ck_sha, z_sha256=sha(a.z),
                       detectors_sha256=sha(a.detectors) if gates else None, floors_sha256=sha(a.floors) if floors else None, identities_checked=checked,
                       parity_rows=npar, source_hashes=h0)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES + [a.codebook]}:
        raise RuntimeError('source changed during run')
    man['seconds'] = time.perf_counter() - t0
    (out / 'manifest.json').write_text(json.dumps(man, indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay'); p.add_argument('--z'); p.add_argument('--tag', default='')
    p.add_argument('--calibrate', action='store_true'); p.add_argument('--calib-old')
    p.add_argument('--calib-lo', type=int, default=301); p.add_argument('--calib-hi', type=int, default=332)
    p.add_argument('--z-only', action='store_true')
    p.add_argument('--detectors'); p.add_argument('--floors')
    p.add_argument('--arms', nargs='+', default=['PLAIN', 'MASK'] + DETECTORS)
    p.add_argument('--K', type=int, default=0, help='deployment K; 0 = iid'); p.add_argument('--ktrain', type=int, default=1)
    p.add_argument('--parity', nargs='*', default=[], help='ARM=rows.json[:key=value] stored rows to reproduce')
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='*', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    a = p.parse_args()
    if not a.calibrate and not a.z_only and 'PLAIN' not in a.arms:
        p.error('PLAIN is required (first-episode identities)')
    main(a)
