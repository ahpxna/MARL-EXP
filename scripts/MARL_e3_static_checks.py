#!/usr/bin/env python3
"""Static checks on STORED E3 artifacts (28/09 20:2x; the auditor's open list).  Inference only: no training, no rollouts.

S1  normalisation bug census (trainer: cs = std + 1e-6): for EVERY saved selector checkpoint, the context dims that
    were constant on TRAIN (cs < 1e-4), by block and field.  On stored states (original and dense DEV/SELECT labels):
    the largest |(c - cm)/cs| per state by snapshot t.  At t = 0 the receiver caches and the scheduler context are
    empty BY CONSTRUCTION (MessageCache starts empty; SchedulerContext has no packets), so every constant-1 'present'
    flag becomes (0 - 1)/1e-6.  Offline decision impact where stored states exist: the chosen index with the saved
    normaliser vs with those dims clamped to their training value (a DIAGNOSTIC, not an equivalent checkpoint).
S2  the 3-step gain g3 = cont - cont(P) versus the one-step gain g1 = cont_1 - cont_1(P) (both stored in the labels):
    oracle headroom of each; the g3 realised by the g1-argmax; within-state tie-aware Spearman of g1 with g3 and with
    the later part g3 - g1; the same for the saved legal and privileged v3 critics' scores.
S3  validation of the L-60 reconstruction WITHOUT a simulator: the labels store each receiver's bid (p1, p2), the
    actor's top-2 actions on its TRUE pre-transmission view (no fresh deliveries; the cache = the mirror, exact).
    The reconstructed pre-transmission input differs from the true one ONLY in the own block (lanes from the last
    paid payload split over 3 lanes; phase/elapsed one decision stale).  Reported: top-1 agreement with the stored p1,
    top-2 overlap, and the baseline 'the last paid phase'; plus how often the stored prefix action equals p1.
S4  does the offline 3-step DEV gain predict closed loop?  Per selector checkpoint (selectors_v2 ablation), the
    offline DEV realised gain (job dev_gain_mean) against its closed-loop paired change in Σ waiting vs the same
    actor's prefix (cl_v3_direct rows, 901-916); Spearman across checkpoints, per actor and pooled.
"""
from __future__ import annotations
import argparse, glob, json, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch
from scipy.stats import spearmanr

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, features, Net, choose
from scripts.MARL_e3_selector_diag_v2 import predictions
from models.marl_e3_response import RespNet
from models.marl_comm_actor import CommAdapter, ActorNet
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_emulation_probe import encode as legal_encode

M = ROOT / 'research/marl_budget'
FIELDS = ['present', 'age', 'phase', 'elapsed'] + [f'veh{k}' for k in range(4)] + [f'wait{k}' for k in range(4)]


def ctx_names(meta, m=9):
    n = ['z.time'] + [f'z.s{j}.{f}' for j in range(m) for f in FIELDS] + [f'K.{i}' for i in range(m)]
    n += [f'mirror.{i}<-{j}.{f}' for i in range(m) for j in range(m) if j != i for f in FIELDS]
    if meta.get('bid'):
        n += [f'bid.{i}.{x}' for i in range(m) for x in [f'p1_{k}' for k in range(9)] + [f'p2_{k}' for k in range(9)] + [f'gap{k}' for k in range(4)]]
    if meta.get('qbid'):
        n += [f'qbid.{i}' for i in range(m)]
    if meta.get('priv_joint'):
        n += [f'priv.P{i}_{k}' for i in range(m) for k in range(9)]
    if meta.get('resp_multi'):
        n += [f'multi.P{i}_{k}' for i in range(m) for k in range(9)]
    return n


def srho(a, b):
    return spearmanr(a, b).correlation if np.ptp(a) > 0 and np.ptp(b) > 0 else np.nan


def s1(ckpts, states_by_actor):
    census, impact = {}, {}
    for mf in ckpts:
        meta = torch.load(mf, weights_only=False); cs = np.asarray(meta['cs']); cm = np.asarray(meta['cm']); names = ctx_names(meta)
        if len(names) != len(cs):
            census[mf] = dict(error=f'layout {len(names)} != {len(cs)}'); continue
        const = np.where(cs < 1e-4)[0]; by = defaultdict(int)
        for k in const:
            nm = names[k]; blk = nm.split('.')[0]; fld = nm.split('.')[-1] if blk in ('z', 'mirror') else ''
            by[f'{blk}.{fld}' if fld else blk] += 1
        ones = [names[k] for k in const if names[k].endswith('.present') and cm[k] > 0.5]
        census[mf] = dict(ctx_dims=int(len(cs)), constant_dims=int(len(const)), by_block=dict(by), present_flags_constant_1=len(ones),
                          fires_at_t0=len(ones), example=[names[k] for k in const[:5]])
        actor = str(Path(mf).parents[1].relative_to(M)) if 'dense' not in mf else None
        if meta.get('qbid') or meta.get('priv_joint') or meta.get('resp_multi') or actor not in states_by_actor:
            continue
        net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); hn = None
        if meta.get('resp'):
            hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
        tau = meta['tau']['direct']; tau = {None: -np.inf, '-inf': -np.inf, '+inf': np.inf}.get(tau, tau) if not isinstance(tau, float) else tau
        rows = defaultdict(lambda: dict(n=0, big=0, changed=0, dgain=0.0))
        for tag, S in states_by_actor[actor].items():
            for st in S:
                an, y, feas, r1 = predictions(meta, net, hn, st); c = features(st, meta['bid'], meta['gap_thr'])[0]
                zmax = float(np.max(np.abs((c - cm) / cs))); key = f'{tag} t{st["t"]:02d}'; r = rows[key]; r['n'] += 1
                if zmax > 1e3:
                    r['big'] += 1
                    meta2 = dict(meta); cs2 = cs.copy(); cm2 = cm.copy(); dev = np.abs((c - cm) / cs) > 1e3
                    cm2[dev] = c[dev]; meta2['cm'] = cm2                                        # clamp: the deviating constant dims read as trained
                    an2, _, _, _ = predictions(meta2, net, hn, st)
                    j1 = choose(an, feas, np.ones_like(r1), tau); j2 = choose(an2, feas, np.ones_like(r1), tau)
                    r['changed'] += int(j1 != j2); r['dgain'] += float(y[j2] - y[j1])
        impact[mf] = {k: v for k, v in sorted(rows.items())}
    return census, impact


def s2(D, S, ckpts):
    out = {}
    g3o, g1o, g3_at_g1, same = [], [], [], []; r13, r1f = [], []
    for st in S:
        C = st['cands']; y3 = np.array([c['cont'] for c in C]) - C[0]['cont']; y1 = np.array([c['cont_1'] for c in C]) - C[0]['cont_1']
        ok = np.array([c['bytes'] <= st['b0'] + 84 for c in C])
        g3o.append(y3[ok].max()); g1o.append(y1[ok].max())
        best1 = np.where(ok & (y1 == y1[ok].max()))[0]; g3_at_g1.append(float(y3[best1].mean())); same.append(bool(y3[best1].max() == y3[ok].max()))
        r13.append(srho(y1[ok], y3[ok])); r1f.append(srho(y1[ok], (y3 - y1)[ok]))
    out['labels'] = dict(g3_oracle=round(float(np.mean(g3o)), 3), g1_oracle=round(float(np.mean(g1o)), 3), g3_of_g1_argmax=round(float(np.mean(g3_at_g1)), 3),
                         g1_argmax_contains_g3_best=round(float(np.mean(same)), 3), spearman_g1_g3=round(float(np.nanmean(r13)), 3),
                         spearman_g1_later=round(float(np.nanmean(r1f)), 3))
    for mf in ckpts:
        meta = torch.load(mf, weights_only=False); net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); hn = None
        if meta.get('resp'):
            hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
        a1, a3, af = [], [], []
        for st in S:
            an, y3, feas, _ = predictions(meta, net, hn, st); C = st['cands']; y1 = np.array([c['cont_1'] for c in C]) - C[0]['cont_1']; ok = feas.copy(); ok[0] = True
            a1.append(srho(an[ok], y1[ok])); a3.append(srho(an[ok], y3[ok])); af.append(srho(an[ok], (y3 - y1)[ok]))
        out[Path(mf).name] = dict(spearman_with_g1=round(float(np.nanmean(a1)), 3), with_g3=round(float(np.nanmean(a3)), 3), with_later=round(float(np.nanmean(af)), 3))
    return out


def s3(D, S, scratch):
    ckp = json.loads((D / 'labels_dev' / 'manifest.json').read_text())['args']['ckpt']; ck = torch.load(ROOT / ckp if not Path(ckp).is_absolute() else ckp, weights_only=False)
    sc = Scenarios(Path(scratch)); env0, topo0, _, _ = sc.env(501, 8.0); ad = CommAdapter(topo0, N_DEC, env0.action_interval)
    net = ActorNet(ad.dim, ck['config']['hidden']); net.load_state_dict(ck['actor']); net.eval(); mask = torch.as_tensor(ad.valid_mask())
    top1 = top2 = pers = pj = n = 0
    for st in S:
        m = st['m']; X = np.stack([legal_encode(ad, st, i, set()) for i in range(m)])
        with torch.no_grad():
            lg = net(torch.as_tensor(X), mask).numpy()
        o = np.argsort(-lg, 1)
        for i in range(m):
            b = st['bid'][i]; n += 1; top1 += int(o[i, 0] == b['p1']); top2 += int(o[i, 0] in (b['p1'], b['p2']))
            zph = int(round(st['z'][1 + 12 * i + 2] * 10)); pers += int(zph == b['p1']); pj += int(st['cands'][0]['joint'][i] == b['p1'])
    return dict(pairs=n, reconstructed_top1_eq_true_p1=round(top1 / n, 4), reconstructed_top1_in_true_top2=round(top2 / n, 4),
                last_paid_phase_eq_true_p1=round(pers / n, 4), stored_prefix_action_eq_p1=round(pj / n, 4))


def s4():
    pts = []
    for d in sorted(glob.glob(str(M / 'e3_*/actor_s*/cl_v3_direct/manifest.json'))):
        C = Path(d).parent; A = C.parent; rows = json.loads((C / 'rows.json').read_text()); per = defaultdict(lambda: defaultdict(list))
        for r in rows:
            per[r['method']][r['episode']] = r['queue_sum']
        pq = per['prefix']
        for meth, E in per.items():
            if '/s' not in meth:
                continue
            name, s = meth.split('/s'); job = A / 'selectors_v2' / f'job_{name}_s{s}.json'
            if not job.exists():
                continue
            off = json.loads(job.read_text())['results']['direct']['dev_gain_mean']
            cl = float(np.mean([100 * (E[e] - pq[e]) / pq[e] for e in pq]))
            pts.append(dict(actor=str(A.relative_to(M)), ckpt=meth, offline_dev_gain=round(off, 3), closed_loop_pct=round(cl, 3)))
    out = dict(points=pts)
    for a in sorted({p['actor'] for p in pts}) + ['ALL']:
        P = [p for p in pts if a == 'ALL' or p['actor'] == a]
        x = [p['offline_dev_gain'] for p in P]; y = [-p['closed_loop_pct'] for p in P]   # sign: positive = the selector reduced waiting
        out[a] = dict(n=len(P), spearman_offline_gain_vs_closed_loop_reduction=round(float(srho(np.array(x), np.array(y))), 3))
    return out


def main(a):
    rep = {}
    actors = {'scratch_s3': M / 'e3_scratch_seeds34_20260928/actor_s3', 'bc_s3': M / 'e3_run_seeds34_20260928/actor_s3'}
    states = {}
    for d in sorted(glob.glob(str(M / 'e3_*/actor_s*/labels_dev/manifest.json'))):
        A = Path(d).parents[1]
        if 'smoke' in str(A):
            continue
        S = {'dev': load([A / 'labels_dev'])[0]}
        if (A / 'dense/labels_dev/manifest.json').exists():
            S['dense_dev'] = load([A / 'dense/labels_dev'])[0]
        states[str(A.relative_to(M))] = S
    ckpts = sorted(f for f in glob.glob(str(M / 'e3_*/actor_s*/*/model_*.pt')) if 'smoke' not in f)
    census, impact = s1(ckpts, states)
    rep['S1_census'] = {str(Path(k).relative_to(M)): v for k, v in census.items()}; rep['S1_offline_impact'] = {str(Path(k).relative_to(M)): v for k, v in impact.items()}
    print(f'S1: {len(census)} checkpoints', flush=True)
    for k, v in list(rep['S1_census'].items()):
        if 'error' in v:
            print('   ', k, v['error'])
    tot = defaultdict(list)
    for k, v in rep['S1_census'].items():
        if 'error' not in v:
            tot[k.split('/')[0] + '/' + k.split('/')[1]].append((v['constant_dims'], v['present_flags_constant_1']))
    for a_, L in tot.items():
        print(f'    {a_:40s} checkpoints {len(L)}: constant ctx dims {min(x for x, _ in L)}-{max(x for x, _ in L)}; constant-1 present flags {min(y for _, y in L)}-{max(y for _, y in L)} (all fire at t = 0)')
    agg = defaultdict(lambda: dict(n=0, big=0, changed=0, dgain=0.0))
    for k, v in rep['S1_offline_impact'].items():
        for key, r in v.items():
            g = agg[f'{k.split("/")[0]}/{k.split("/")[1]} {key.split(" ")[0]} {key.split(" ")[1]}']
            for f in ('n', 'big', 'changed'):
                g[f] += r[f]
            g['dgain'] += r['dgain']
    rep['S1_offline_impact_by_t'] = {k: v for k, v in sorted(agg.items())}
    for k, v in sorted(agg.items()):
        if v['big']:
            print(f'    impact {k}: states x ckpts {v["n"]}, |z|>1e3 in {v["big"]}, choice changed by clamping {v["changed"]}, Δgain sum {v["dgain"]:+.1f}')
    print('    (states x ckpts with no |z| > 1e3 are omitted)', flush=True)
    for name, D in actors.items():
        S = load([D / 'labels_dev'])[0]
        r = dict(S2=s2(D, S, sorted(glob.glob(str(D / 'selectors_v3/model_*.pt')))), S3=s3(D, S, Path(a.scratch) / name)); rep[name] = r
        print(f'S2 {name}: {r["S2"]["labels"]}', flush=True)
        for k, v in r['S2'].items():
            if k != 'labels':
                print(f'    {k:32s} {v}')
        print(f'S3 {name}: {r["S3"]}', flush=True)
    rep['S4'] = s4()
    for k, v in rep['S4'].items():
        if k != 'points':
            print(f'S4 {k}: {v}')
    Path(a.out).write_text(json.dumps(rep, indent=1, default=float))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--out', required=True); p.add_argument('--scratch', required=True); main(p.parse_args())
