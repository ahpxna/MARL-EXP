#!/usr/bin/env python3
"""B2 confirmation v2 (PROTOCOL_B2_FRESH_BID_20260927.md, Amendment 1): frozen evaluation that also
covers the development-screen bids added by the amendment (mlp_top2, mlp_top2_joint,
mlp_bid_request).  v1 (MARL_hetero_b2_confirm.py) is unchanged and covers the original bids.

For each learner the FROZEN development artifacts are read from the directory given in --dev-map
(learner -> dev dir): model_<learner>_s<k>.pt, job_<learner>_s<k>.json (frozen tau per cap and
policy), and for mlp_top2_joint the frozen stage-A model stageA.pt.  Confirmation groups get the
same receiver-local bids by replay (bid2_* / bid3_* next to labels_c*).  Nothing is refitted.
Checks: confirmation seeds disjoint from development seeds; label hashes; oracle >= 0; sources.
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_hetero_mitigation_dev as md
import scripts.MARL_hetero_bid_top2_dev as t2
import scripts.MARL_hetero_bid_request_dev as rq
import scripts.MARL_hetero_top2_joint_dev as tj
from scripts.MARL_hetero_diag_train_v2 import choose, outcome, summarise, anchor
from scripts.MARL_hetero_b2_confirm import boot, DEV_SEEDS

SOURCES = ['scripts/MARL_hetero_b2_confirm_v2.py', 'scripts/MARL_hetero_b2_confirm.py',
           'scripts/MARL_hetero_mitigation_dev.py', 'scripts/MARL_hetero_bid_top2_dev.py',
           'scripts/MARL_hetero_bid_request_dev.py', 'scripts/MARL_hetero_top2_joint_dev.py',
           'research/marl_budget/PROTOCOL_B2_FRESH_BID_20260927.md']
BID = {'bid_prefgap': 10, 'bid_flag': 3, 'bid_queue': 10, 'mlp_top2': 10, 'mlp_top2_joint': 10, 'mlp_bid_request': 10}


def features(g, learner):
    if learner == 'mlp_top2':
        return t2.feats(g, learner)
    if learner == 'mlp_bid_request':
        return rq.patched_features(g, learner)
    if learner == 'mlp_top2_joint':
        ip = g['ev']['ip']
        return (np.concatenate([g['ctx_pub'], g['top2'], g['soft'][ip]]).astype(np.float32),
                np.concatenate([g['soft'], g['masks'].astype(np.float32)], 1))
    return md.features(g, learner)


def main(a):
    run = Path(a.confirm_run); out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    freeze = json.loads(Path(a.freeze).read_text()); devmap = json.loads(Path(a.dev_map).read_text())
    for lab in sorted(x for x in run.glob('labels_*') if x.is_dir()):
        man = json.loads((lab / 'manifest.json').read_text())
        if hashlib.sha256((lab / 'labels.jsonl.gz').read_bytes()).hexdigest() != man['labels_sha256']:
            raise AssertionError(f'{lab}: labels hash mismatch')
    G = md.build(run)
    if any(x.is_dir() for x in run.glob('bid3_*')):
        t2.attach(G, run)
    if any(x.is_dir() for x in run.glob('bid2_*')):
        rq.attach_bids(G, run)
    G = [g for g in G if g['split'] == 'confirm']
    seeds = {g['seed'] for g in G}
    if not G or seeds & DEV_SEEDS:
        raise AssertionError('confirmation seeds empty or overlapping development')
    evs = [g['ev'] for g in G]; eps = [e['ep'] for e in evs]
    learners = sorted(set(devmap))
    if 'mlp_top2_joint' in learners:
        d = Path(devmap['mlp_top2_joint'])
        X0, _, _, _ = tj.a_features(G[0])
        netA = nn.Sequential(nn.Linear(X0.shape[2], 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, 3))
        netA.load_state_dict(torch.load(d / 'stageA.pt', weights_only=False)); netA.eval()
        with torch.no_grad():
            for g in G:
                X, _, p1, p2 = tj.a_features(g)
                pr = torch.softmax(netA(torch.as_tensor(X.reshape(-1, X.shape[2]))), 1).numpy().reshape(g['C'], g['m'], 3)
                g['soft'] = tj.soft_joint(pr, p1, p2)
    res = {}
    for learner in learners:
        d = Path(devmap[learner]); res[learner] = {}
        for seed in (0, 1, 2):
            job = json.loads((d / f'job_{learner}_s{seed}.json').read_text())
            ck = torch.load(d / f'model_{learner}_s{seed}.pt', weights_only=False)
            c0, d0 = features(G[0], learner)
            net = md.Net(len(c0) + d0.shape[1], G[0]['m']); net.load_state_dict(ck['state']); net.eval()
            anch = []
            with torch.no_grad():
                for g in G:
                    c, dd = features(g, learner)
                    x = torch.as_tensor(np.concatenate([np.tile((c - ck['cm']) / ck['cs'], (g['C'], 1)),
                                                        (dd - ck['dm']) / ck['ds']], 1).astype(np.float32))
                    anch.append(anchor(g['ev'], net(x)[0].numpy().astype(float)))
            rs = {}
            for total in md.TOTAL_CAPS:
                key = 'none' if total is None else f'+{total}'
                cx = None if total is None else total - BID.get(learner, 0); row = {}
                for pol in ('repair_R1', 'direct'):
                    t = job['results'][learner][key][pol]['tau']; tau = np.inf if t is None else t
                    o = [outcome(e, choose(e, an, cx, pol == 'repair_R1', tau)) for e, an in zip(evs, anch)]
                    row[pol] = dict(summary=summarise(o), tau=t, gains=[x['gain'] for x in o], chosen=[x['chosen'] for x in o])
                o = [outcome(e, choose(e, e['delta'].astype(float), cx, True, 0.0)) for e in evs]
                if any(x['gain'] < -1e-9 for x in o):
                    raise AssertionError('oracle_R1 gain < 0')
                row['oracle_R1'] = dict(summary=summarise(o), gains=[x['gain'] for x in o])
                rs[key] = row
            res[learner][seed] = rs
            tmp = out / f'.conf_{learner}_s{seed}.json'
            tmp.write_text(json.dumps(dict(learner=learner, seed=seed, results=rs,
                                           anchored=[[round(float(v), 5) for v in an] for an in anch]), default=float))
            os.replace(tmp, out / f'conf_{learner}_s{seed}.json')
            print(f'{learner} s{seed}: ' + ' | '.join(f'{k} R1 {v["repair_R1"]["summary"]["gain"]:+.3f} dir '
                  f'{v["direct"]["summary"]["gain"]:+.3f}' for k, v in rs.items()), flush=True)
    rng = np.random.default_rng(0)
    key = 'none' if freeze['cap'] is None else f'+{freeze["cap"]}'; pol = freeze['policy']
    avg = lambda L: np.mean([res[L][s][key][pol]['gains'] for s in (0, 1, 2)], axis=0)
    gb, gc = avg(freeze['bid']), avg(freeze['control'])
    gq = avg('bid_queue') if 'bid_queue' in res else None
    d = gb - gc
    per_seed = [float(np.mean(res[freeze['bid']][s][key][pol]['gains'])) for s in (0, 1, 2)]
    ci_d, ci_b = boot(d, eps, a.boot, rng), boot(gb, eps, a.boot, rng)
    crit = dict(c1_delta_ci_lower_pos=ci_d[0] > 0, c2_bid_ci_lower_pos=ci_b[0] > 0,
                c3_all_seeds_pos=all(x > 0 for x in per_seed),
                c4_beats_queue=(freeze['bid'] == 'bid_queue') or (gq is not None and float((gb - gq).mean()) > 0))
    verdict = dict(freeze=freeze, delta_mean=float(d.mean()), delta_ci95=ci_d, bid_mean=float(gb.mean()), bid_ci95=ci_b,
                   control_mean=float(gc.mean()), queue_mean=None if gq is None else float(gq.mean()),
                   bid_per_seed=per_seed, oracle_at_bid_cap=float(np.mean(res[freeze['bid']][0][key]['oracle_R1']['gains'])),
                   episodes=len(set(eps)), groups=len(G), **crit, PASS=bool(all(crit.values())))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during confirmation')
    (out / 'verdict.json').write_text(json.dumps(dict(status='COMPLETE', dev_map=devmap, confirm_run=str(run),
        source_hashes=h0, verdict=verdict), indent=1, default=float))
    print(json.dumps(verdict, indent=1, default=float), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dev-map', required=True, help='json: learner -> development dir')
    p.add_argument('--confirm-run', required=True); p.add_argument('--freeze', required=True)
    p.add_argument('--out', required=True); p.add_argument('--boot', type=int, default=10000)
    main(p.parse_args())
