#!/usr/bin/env python3
"""B2 confirmation (research/marl_budget/PROTOCOL_B2_FRESH_BID_20260927.md §4-§6).

Loads the FROZEN development models (model_<learner>_s<seed>.pt) and their frozen tau per
(cap, policy) from the development job files, evaluates them ONCE on the fresh confirmation panel
(split 'confirm', seeds 601-616), and applies the preregistered PASS rule to the frozen design in
--freeze.  Nothing is refitted or re-selected.
Checks (abort): confirmation seeds disjoint from every development seed; labels hash equals the
manifest; oracle R1 gain >= 0; sources unchanged.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_hetero_mitigation_dev import build, features, Net, op_cap, TOTAL_CAPS, BID_BYTES
from scripts.MARL_hetero_diag_train_v2 import choose, outcome, summarise, anchor

SOURCES = ['scripts/MARL_hetero_b2_confirm.py', 'scripts/MARL_hetero_mitigation_dev.py',
           'scripts/MARL_hetero_diag_train_v2.py', 'scripts/MARL_hetero_diag_train.py',
           'research/marl_budget/PROTOCOL_B2_FRESH_BID_20260927.md']
DEV_SEEDS = set(range(301, 365)) | set(range(401, 409)) | set(range(501, 509))


def boot(vals, eps, B, rng):
    E = sorted(set(eps)); idx = {e: np.array([i for i, x in enumerate(eps) if x == e]) for e in E}
    v = np.asarray(vals, float); out = np.empty(B)
    for b in range(B):
        rows = np.concatenate([idx[E[p]] for p in rng.choice(len(E), size=len(E), replace=True)])
        out[b] = v[rows].mean()
    return [float(x) for x in np.quantile(out, [0.025, 0.975])]


def main(a):
    dev = Path(a.dev); run = Path(a.confirm_run); out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    freeze = json.loads(Path(a.freeze).read_text())
    for lab in sorted(run.glob('labels_*')):
        man = json.loads((lab / 'manifest.json').read_text())
        if hashlib.sha256((lab / 'labels.jsonl.gz').read_bytes()).hexdigest() != man['labels_sha256']:
            raise AssertionError(f'{lab}: labels hash mismatch')
    G = [g for g in build(run) if g['split'] == 'confirm']
    seeds = {g['seed'] for g in G}
    if not G or seeds & DEV_SEEDS:
        raise AssertionError(f'confirmation seeds empty or overlapping development: {sorted(seeds & DEV_SEEDS)}')
    evs = [g['ev'] for g in G]; eps = [e['ep'] for e in evs]
    learners = sorted({freeze['bid'], freeze['control'], 'bid_queue', 'ctrl_public', 'ctrl_history'}
                      | set(a.extra))
    res = {}
    for learner in learners:
        res[learner] = {}
        for seed in (0, 1, 2):
            job = json.loads((dev / f'job_{learner}_s{seed}.json').read_text())
            ck = torch.load(dev / f'model_{learner}_s{seed}.pt', weights_only=False)
            c0, d0 = features(G[0], learner)
            net = Net(len(c0) + d0.shape[1], G[0]['m']); net.load_state_dict(ck['state']); net.eval()
            anch = []
            with torch.no_grad():
                for g in G:
                    c, d = features(g, learner)
                    x = torch.as_tensor(np.concatenate([np.tile((c - ck['cm']) / ck['cs'], (g['C'], 1)),
                                                        (d - ck['dm']) / ck['ds']], 1).astype(np.float32))
                    anch.append(anchor(g['ev'], net(x)[0].numpy().astype(float)))
            rs = {}
            for total in TOTAL_CAPS:
                key = 'none' if total is None else f'+{total}'; cx = op_cap(learner, total); row = {}
                for pol in ('repair_R1', 'direct'):
                    t = job['results'][learner][key][pol]['tau']; tau = np.inf if t is None else t
                    o = [outcome(e, choose(e, an, cx, pol == 'repair_R1', tau)) for e, an in zip(evs, anch)]
                    row[pol] = dict(summary=summarise(o), tau=t, gains=[x['gain'] for x in o],
                                    chosen=[x['chosen'] for x in o])
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
            print(f'{learner} s{seed}: +28 R1 {rs["+28"]["repair_R1"]["summary"]["gain"]:+.3f}', flush=True)
    rng = np.random.default_rng(0)
    key = 'none' if freeze['cap'] is None else f'+{freeze["cap"]}'; pol = freeze['policy']
    avg = lambda L: np.mean([res[L][s][key][pol]['gains'] for s in (0, 1, 2)], axis=0)
    gb, gc, gq = avg(freeze['bid']), avg(freeze['control']), avg('bid_queue')
    d = gb - gc
    per_seed = [float(np.mean(res[freeze['bid']][s][key][pol]['gains'])) for s in (0, 1, 2)]
    ci_d, ci_b = boot(d, eps, a.boot, rng), boot(gb, eps, a.boot, rng)
    crit = dict(c1_delta_ci_lower_pos=ci_d[0] > 0, c2_bid_ci_lower_pos=ci_b[0] > 0,
                c3_all_seeds_pos=all(x > 0 for x in per_seed),
                c4_beats_queue=(freeze['bid'] == 'bid_queue') or float((gb - gq).mean()) > 0)
    verdict = dict(freeze=freeze, delta_mean=float(d.mean()), delta_ci95=ci_d, bid_mean=float(gb.mean()),
                   bid_ci95=ci_b, control_mean=float(gc.mean()), queue_mean=float(gq.mean()), bid_per_seed=per_seed,
                   oracle_at_bid_cap=float(np.mean(res[freeze['bid']][0][key]['oracle_R1']['gains'])),
                   oracle_at_control_cap=float(np.mean(res[freeze['control']][0][key]['oracle_R1']['gains'])),
                   episodes=len(set(eps)), groups=len(G), **crit, PASS=bool(all(crit.values())))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during confirmation')
    (out / 'verdict.json').write_text(json.dumps(dict(status='COMPLETE', dev=str(dev), confirm_run=str(run),
        source_hashes=h0, verdict=verdict), indent=1, default=float))
    print(json.dumps(verdict, indent=1, default=float), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dev', required=True); p.add_argument('--confirm-run', required=True)
    p.add_argument('--freeze', required=True); p.add_argument('--out', required=True)
    p.add_argument('--extra', nargs='*', default=['bid_prefgap', 'bid_flag', 'ref_joint'])
    p.add_argument('--boot', type=int, default=10000)
    main(p.parse_args())
