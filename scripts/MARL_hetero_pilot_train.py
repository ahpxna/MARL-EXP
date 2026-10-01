#!/usr/bin/env python3
"""Step 3 pilot: train the heterogeneous-profile critic f_hat(z, K, S) on the pilot labels.

ONE critic per (feature variant, seed) is shared by learned R1 repair and the direct
budget-aware search, so both have the same information, labels and evaluator.
  public      : z = paid scheduler cache + time (deployable)
  privileged  : z + ORACLE current summaries (diagnostic only, never deployable)
Target: value centred within its (context, K) group, scaled by the train std of those centred
values.  Checkpoint: every 10 epochs, validation decision regret of the critic's argmax over
the labelled candidates (all, and R<=1-legal), averaged; lowest wins.  Test data is not read.
"""
from __future__ import annotations
import argparse, copy, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_hetero_selector import HeteroCritic, critic_input, prefix_sets

SOURCES = ['scripts/MARL_hetero_pilot_train.py', 'models/marl_hetero_selector.py']


def unmask(masks):
    return [frozenset(j for j in range(16) if (x >> j) & 1) for x in masks]


def build(rows, variant):
    X, Y, G, R1 = [], [], [], []
    gid = 0
    for r in rows:
        z = list(r['z']) + (list(r['privileged']) if variant == 'privileged' else [])
        order, m = r['order'], r['m']
        for g in r['groups']:
            K = g['K']; P = prefix_sets(order, K)
            vals = np.asarray(g['values'], dtype=float); c = vals - vals.mean()
            for masks, y in zip(g['profiles'], c):
                s = unmask(masks)
                X.append(critic_input(z, K, s, m)); Y.append(y); G.append(gid)
                R1.append(all(len(s[i] - P[i]) <= 1 for i in range(m)))
            gid += 1
    return np.asarray(X, np.float32), np.asarray(Y, np.float32), np.asarray(G), np.asarray(R1)


def decision_regret(pred, Y, G, R1):
    out_all, out_r1 = [], []
    for g in np.unique(G):
        ix = np.nonzero(G == g)[0]
        out_all.append(Y[ix].max() - Y[ix][np.argmax(pred[ix])])
        jx = ix[R1[ix]]
        out_r1.append(Y[jx].max() - Y[jx][np.argmax(pred[jx])])
    return float(np.mean(out_all)), float(np.mean(out_r1))


def main(a):
    torch.set_num_threads(1)
    folder = Path(a.labels)
    man = json.loads((folder / 'manifest.json').read_text())
    if man.get('status') != 'COMPLETE':
        raise ValueError('labels not COMPLETE')
    if hashlib.sha256((folder / 'labels.jsonl.gz').read_bytes()).hexdigest() != man['labels_sha256']:
        raise ValueError('labels hash mismatch')
    rows = [json.loads(l) for l in gzip.open(folder / 'labels.jsonl.gz', 'rt')]
    tr = [r for r in rows if r['split'] == 'train']; va = [r for r in rows if r['split'] == 'val']
    if {r['traffic_seed'] for r in tr} & {r['traffic_seed'] for r in va}:
        raise ValueError('seed overlap between train and val')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    report = dict(status='RUNNING', labels=str(folder.resolve()), labels_sha256=man['labels_sha256'],
                  source_hashes=hashes, n_train_contexts=len(tr), n_val_contexts=len(va), runs=[])
    t0 = time.perf_counter()
    for variant in a.variants:
        Xtr, Ytr, Gtr, R1tr = build(tr, variant); Xva, Yva, Gva, R1va = build(va, variant)
        mean = Xtr.mean(0); std = Xtr.std(0); std[std < 1e-6] = 1.0
        scale = max(float(Ytr.std()), 1e-6)
        xt = torch.as_tensor((Xtr - mean) / std); yt = torch.as_tensor(Ytr / scale)
        xv = torch.as_tensor((Xva - mean) / std)
        for seed in a.seeds:
            critic = HeteroCritic(Xtr.shape[1], hidden=a.hidden, seed=seed)
            opt = torch.optim.Adam(critic.net.parameters(), lr=a.lr, weight_decay=a.wd)
            rng = np.random.default_rng(seed); best, saved, hist = float('inf'), None, []
            for ep in range(a.epochs):
                perm = rng.permutation(len(Ytr))
                for b in np.array_split(perm, max(1, len(perm) // a.batch)):
                    loss = ((critic.net(xt[b]).squeeze(-1) - yt[b]) ** 2).mean()
                    opt.zero_grad(); loss.backward(); opt.step()
                if ep % 10 == 0 or ep == a.epochs - 1:
                    with torch.no_grad():
                        pv = critic.net(xv).squeeze(-1).numpy() * scale
                        ptr = critic.net(xt).squeeze(-1).numpy() * scale
                    ra, r1 = decision_regret(pv, Yva, Gva, R1va)
                    ta, t1 = decision_regret(ptr, Ytr, Gtr, R1tr)
                    metric = 0.5 * (ra + r1)
                    hist.append(dict(epoch=ep, val_regret_all=ra, val_regret_R1=r1, train_regret_all=ta,
                                     train_regret_R1=t1, val_mse=float(((pv - Yva) ** 2).mean())))
                    if metric < best:
                        best, saved = metric, copy.deepcopy(critic.net.state_dict())
            critic.net.load_state_dict(saved)
            path = out / f'critic_{variant}_seed{seed}.pt'
            torch.save(dict(state=saved, mean=mean, std=std, scale=scale, d_in=Xtr.shape[1],
                            hidden=a.hidden, variant=variant, seed=seed), path)
            bh = min(hist, key=lambda h: 0.5 * (h['val_regret_all'] + h['val_regret_R1']))
            report['runs'].append(dict(variant=variant, seed=seed, checkpoint=str(path), selected=bh,
                                       history=hist))
            print(f'[{time.perf_counter() - t0:.0f}s] {variant} seed {seed}: selected epoch {bh["epoch"]} '
                  f'val regret all {bh["val_regret_all"]:.2f} R1 {bh["val_regret_R1"]:.2f} | '
                  f'train all {bh["train_regret_all"]:.2f} R1 {bh["train_regret_R1"]:.2f}', flush=True)
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during training')
    report.update(status='COMPLETE', seconds=time.perf_counter() - t0,
                  config=dict(epochs=a.epochs, hidden=a.hidden, lr=a.lr, wd=a.wd, batch=a.batch, seeds=a.seeds))
    (out / 'report.json').write_text(json.dumps(report, indent=1, default=float))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--labels', required=True); p.add_argument('--out', required=True)
    p.add_argument('--variants', nargs='+', default=['public', 'privileged'])
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--epochs', type=int, default=200); p.add_argument('--hidden', type=int, default=128)
    p.add_argument('--lr', type=float, default=1e-3); p.add_argument('--wd', type=float, default=1e-4)
    p.add_argument('--batch', type=int, default=256)
    main(p.parse_args())
