#!/usr/bin/env python3
"""E3 selector on CONTINUATION labels of a frozen learned actor (readiness audit P2.5-P2.6).

Input: label shards from MARL_e3_continuation_labels.py (train / select / dev splits), all made with
the SAME actor checkpoint (checked).  Target: y(S) = cont(S) - cont(P), the declared-continuation
gain of profile S over the prefix P at the same state.
Scheduler inputs (LEGAL only): z (SchedulerContext.features), K/m, the receiver mirror features, the
candidate masks and byte cost; with --bid also the 1-byte receiver bid of the NEW actor: top-2 phases
(p1, p2) and the logit gap quantised into 4 bins by thresholds fixed on the TRAIN split (quartiles);
the bid costs 10 B (9 x 1 B + 1 B header) inside the same total cap.
Model: MLP on [context, candidate] -> gain; anchored score a(S) = pred(S) - pred(P).
Policies: direct (any candidate within the cap) and R1 (radius <= 1 in every receiver).  Epoch and
edit threshold tau are chosen on the SELECT split (never on dev); dev is reported.
Outputs: job_<name>_s<seed>.json (per-state dev gains, chosen index, tau, select metric, oracle best
within the same cap) and model_<name>_s<seed>.pt (weights, normalisers, gap thresholds).
"""
from __future__ import annotations
import argparse, glob, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
SOURCES = ['scripts/MARL_e3_selector_train.py']
BID_BYTES = 10
CAP = 84


def load(dirs):
    S = []
    for d in dirs:
        man = json.loads((Path(d) / 'manifest.json').read_text())
        if man.get('self_check') != 'PASS':
            raise SystemExit(f'{d}: label self-check is not PASS')
        with gzip.open(Path(d) / 'labels.jsonl.gz', 'rt') as f:
            S += [json.loads(l) for l in f]
    return S, {json.loads((Path(d) / 'manifest.json').read_text())['args']['ckpt'] for d in dirs}


def radius(c, P):
    return max(len(set(s) - set(p)) for s, p in zip(c['sets'], P['sets']))


def features(st, bid, gap_thr):
    """Scheduler-side inputs only (no label): shared by training and the closed-loop runner."""
    m = st['m']; P = st['cands'][0]
    ctx = [np.asarray(st['z'], np.float32), np.asarray(st['K'], np.float32) / m, np.asarray(st['mirror'], np.float32)]
    if bid:
        for b in st['bid']:
            gb = int(np.searchsorted(gap_thr, b['gap']))
            ctx += [np.eye(9, dtype=np.float32)[b['p1']], np.eye(9, dtype=np.float32)[b['p2']], np.eye(4, dtype=np.float32)[gb]]
    ctx = np.concatenate(ctx)
    PM = np.zeros((m, m), np.float32)
    for i, s in enumerate(P['sets']):
        PM[i, s] = 1
    D = []
    for c in st['cands']:
        M = np.zeros((m, m), np.float32)
        for i, s in enumerate(c['sets']):
            M[i, s] = 1
        D.append(np.concatenate([M.ravel(), (M - PM).ravel(), [(c['bytes'] - st['b0']) / 100.0]]))
    feas = np.array([c['bytes'] <= st['b0'] + CAP - (BID_BYTES if bid else 0) for c in st['cands']])
    r1 = np.array([radius(c, P) <= 1 for c in st['cands']])
    return ctx, np.stack(D).astype(np.float32), feas, r1


def featurize(st, bid, gap_thr):
    ctx, D, feas, r1 = features(st, bid, gap_thr)
    y = np.array([c['cont'] for c in st['cands']], np.float32) - st['cands'][0]['cont']
    return ctx, D, y, feas, r1


class Net(nn.Module):
    def __init__(self, dc, dd, h=128):
        super().__init__()
        self.c = nn.Sequential(nn.Linear(dc, h), nn.ReLU()); self.d = nn.Sequential(nn.Linear(dd, h), nn.ReLU())
        self.o = nn.Sequential(nn.Linear(2 * h, h), nn.ReLU(), nn.Linear(h, 1))

    def forward(self, c, d):
        return self.o(torch.cat([self.c(c).expand(d.shape[0], -1), self.d(d)], 1)).squeeze(-1)


def choose(a, feas, allow, tau):
    ok = feas & allow; ok[0] = True
    s = np.where(ok, a, -np.inf); j = int(np.argmax(s))
    return j if s[j] > tau else 0


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    data, ck = {}, set()
    for sp, dirs in (('train', a.train), ('select', a.select), ('dev', a.dev)):
        data[sp], c = load([x for d in dirs for x in sorted(glob.glob(d)) if Path(x).is_dir()]); ck |= c   # dirs only: the glob also matches *.log
    if len(ck) != 1:
        raise SystemExit(f'labels come from different actor checkpoints: {ck}')
    gap_thr = np.quantile([b['gap'] for st in data['train'] for b in st['bid']], [0.25, 0.5, 0.75]).tolist()
    F = {sp: [featurize(st, a.bid, gap_thr) for st in data[sp]] for sp in data}
    C = np.stack([f[0] for f in F['train']]); cm, cs = C.mean(0), C.std(0) + 1e-6
    ys = float(np.std(np.concatenate([f[2] for f in F['train']])) + 1e-6)
    torch.manual_seed(a.seed); rng = np.random.default_rng(a.seed); torch.set_num_threads(a.threads)
    net = Net(C.shape[1], F['train'][0][1].shape[1], a.hidden); opt = torch.optim.Adam(net.parameters(), lr=a.lr, weight_decay=1e-5)

    def T(f):
        return torch.as_tensor((f[0] - cm) / cs)[None], torch.as_tensor(f[1])

    def anchored(sp):
        out_ = []
        with torch.no_grad():
            for f in F[sp]:
                p = net(*T(f)).numpy() * ys; out_.append(p - p[0])
        return out_

    def evaluate(sp, pol, tau):
        return [float(f[2][choose(an, f[3], f[4] if pol == 'R1' else np.ones_like(f[4]), tau)]) for f, an in zip(F[sp], anchored(sp))]

    def pick_tau(pol):
        an = anchored('select'); grid = [-np.inf, 0.0] + sorted({float(x) for v in an for x in np.quantile(v[1:], [0.9, 0.99])})
        scores = [(np.mean([float(f[2][choose(v, f[3], f[4] if pol == 'R1' else np.ones_like(f[4]), t)]) for f, v in zip(F['select'], an)]), t) for t in grid]
        best = max(scores, key=lambda x: x[0]); return best[1], best[0]

    best, saved, best_ep = -np.inf, None, None; t0 = time.perf_counter()
    for ep in range(a.epochs):
        for k in rng.permutation(len(F['train'])):
            c, d = T(F['train'][k]); y = torch.as_tensor(F['train'][k][2] / ys)
            loss = ((net(c, d) - y) ** 2).mean(); opt.zero_grad(); loss.backward(); opt.step()
        if ep % 4 == 3 or ep == a.epochs - 1:
            tau, metric = pick_tau('direct')
            if metric > best:
                best, saved, best_ep = metric, {k: v.clone() for k, v in net.state_dict().items()}, ep
            print(f'[{time.perf_counter() - t0:.0f}s] {a.name} s{a.seed} ep {ep}: select direct {metric:+.2f}', flush=True)
    net.load_state_dict(saved); res = {}
    for pol in ('direct', 'R1'):
        tau, sel = pick_tau(pol); g = evaluate('dev', pol, tau)
        orc = [float(np.max(np.where(f[3] & (f[4] if pol == 'R1' else True), f[2], -np.inf))) for f in F['dev']]
        res[pol] = dict(tau=None if np.isinf(tau) else tau, select_metric=sel, dev_gain_mean=float(np.mean(g)), dev_gains=g,
                        dev_oracle_mean=float(np.mean(orc)), dev_oracle=orc, eps=[st['episode_id'] for st in data['dev']],
                        edit_rate=float(np.mean([x != 0 for x in g])))
    blob = dict(name=a.name, seed=a.seed, bid=a.bid, best_epoch=best_ep, select_metric=best, gap_thresholds=gap_thr, actor_ckpt=ck.pop(),
                n_states={sp: len(F[sp]) for sp in F}, results=res, source_hashes=h0)
    (out / f'job_{a.name}_s{a.seed}.json').write_text(json.dumps(blob))
    torch.save(dict(state=saved, cm=cm, cs=cs, ys=ys, gap_thr=gap_thr, bid=a.bid, hidden=a.hidden, dims=(C.shape[1], F['train'][0][1].shape[1]),
                    tau={p: res[p]['tau'] for p in res}), out / f'model_{a.name}_s{a.seed}.pt')
    print(f'{a.name} s{a.seed}: dev direct {res["direct"]["dev_gain_mean"]:+.2f} (oracle {res["direct"]["dev_oracle_mean"]:+.2f}), '
          f'R1 {res["R1"]["dev_gain_mean"]:+.2f} (oracle {res["R1"]["dev_oracle_mean"]:+.2f})', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--train', nargs='+', required=True); p.add_argument('--select', nargs='+', required=True); p.add_argument('--dev', nargs='+', required=True)
    p.add_argument('--out', required=True); p.add_argument('--name', required=True); p.add_argument('--bid', action='store_true')
    p.add_argument('--seed', type=int, default=0); p.add_argument('--epochs', type=int, default=40); p.add_argument('--lr', type=float, default=1e-3)
    p.add_argument('--hidden', type=int, default=128); p.add_argument('--threads', type=int, default=2)
    main(p.parse_args())
