#!/usr/bin/env python3
"""Mitigation DEVELOPMENT screen on the existing B1 artifacts (no new traffic, no actor training).

Data: B1 run b1_lc_20260927_201443 (labels + mirror + response replays).  Fit on the train pool
(301-364), select epoch and no-edit threshold on 401-408, and report 501-508 as DEVELOPMENT only:
the B1 test panel has been opened, so nothing here is confirmatory.  A design chosen here must be
confirmed on a fresh preregistered panel.

One trainer for every learner (controls included), so differences are not trainer artifacts:
MLP 2x128, Adam 1e-3, wd 1e-4, batch 512, 40 epochs, epoch chosen on the select split by the
operating-point metric; anchoring, prefix tie rule, tau grid with never-edit, candidate-set argmax
and outcome/summary definitions are IMPORTED from MARL_hetero_diag_train_v2.py.

Learners (information class in brackets; PRIV never enters a deployable input):
  ctrl_public       [legal]  z, K, candidate mask                       (B1 control, retrained)
  ctrl_history      [legal]  + receiver mirror                          (B1 control, retrained)
  aux_public/history[legal]  + auxiliary head predicting per-receiver ACTION CHANGE, trained on
                             the privileged counterfactual labels; inference uses legal inputs only
  cls_history       [legal]  decision-focused loss: BCE on 1[gain > 0]
  struct_legal      [legal]  + frozen-MP2 predicted joint action from scheduler-known data
                             (MARL_hetero_response_replay.py)
  bid_prefgap       [bid 10B] + receiver-local preferred action and quantised score gap
                             (1 B/receiver + 1 B header), charged against the SAME total cap
  bid_flag          [bid 3B]  + 1 bit/receiver "fragile" (local gap <= 1.0) + 1 B header
  bid_queue         [bid 10B] + receiver-local total waiting, 1 B/receiver + 1 B header
  ref_joint         [PRIV]   true counterfactual joint actions (the B1 reference, retrained)
Decision variants (no retraining): *_gate restricts edits to candidates whose predicted change
(aux head >= 0.5, or struct prediction) is positive for some edited receiver.
Every job writes model state, anchored predictions and chosen indices atomically.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_hetero_diag_train import load, pmat
from scripts.MARL_hetero_diag_train_v2 import choose, outcome, summarise, anchor, TOL

SOURCES = ['scripts/MARL_hetero_mitigation_dev.py', 'scripts/MARL_hetero_diag_train_v2.py',
           'scripts/MARL_hetero_diag_train.py', 'models/marl_hetero_selector.py',
           'scripts/MARL_hetero_response_replay.py']
POOL = set(range(301, 365))
BID_BYTES = {'bid_prefgap': 10, 'bid_flag': 3, 'bid_queue': 10}
TOTAL_CAPS = [28, 56, 84, None]
FRAGILE = 1.0


def onehot8(a):
    v = np.zeros(8, np.float32); v[int(a) % 8] = 1; return v


def build(run):
    """Compact arrays: per-group context blocks, per-candidate features and evaluation dicts."""
    G = []
    for lab in sorted(run.glob('labels_*')):
        sfx = lab.name[len('labels_'):]
        mir, rsp = run / f'mirror_{sfx}', run / f'response_{sfx}'
        groups = load(lab, mir)
        recs = [json.loads(l) for l in gzip.open(lab / 'labels.jsonl.gz', 'rt')]
        R = {(r['episode_id'], r['t']): r for r in (json.loads(l) for l in gzip.open(rsp / 'response_diag.jsonl.gz', 'rt'))}
        k = 0
        for r in recs:
            rr = R[(r['episode_id'], r['t'])]
            for gi in range(len(r['groups'])):
                g = groups[k]; k += 1
                if g['ep'] != r['episode_id']:
                    raise AssertionError('group order mismatch')
                m = g['m']; C = len(g['profs'])
                masks = np.stack([pmat(p, m).reshape(-1) for p in g['profs']]).astype(np.uint8)
                edited = np.array([[g['profs'][c][i] != g['P'][i] for i in range(m)] for c in range(C)], bool)
                tj = np.array(g['joint'], np.int16); pj = np.array(rr['pjoint'][gi], np.int16)
                bid = rr['bid']
                G.append(dict(ep=g['ep'], seed=g['seed'], split=g['split'], m=m, C=C,
                              ctx_pub=np.asarray(list(g['z']) + [x / m for x in g['K']], np.float32),
                              mirror=np.asarray(g['mirror'], np.float32),
                              bid_prefgap=np.concatenate([np.concatenate([onehot8(b['pref']) for b in bid]),
                                                          np.asarray([min(31, round(b['gap'] * 2)) / 31 for b in bid], np.float32)]),
                              bid_flag=np.asarray([float(b['gap'] <= FRAGILE) for b in bid], np.float32),
                              bid_queue=np.asarray([min(255, round(sum(b['own']))) / 255 for b in bid], np.float32),
                              masks=masks, edited=edited, tj=tj, pj=pj,
                              ch_true=(tj != tj[g['ip']][None, :]), ch_pred=(pj != pj[g['ip']][None, :]),
                              ev=dict(ep=g['ep'], cost=g['cost'], b0=g['b0'], r1=g['r1'], ip=g['ip'],
                                      delta=g['delta'], joint=[tuple(x) for x in g['joint']], joint_P=tuple(g['joint_P']))))
        del groups
    return G


def features(g, learner):
    m = g['m']; C = g['C']
    ctx = [g['ctx_pub']]
    if learner in ('ctrl_history', 'aux_history', 'cls_history'):
        ctx.append(g['mirror'])
    if learner in BID_BYTES:
        ctx.append(g[learner])
    if learner == 'struct_legal':
        ctx.append(np.concatenate([onehot8(a) for a in g['pj'][g['ev']['ip']]]))
    ctx = np.concatenate(ctx).astype(np.float32)
    if learner == 'ref_joint':
        ctx = np.concatenate([ctx, np.concatenate([onehot8(a) for a in g['tj'][g['ev']['ip']]])])
        cand = np.stack([np.concatenate([onehot8(a) for a in g['tj'][c]]) for c in range(C)])
    elif learner == 'struct_legal':
        cand = np.concatenate([g['masks'].astype(np.float32),
                               np.stack([np.concatenate([onehot8(a) for a in g['pj'][c]]) for c in range(C)]),
                               g['ch_pred'].astype(np.float32)], 1)
    else:
        cand = g['masks'].astype(np.float32)
    return ctx, cand


class Net(nn.Module):
    def __init__(self, d, m, hidden=128):
        super().__init__()
        self.trunk = nn.Sequential(nn.Linear(d, hidden), nn.ReLU(), nn.Linear(hidden, hidden), nn.ReLU())
        self.gain = nn.Linear(hidden, 1); self.change = nn.Linear(hidden, m)

    def forward(self, x):
        h = self.trunk(x)
        return self.gain(h).squeeze(-1), self.change(h)


def select_tau(evs, anch, restrict, cap_extra):
    pos = np.concatenate([a[a > 0] for a in anch]) if anch else np.array([])
    grid = [0.0] + (list(np.quantile(pos, [0.1, 0.25, 0.5, 0.75, 0.9])) if len(pos) else []) + [np.inf]
    best_t, best_v = None, -np.inf
    for t in grid:
        v = np.mean([outcome(e, choose(e, a, cap_extra, restrict, t))['gain'] for e, a in zip(evs, anch)])
        if v > best_v + 1e-12:
            best_t, best_v = t, v
    return best_t, best_v


def op_cap(learner, total):
    return None if total is None else total - BID_BYTES.get(learner, 0)


def gated(anch, g, prob):
    """Edits allowed only where some edited receiver is predicted to change action."""
    a = anch.copy()
    ok = (g['edited'] & prob).any(1)
    a[~ok] = np.minimum(a[~ok], 0.0)
    return a


def run_job(G, learner, seed, out, epochs, threads):
    torch.manual_seed(seed); torch.set_num_threads(threads); rng = np.random.default_rng(seed)
    fit = [g for g in G if g['split'] == 'train' and g['seed'] in POOL]
    sel = [g for g in G if g['split'] == 'select']; dev = [g for g in G if g['split'] == 'test']
    F = {id(g): features(g, learner) for g in fit + sel + dev}
    CX = np.stack([F[id(g)][0] for g in fit]); cand = np.concatenate([F[id(g)][1] for g in fit])
    gidx = np.concatenate([np.full(g['C'], k) for k, g in enumerate(fit)])
    Y = np.concatenate([g['ev']['delta'] for g in fit]).astype(np.float32)
    E = np.concatenate([g['edited'] for g in fit]); CH = np.concatenate([g['ch_true'] for g in fit])
    cm, cs = CX.mean(0), CX.std(0); cs[cs < 1e-6] = 1
    dm, ds = cand.mean(0), cand.std(0); ds[ds < 1e-6] = 1
    scale = max(float(Y.std()), 1e-6)
    CXn = torch.as_tensor((CX - cm) / cs); candn = torch.as_tensor((cand - dm) / ds)
    Yt = torch.as_tensor(Y / scale); Et = torch.as_tensor(E); CHt = torch.as_tensor(CH.astype(np.float32))
    gidt = torch.as_tensor(gidx)
    net = Net(CX.shape[1] + cand.shape[1], G[0]['m'])
    opt = torch.optim.Adam(net.parameters(), lr=1e-3, weight_decay=1e-4)
    aux = learner.startswith('aux'); cls = learner == 'cls_history'
    Ypos = torch.as_tensor((Y > 0).astype(np.float32))

    def predict(gs):
        outs, probs = [], []
        with torch.no_grad():
            for g in gs:
                c, d = F[id(g)]
                x = torch.as_tensor(np.concatenate([np.tile((c - cm) / cs, (g['C'], 1)), (d - dm) / ds], 1).astype(np.float32))
                a, b = net(x); outs.append(a.numpy().astype(float)); probs.append(torch.sigmoid(b).numpy() >= 0.5)
        return outs, probs

    best, saved, best_ep = -np.inf, None, None
    cap_sel = op_cap(learner, 28)
    for ep in range(epochs):
        for b in np.array_split(rng.permutation(len(Y)), max(1, len(Y) // 512)):
            bt = torch.as_tensor(b)
            x = torch.cat([CXn[gidt[bt]], candn[bt]], 1)
            pg, pc = net(x)
            loss = (nn.functional.binary_cross_entropy_with_logits(pg, Ypos[bt]) if cls
                    else ((pg - Yt[bt]) ** 2).mean())
            if aux:
                w = Et[bt].float()
                if w.sum() > 0:
                    bce = nn.functional.binary_cross_entropy_with_logits(pc, CHt[bt], reduction='none')
                    loss = loss + (bce * w).sum() / w.sum()
            opt.zero_grad(); loss.backward(); opt.step()
        if ep % 4 == 3 or ep == epochs - 1:
            ps, _ = predict(sel)
            metric = select_tau([g['ev'] for g in sel], [anchor(g['ev'], p) for g, p in zip(sel, ps)], True, cap_sel)[1]
            if metric > best + 1e-12:
                best, saved, best_ep = metric, {k: v.clone() for k, v in net.state_dict().items()}, ep
    net.load_state_dict(saved)
    ps, pp = predict(sel); pd, pdp = predict(dev)
    variants = {learner: (lambda gs, p, q: [anchor(g['ev'], x) for g, x in zip(gs, p)])}
    if aux:
        variants[learner + '_gate'] = lambda gs, p, q: [gated(anchor(g['ev'], x), g, y) for g, x, y in zip(gs, p, q)]
    if learner == 'struct_legal':
        variants[learner + '_gate'] = lambda gs, p, q: [gated(anchor(g['ev'], x), g, g['ch_pred']) for g, x in zip(gs, p)]
    res = {}
    dev_eval = [g['ev'] for g in dev]; sel_eval = [g['ev'] for g in sel]
    for name, fn in variants.items():
        sa, da = fn(sel, ps, pp), fn(dev, pd, pdp)
        res[name] = {}
        for total in TOTAL_CAPS:
            cx = op_cap(learner, total); key = 'none' if total is None else f'+{total}'
            row = {}
            for pol in ('repair_R1', 'direct'):
                tau = select_tau(sel_eval, sa, pol == 'repair_R1', cx)[0]
                o = [outcome(e, choose(e, a, cx, pol == 'repair_R1', tau)) for e, a in zip(dev_eval, da)]
                row[pol] = dict(summary=summarise(o), tau=None if np.isinf(tau) else float(tau),
                                gains=[x['gain'] for x in o], eps=[x['ep'] for x in o], chosen=[x['chosen'] for x in o])
            o = [outcome(e, choose(e, e['delta'].astype(float), cx, True, 0.0)) for e in dev_eval]
            row['oracle_R1'] = dict(summary=summarise(o), gains=[x['gain'] for x in o])
            res[name][key] = row
    blob = dict(learner=learner, seed=seed, best_epoch=best_ep, select_metric=best, results=res,
                change_acc=None)
    if aux:
        yt = np.concatenate([g['ch_true'][g['edited']] for g in dev]); yp = np.concatenate([q[g['edited']] for g, q in zip(dev, pdp)])
        blob['change_acc'] = dict(base_rate=float(yt.mean()), precision=float((yt & yp).sum() / max(yp.sum(), 1)),
                                  recall=float((yt & yp).sum() / max(yt.sum(), 1)))
    tmp = out / f'.{learner}_s{seed}.json'
    tmp.write_text(json.dumps(blob, default=float)); os.replace(tmp, out / f'job_{learner}_s{seed}.json')
    torch.save(dict(state=saved, cm=cm, cs=cs, dm=dm, ds=ds, scale=scale), out / f'model_{learner}_s{seed}.pt')
    return blob


def main(a):
    run = Path(a.run); out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    (out / 'manifest.json').write_text(json.dumps(dict(status='RUNNING', run=str(run), source_hashes=h0,
                                                       learners=a.learners, seeds=a.seeds, epochs=a.epochs), indent=1))
    t0 = time.perf_counter()
    G = build(run)
    splits = {s: {g['seed'] for g in G if g['split'] == s} for s in ('train', 'select', 'test')}
    if splits['train'] & splits['select'] or splits['train'] & splits['test'] or splits['select'] & splits['test']:
        raise AssertionError('splits share seeds')
    print(f'[{time.perf_counter() - t0:.0f}s] built {len(G)} groups', flush=True)
    for learner in a.learners:
        for seed in a.seeds:
            b = run_job(G, learner, seed, out, a.epochs, a.threads)
            r = b['results'][learner]['+28']
            print(f'[{time.perf_counter() - t0:.0f}s] {learner} s{seed}: ep {b["best_epoch"]} sel {b["select_metric"]:+.3f} | '
                  f'dev +28 R1 {r["repair_R1"]["summary"]["gain"]:+.3f} direct {r["direct"]["summary"]["gain"]:+.3f} '
                  f'oracle {r["oracle_R1"]["summary"]["gain"]:+.3f}', flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', run=str(run), source_hashes=h0,
        learners=a.learners, seeds=a.seeds, epochs=a.epochs, seconds=time.perf_counter() - t0,
        evidence_class='DEVELOPMENT screen on opened B1 data; not confirmatory'), indent=1))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', required=True); p.add_argument('--out', required=True)
    p.add_argument('--learners', nargs='+', default=['ctrl_public', 'ctrl_history', 'aux_public', 'aux_history',
                   'cls_history', 'struct_legal', 'bid_prefgap', 'bid_flag', 'bid_queue', 'ref_joint'])
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--epochs', type=int, default=40)
    p.add_argument('--threads', type=int, default=4)
    main(p.parse_args())
