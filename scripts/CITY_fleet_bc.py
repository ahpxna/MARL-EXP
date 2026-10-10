#!/usr/bin/env python3
"""B6-I, PREPARED (04/10/2026 wake 4; audit Addendum B6 item 6 "distillation / residual from SUMO"): behaviour-clone SUMO's default
driver model into the fleet's discrete action set, to separate "the class cannot represent the baseline" from "RL does not find it".
Data: always-SUMO runs (every agent released to SUMO) under ACT on TRAINING demand seeds 0-7; for each agent decision state in the
approach zone, the fleet observation o_t (the same 6 features CarRL builds) and SUMO's realized acceleration a_t = v_{t+1} - v_t, mapped
to the nearest action of the chosen set (acc: -3..+2; fine: -1.5..+1).  A classifier with the Q7 DQN architecture (6-64-64-n) is fit by
cross-entropy; its argmax is the fleet policy, saved in the trainer checkpoint format (`actions` field), so CITY_eval4 evaluates it and
CITY_fleet_train_v6 --init can fine-tune it by RL.  The discretization error is reported (mean |a_t - nearest action|)."""
from __future__ import annotations
import argparse, hashlib, json, os, sys
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import run_episode, ACC, ZONE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
from scripts.CITY_env import CarRL  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); SETS = {'acc': ACC, 'fine': np.array([-1.5, -1.0, -0.5, 0.0, 0.5, 1.0])}


def collect(seeds, end):
    X, A = [], []
    for seed in seeds:
        car = CarRL(None, Q7.RHO, seed); prev = {}

        class Log:
            def step(self, t):
                ls = CE.ls; cur = {}
                for v in ls.vehicle.getIDList():
                    if not car.is_agent(v):
                        continue
                    try:
                        nt = ls.vehicle.getNextTLS(v)
                        if not nt or nt[0][2] > ZONE:
                            continue
                        tid, _li, dist, st = nt[0]; sp = ls.vehicle.getSpeed(v); lead = ls.vehicle.getLeader(v, 100.0)
                    except Exception:
                        continue
                    if not (0 <= sp < 100):
                        continue                                    # teleport sentinel (city ledger C-22)
                    gap = (lead[1] / 100.0) if lead else 1.0
                    cur[v] = (np.array([dist / ZONE, sp / 14.0, st in 'Gg', st in 'yY', ls.trafficlight.getSpentDuration(tid) / 60.0, gap], np.float32), sp)
                for v, (o, sp) in prev.items():
                    if v in cur:
                        X.append(o); A.append(cur[v][1] - sp)
                prev.clear(); prev.update(cur)
        run_episode(Q7.NET_A, Q7.ROU.format(seed), seed, None, Log(), end=end)
    return np.stack(X), np.array(A)


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.manual_seed(a.seed); torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}_fleet.pt'
    X, Acc = collect(list(range(8)), 300 if a.smoke else 3600); S = SETS[a.actions]
    y = np.abs(Acc[:, None] - S[None, :]).argmin(1); err = float(np.mean(np.abs(Acc - S[y])))
    net = nn.Sequential(nn.Linear(6, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, len(S)))
    opt = torch.optim.Adam(net.parameters(), 1e-3); Xt = torch.as_tensor(X); yt = torch.as_tensor(y); rng = np.random.default_rng(a.seed)
    for ep in range(2 if a.smoke else a.epochs):
        idx = rng.permutation(len(X))
        for k in range(0, len(idx), 1024):
            j = idx[k:k + 1024]; loss = nn.functional.cross_entropy(net(Xt[j]), yt[j]); opt.zero_grad(); loss.backward(); opt.step()
    with torch.no_grad():
        acc_train = float((net(Xt).argmax(1) == yt).float().mean())
    net.eval()
    torch.save(dict(net=net, kind='fleet', actions=a.actions if a.actions != 'acc' else 'acc', tmax=[1e9, 1e9], name=a.name, against='ACT', reward='bc',
                    samples=int(len(X)), label_hist=np.bincount(y, minlength=len(S)).tolist(), discretization_mae=err, train_accuracy=acc_train,
                    source_sha256=SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fn)
    print(json.dumps(dict(name=a.name, samples=int(len(X)), label_hist=np.bincount(y, minlength=len(S)).tolist(), discretization_mae=round(err, 3), train_accuracy=round(acc_train, 3))), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actions', default='fine', choices=['acc', 'fine']); p.add_argument('--epochs', type=int, default=20); p.add_argument('--seed', type=int, default=0)
    p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
