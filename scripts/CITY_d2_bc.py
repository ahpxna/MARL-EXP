#!/usr/bin/env python3
"""D2 learnability check, stages 1-2 (user guidance TWO_POPULATION_CAUSAL_DIAGNOSIS §3 D2; 04/10/2026).  Positive control = the simple
heuristic GLOSA, FEASIBLE on TRAIN traffic under FT (C-39) and preferred by reward B.
  collect  run GLOSA under FT on traffic SEEDS (3600 s); for every agent-second in the 200 m zone record the v8 observation (SPaT on, and
           the same with SPaT inputs zeroed) at t and the REALISED acceleration a = v(t+1) - v(t), clipped to [LO, HI] (this label covers
           GLOSA-commanded and released seconds, so a policy that commands setSpeed(v + a) can in principle reproduce the trajectory)
  fit      behaviour-clone the v8 actor mean on u = atanh(2 (a - LO) / (HI - LO) - 1) (clipped to |.| <= 0.999), MSE, Adam 1e-3, 20 epochs,
           batch 4096; train on seeds 0-5, validate on 6-7; report the action MAE (m/s^2) for the SPaT and the no-SPaT input variants
           and save fleet files (deterministic evaluation via CITY_eval6 P:).  Debug evidence, not a paper result.
Usage: CITY_d2_bc.py collect OUT_DIR SEED... | CITY_d2_bc.py fit OUT_DIR"""
import json, os, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402


class Rec(V8.CarGLOSA):
    def __init__(self, rho, seed):
        super().__init__(rho, seed); self.pend = {}; self.X = []; self.Y = []; self.st = dict(spat_valid=0, spat_n=0)

    def step(self, t):
        ls = CE.ls
        for v, (o, sp0) in list(self.pend.items()):              # label the previous second with the realised acceleration
            try:
                sp1 = ls.vehicle.getSpeed(v)
            except Exception:
                sp1 = None
            if sp1 is not None and V8.ok(sp1):
                self.X.append(o); self.Y.append(float(np.clip(sp1 - sp0, V8.LO, V8.HI)))
        self.pend = {}
        for v in list(self.agents):
            try:
                nt = ls.vehicle.getNextTLS(v); sp = ls.vehicle.getSpeed(v); vl = ls.vehicle.getAllowedSpeed(v)
                if nt and nt[0][2] <= V8.ZONE and V8.ok(sp) and V8.ok(vl) and vl > 0 and ls.vehicle.getLaneID(v):
                    self.pend[v] = (V8.build_obs(ls, v, nt[0], sp, vl, True, self.st), sp)
            except Exception:
                continue
        super().step(t)


def collect(out, seeds):
    out.mkdir(parents=True, exist_ok=True)
    for s in seeds:
        r = Rec(Q7.RHO, s); m = CE.run_episode(Q7.NET_S, Q7.ROU.format(s), s, None, r, end=3600)
        np.savez_compressed(out / f'glosa_s{s}.npz', X=np.array(r.X, np.float32), Y=np.array(r.Y, np.float32))
        print(f'seed {s}: {len(r.Y)} labelled agent-seconds; teleports {m["teleports"]}; mean |a| {np.mean(np.abs(r.Y)):.3f}', flush=True)


def to_u(a):
    z = np.clip(2 * (a - V8.LO) / (V8.HI - V8.LO) - 1, -0.999, 0.999); return np.arctanh(z).astype(np.float32)


def fit(out):
    torch.set_num_threads(1); res = {}
    load = lambda ss: [np.load(out / f'glosa_s{s}.npz') for s in ss]
    tr, va = load(range(6)), load([6, 7])
    for arm in ('on', 'off'):
        Xt = np.concatenate([d['X'] for d in tr]); Yt = np.concatenate([d['Y'] for d in tr]); Xv = np.concatenate([d['X'] for d in va]); Yv = np.concatenate([d['Y'] for d in va])
        if arm == 'off':
            Xt = Xt.copy(); Xv = Xv.copy(); Xt[:, 10:13] = 0; Xv[:, 10:13] = 0
        net = V8.Net(13); opt = torch.optim.Adam(net.pi.parameters(), lr=1e-3); At = torch.as_tensor(Yt); XT = torch.as_tensor(Xt)
        rng = np.random.default_rng(0); sq = lambda u: V8.LO + (torch.tanh(u) + 1.0) * 0.5 * (V8.HI - V8.LO)
        for ep in range(20):                                     # v2 (14:0x): loss in ACCELERATION space (atanh-space MSE was dominated by
            idx = rng.permutation(len(Xt))                       # clipped labels at |u| = 3.8 and did not beat a constant)
            for k in range(0, len(idx), 4096):
                j = torch.as_tensor(idx[k:k + 4096]); loss = ((sq(net.pi(XT[j])[:, 0]) - At[j]) ** 2).mean(); opt.zero_grad(); loss.backward(); opt.step()
        with torch.no_grad():
            av = V8.squash(net.pi(torch.as_tensor(Xv))[:, 0].numpy()); at = V8.squash(net.pi(XT)[:, 0].numpy())
        base = float(np.mean(np.abs(Yv - np.mean(Yt))))
        r2 = 1 - np.mean((av - Yv) ** 2) / np.var(Yv)
        res[arm] = dict(train_mae=float(np.mean(np.abs(at - Yt))), val_mae=float(np.mean(np.abs(av - Yv))), val_mae_constant_baseline=base, val_r2=float(r2), n_train=len(Yt), n_val=len(Yv))
        with torch.no_grad():
            net.log_std.fill_(-1.5)
        torch.save(dict(net=net, kind='ppo', spat=arm, reward=None, name=f'BC_glosa_{arm}', bc_of='GLOSA', note='behaviour clone of the simple heuristic GLOSA (D2)'), out / f'BC_glosa_{arm}_fleet.pt')
        print(arm, res[arm], flush=True)
    (out / 'bc_fit.json').write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'
    if sys.argv[1] == 'collect':
        collect(Path(sys.argv[2]), [int(x) for x in sys.argv[3:]])
    else:
        fit(Path(sys.argv[2]))
