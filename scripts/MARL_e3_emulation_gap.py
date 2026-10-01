#!/usr/bin/env python3
"""Where does legal emulation of the actor fail?  Replays development states with the prefix and, at each stored
snapshot, compares the actor's greedy action on its TRUE post-transmission view with the action after replacing ONE
part of the view by what the scheduler can reconstruct (diagnostic; privileged replay, never a deployable path):
  own_lanes   own per-lane vehicles/waiting -> the per-approach sums of i's last paid payload, split over 3 lanes
  own_lanes_fresh_split   own per-lane values -> TRUE per-approach sums split over 3 lanes (loss of lane detail only)
  own_phase   own phase / elapsed -> those of i's last paid payload
  fresh_msgs  this step's delivered payloads -> the latest paid copies z_j (one decision stale)
  all         every legal reconstruction at once (MARL_e3_emulation_probe's input)
Self-check (abort): the encoding rebuilt from the true view equals CommAdapter.encode(view, 'actual').
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from models.marl_comm_actor import CommAdapter, ActorNet, N_PH, SCALE_Q, SCALE_T
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_e3_continuation_labels import Policy, step_with
from scripts.MARL_e3_emulation_probe import encode as legal_encode


def main(a):
    ck = torch.load(a.ckpt, weights_only=False); sc = Scenarios(Path(a.scratch)); hits = {k: [] for k in ('own_lanes', 'own_lanes_fresh_split', 'own_phase', 'fresh_msgs', 'all')}
    for seed in a.seeds:
        for load in (8.0, 16.0):
            env, topo, _, _ = sc.env(seed, load); pol = Policy(ck, topo, env.action_interval); ad = pol.adapter; m = env.n_agents
            for t in range(max(a.snaps) + 1):
                with no_oracle_access(env):
                    ctx = env.scheduler_context(); z = ctx.features(); mir = env.mirror_features(); order, K = grant(env)
                    P = prefix_sets(order, K)
                    if t in a.snaps:
                        env.submit_profile([set(s) for s in P], R=None); views = env.transmit(); env.verify_mirror()
                        X = np.stack([ad.encode(views[i], 'actual') for i in range(m)])
                        with torch.no_grad():
                            A = pol.actor(torch.as_tensor(X), pol.mask).argmax(-1).numpy()
                        st = dict(m=m, z=z, mirror=mir, t=t)
                        L = np.stack([legal_encode(ad, st, i, set(P[i])) for i in range(m)])
                        own = 24; ph = slice(24, 24 + N_PH + 1)
                        variants = {}
                        v = X.copy(); v[:, :own] = L[:, :own]; variants['own_lanes'] = v
                        v = X.copy()
                        for i in range(m):
                            veh = np.asarray(views[i].lane_vehicles, np.float32); wt = np.asarray(views[i].lane_waiting, np.float32)
                            v[i, :12] = np.repeat(veh.sum(1) / 3.0, 3) / SCALE_Q; v[i, 12:24] = np.repeat(wt.sum(1) / 3.0, 3) / SCALE_Q
                        variants['own_lanes_fresh_split'] = v
                        v = X.copy(); v[:, ph] = L[:, ph]; variants['own_phase'] = v
                        v = X.copy(); off = ad.own_dim + m; v[:, off:] = L[:, off:]; variants['fresh_msgs'] = v
                        variants['all'] = L
                        for k, V in variants.items():
                            with torch.no_grad():
                                Av = pol.actor(torch.as_tensor(V), pol.mask).argmax(-1).numpy()
                            hits[k].append(float((Av == A).mean()))
                        acts = pol.act(views); env.step(acts); continue
                step_with(env, pol, P)
    rep = {k: round(float(np.mean(v)), 4) for k, v in hits.items()}; rep['snapshots'] = len(hits['all'])
    print(json.dumps(rep)); Path(a.out).write_text(json.dumps(rep, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ckpt', required=True); p.add_argument('--scratch', required=True); p.add_argument('--out', required=True)
    p.add_argument('--seeds', type=int, nargs='+', default=[501, 502, 503, 504]); p.add_argument('--snaps', type=int, nargs='+', default=[10, 16, 22])
    main(p.parse_args())
