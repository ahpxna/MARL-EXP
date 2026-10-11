#!/usr/bin/env python3
"""M3′-D evaluator (PROTOCOL_CITY_M3P_DIAG_20261004): CITY_eval_m3p (unchanged, imported: its fleet SPaT rebinding to the light's spat(), its
violation sidecar for every LightRPC instance) + CITY_eval_m3_shadow (SHADOW:<fleet.pt> spec) + the light spec
  RPC2:<k>:<trigger>:<F>:<M>    F 1 = forced hold (registered) / 0 = no forced delay; M 1 = message withdrawn at T_c (registered) / 0 = kept to onset
Extra sidecar <tag>_m3p2.json per seed: H1 log (issue actions, Q-gaps, held-tick actions), zero-hold count, kept messages, and the commitment
list (tid, t_issue, T_c) for the open-loop replay step.  Usage as CITY_eval_m3p.py."""
import hashlib, json, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval_m3p as P  # noqa: E402
_argv = sys.argv; sys.argv = [_argv[0], '--spat-arm', 'none']
import scripts.CITY_eval_m3_shadow as SH  # noqa: E402,F401
sys.argv = _argv
import scripts.CITY_m3p_rpc2 as RPC2  # noqa: E402
import torch  # noqa: E402
W, E4, X2 = P.W, P.E4, P.X2; E4.SRC = f"{E4.SRC}+m3p2:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
SIDE2 = {}; _bl = E4.build_light


def build_light(spec, info, adapter, box):
    if spec.startswith('RPC2:'):
        _, k, trig, F, M = spec.split(':'); _n, ck, _m = X2.light_spec(f'RL-H:{k}'); q = torch.load(ck, weights_only=False)['net']; q.eval()
        L = RPC2.LightRPC2(info, q, trig, None, seed=int(k), forced=F == '1', keep=M == '0'); W.CUR.update(light=L); return W.Q7.NET_S, L, [], None
    return _bl(spec, info, adapter, box)


E4.build_light = build_light
_run = E4.run


def run(a, seed, end):
    out = _run(a, seed, end); L = W.CUR.get('light')
    if isinstance(L, RPC2.LightRPC2):
        g = np.array(L.log['issue_gap']); h = np.array(L.log['held_gap'])
        SIDE2[str(seed)] = dict(issue_switch=L.log['issue_switch'], issue_keep=L.log['issue_keep'], issue_gap_mean_pos=float(g[g > 0].mean()) if (g > 0).any() else 0.0,
                                held_switch=L.log['held_switch'], held_keep=L.log['held_keep'], held_gap_mean_pos=float(h[h > 0].mean()) if (h > 0).any() else 0.0,
                                zero_hold=L.log['zero_hold'], kept_msgs=L.log['kept_msgs'], commits=[list(c) for c in L.log['commits']])
    return out


E4.run = run
if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    a = p.parse_args(); E4.main(a)
    Path(a.out, f'{a.tag}_m3p.json').write_text(json.dumps(dict(light=a.light, fleet=a.fleet, per_seed=P.SIDE)))
    Path(a.out, f'{a.tag}_m3p2.json').write_text(json.dumps(dict(light=a.light, fleet=a.fleet, per_seed=SIDE2)))
