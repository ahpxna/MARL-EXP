#!/usr/bin/env python3
"""Null (constant-action) fleets for the baseline-reproducibility check B6-Z (PROTOCOL_CITY_B6 §B6-Z, 04/10/2026 wake 8).  No training:
each checkpoint is the Q7 DQN architecture (6 -> 64 -> 64 -> nact) with the last layer's weights zeroed and a one-hot bias, so
argmax is the same action for every observation.  Loadable by CITY_eval4 / eval5 as --fleet U:<name>.
  Z-rel    actions 'release', always action len(ACC) = hand the car to SUMO every second   -> must equal always-SUMO
  Z-res0   actions 'residual', always delta = 0 (getSpeedWithoutTraCI + 0)                -> does the residual class contain SUMO?
  Z-hold   actions 'acc', always a = 0 (hold the current speed; cruise control)           -> descriptive: what commanding alone does"""
import hashlib, sys
from pathlib import Path
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_env import ACC  # noqa: E402

FU = ROOT / 'research/city_sim/fleet_upgrade_20261004'; SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
SPECS = {'Z-rel': ('release', len(ACC) + 1, len(ACC)), 'Z-res0': ('residual', 5, 3), 'Z-hold': ('acc', len(ACC), 3)}


def const_net(nact, k):
    net = nn.Sequential(nn.Linear(6, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, nact))
    with torch.no_grad():
        net[4].weight.zero_(); net[4].bias.zero_(); net[4].bias[k] = 1.0
    return net.eval()


if __name__ == '__main__':
    assert float(ACC[3]) == 0.0
    for name, (actions, nact, k) in SPECS.items():
        fn = FU / f'{name}_fleet.pt'
        if fn.exists():
            print('exists, kept', fn); continue
        net = const_net(nact, k); o = torch.randn(1000, 6) * 3
        assert (net(o).argmax(1) == k).all()
        torch.save(dict(net=net, kind='fleet', actions=actions, tmax=[1e9, 1e9], name=name, null_action=k, reward=None, episodes=0,
                        source_sha256=SRC, note='constant-action null fleet (B6-Z); not trained'), fn)
        print('wrote', fn, actions, 'action', k)
