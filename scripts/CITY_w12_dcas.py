#!/usr/bin/env python3
"""W12-4 DCA-task runtime (PROTOCOL_CITY_WAVE12_20261006, Amendment A3).  DC-Ada's transform in front of a frozen RL-H light, two arms:
  DCAS_MODE=info  the input is RL-H's 7 features plus the speed-binned counts TSI uses (n[0.1,2) and n[2,5) on each green's served lanes, / 10),
                  transform 11 -> 32 -> 32 -> 7 (DC-Ada's residual MLP; output added to the 7 RL-H features; zero init = identity);
  DCAS_MODE=raw   DCA3's 7 -> 7 transform.
Outputs pass DC-Ada's nan_to_num and the [-10, 10] bound.  References and candidates both pass through this wrapper, so DCAS_END applies to
both.  Usage: DCAS_MODE=info|raw DCAS_END=<s> [DCAS_PARAMS=<pt>] CITY_w12_dcas.py <target script> <its args>"""
import hashlib, math, os, runpy, sys
from pathlib import Path
import numpy as np
import torch
import torch.nn as nn
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_dcada_layer import TransformationLayer  # noqa: E402


class TransformationLayerX(nn.Module):
    """DC-Ada's residual MLP with extra (information) inputs: y = x[:7] + dec(relu(hid(ln(relu(enc(x))))))."""

    def __init__(self, in_dim=11, out_dim=7, latent_dim=32):
        super().__init__()
        self.out_dim = out_dim
        self.encoder = nn.Linear(in_dim, latent_dim); self.hidden = nn.Linear(latent_dim, latent_dim); self.decoder = nn.Linear(latent_dim, out_dim)
        self.layer_norm = nn.LayerNorm(latent_dim)
        for m in (self.encoder, self.hidden, self.decoder):
            nn.init.zeros_(m.weight); nn.init.zeros_(m.bias)

    def forward(self, x):
        latent = torch.relu(self.encoder(x)); latent = self.layer_norm(latent); latent = torch.relu(self.hidden(latent))
        return self.decoder(latent) + x[..., :self.out_dim]

    def get_params_vector(self):
        return torch.cat([p.data.view(-1) for p in self.parameters()])

    def set_params_vector(self, v):
        i = 0
        for p in self.parameters():
            n = p.numel(); p.data.copy_(v[i:i + n].view(p.shape)); i += n


def new_layer(mode):
    return TransformationLayerX() if mode == 'info' else TransformationLayer()


def speed_bins(info, tid):
    """[n[0.1,2) green 0, n[2,5) green 0, n[0.1,2) green 1, n[2,5) green 1] / 10, on the served lanes (the bins of TSI's adapter)."""
    ls = CE.ls; z = []
    for s in info.tls[tid]['serve']:
        m1 = m2 = 0
        for l in s:
            for v in ls.lane.getLastStepVehicleIDs(l):
                sp = ls.vehicle.getSpeed(v); m1 += 0.1 <= sp < 2.0; m2 += 2.0 <= sp < 5.0
        z += [m1 / 10, m2 / 10]
    return np.asarray(z, np.float32)


class LightDCAS(E4.LightRLX):
    def __init__(self, info, policy, params, mode):
        super().__init__(info, policy, adapter='raw'); self.mode = mode; self.transforms = {}
        for tid in info.tls:
            tr = new_layer(mode); tr.set_params_vector(torch.as_tensor(params[tid], dtype=torch.float32)); tr.eval(); self.transforms[tid] = tr

    def obs(self, tid):
        obs, halt, cur = super().obs(tid)
        x = np.concatenate([np.asarray(obs, np.float32), speed_bins(self.info, tid)]) if self.mode == 'info' else np.asarray(obs, np.float32)
        with torch.no_grad():
            y = self.transforms[tid](torch.as_tensor(x)[None])[0]
            y = torch.clamp(torch.nan_to_num(y, nan=0.0, posinf=0.0, neginf=0.0), -10.0, 10.0)
        return y.numpy().astype(np.float32), halt, cur


def install(end, params_path, mode):
    assert mode in ('info', 'raw'), mode
    if end is not None:
        assert math.isfinite(end) and end > 0
    if params_path:
        params = torch.load(params_path, weights_only=False); build = E4.build_light

        def build_light(spec, info, adapter, box):
            net, light, a, b = build(spec, info, adapter, box)
            assert isinstance(light, E4.LightRLX), 'DCAS requires an RL signal'
            assert set(params) == set(info.tls), 'controller ids'
            return net, LightDCAS(info, light.inner, params, mode), a, b
        E4.build_light = build_light
    run0 = E4.run

    def run(args, seed, requested_end):
        horizon = requested_end if end is None else end
        out = run0(args, seed, horizon)
        out.update(dcas_horizon_s=horizon, dcas_mode=mode, dcas_runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   dcas_params_sha256=hashlib.sha256(Path(params_path).read_bytes()).hexdigest() if params_path else None)
        return out
    E4.run = run


if __name__ == '__main__':
    install(float(os.environ['DCAS_END']) if os.environ.get('DCAS_END') else None, os.environ.get('DCAS_PARAMS'), os.environ.get('DCAS_MODE', 'raw'))
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]
    runpy.run_path(str(ROOT / target), run_name='__main__')
