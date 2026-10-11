#!/usr/bin/env python3
"""CITY_eval4 plus the SPaT-pilot fleets (PROTOCOL_CITY_SPAT_PILOT_20261004; 04/10/2026).  CITY_eval4 is not edited; this wrapper patches
its load_fleet for two new fleet specs and records '<eval4 sha>+eval6:<wrapper sha>' in source_sha256:
  --fleet P:<path to a v8 *_fleet.pt>   PPO fleet, DETERMINISTIC (action = squash(mean)); SPaT inputs on/off as stored in the checkpoint
  --fleet GLOSA                         simple heuristic GLOSA with the same SPaT feature (CITY_fleet_v8.CarGLOSA)
Both use the eval agent membership (_stable_u(seed, vid) < 0.5).  The --guard argument is ignored for these fleets (no guard)."""
import argparse, hashlib, sys
from pathlib import Path
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402

E4.SRC = f"{E4.SRC}+eval6:{hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}"
_orig = E4.load_fleet


def load_fleet(spec, seed, guard):
    if spec.startswith('P:'):
        p = Path(spec[2:]); d = torch.load(p, weights_only=False); net = d['net']; net.eval()
        return V8.CarPPO(net, E4.Q7.RHO, seed, d['spat'] == 'on', deterministic=True, record=False, reward=None), p
    if spec.startswith('R:'):                                    # v9 residual fleet on the in-class base controller (Amendment R4)
        import scripts.CITY_fleet_v9 as V9
        p = Path(spec[2:]); d = torch.load(p, weights_only=False); net = d['net']; net.eval()
        return V9.CarPPOR(net, E4.Q7.RHO, seed, d['spat'] == 'on', deterministic=True, record=False, reward=None), p
    if spec.startswith('ES:'):                                   # R6 parametric GLOSA from policy search (CITY_es_glosa.py); ES:<theta json>
        import json as _j
        import scripts.CITY_es_glosa as ES
        th = _j.loads(Path(spec[3:]).read_text())['theta']
        return ES.CarESGlosa(E4.Q7.RHO, seed, th), spec
    if spec == 'GLOSA':
        return V8.CarGLOSA(E4.Q7.RHO, seed), 'GLOSA'
    if spec == 'IC:GLOSA':                                       # D2 representability control (CITY_d2_inclass.py), added 04/10 13:58
        import scripts.CITY_d2_inclass as IC
        return IC.CarICGlosa(E4.Q7.RHO, seed), 'IC:GLOSA'
    return _orig(spec, seed, guard)


E4.load_fleet = load_fleet

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--light', default='ACT'); p.add_argument('--light-obs', default='raw'); p.add_argument('--light-fallback', default='none')
    p.add_argument('--fleet', default='human'); p.add_argument('--guard', default='none')
    p.add_argument('--record'); p.add_argument('--replay'); p.add_argument('--replay-dir'); p.add_argument('--discharge', action='store_true'); p.add_argument('--delay-trace', action='store_true')
    p.add_argument('--swap-at', type=float); p.add_argument('--swap-light'); p.add_argument('--swap-fleet')
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--tag'); p.add_argument('--out', required=True)
    E4.main(p.parse_args())
