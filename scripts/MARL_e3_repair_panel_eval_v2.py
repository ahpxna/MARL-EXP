#!/usr/bin/env python3
"""Repair-panel evaluator v2 (03/10/2026 23:2x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003 E8): v1
(scripts/MARL_e3_repair_panel_eval.py, NOT edited; imported) plus the residual-guarded Gaussian gate FB_Mr+/-:
  flag iff FB_Mq's test fires (empirical 0.99 threshold on the shared d2) OR the component of (x - mu) outside the column space
  of the calibration covariance is larger than every calibration view's: ||(I - C C^+)(x - mu)|| > r*, r* = max over calibration
  keys of the same residual (rounded to 1e-9, strict >).  Why: CK1's calibration covariance is rank-deficient (a feature constant
  under K1); the pseudo-inverse is blind to deviations along that direction.  Everything else (calibration parity with the #3
  counts, calibration / runtime decision parity, first-episode identities, arms) is v1's code path."""
from __future__ import annotations
import argparse, sys
from collections import defaultdict
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_e3_repair_panel_eval as RP

_build, _gate_of = RP.build, RP.gate_of


def _resid(x, mu, R):
    d = np.asarray(x, np.float64) - mu
    return round(float(np.linalg.norm(R @ d)), 9)


def build(name, counts):
    if not name.startswith('FB_Mr'):
        return _build(name, counts)
    cond = name.endswith('+'); spec = _build('FB_Mq' + name[-1], counts); spec['name'] = name
    groups = defaultdict(list)
    for k, c in counts.items():
        groups[str(k[0]) if cond else 'all'].append((tuple(k[1:]), c))
    for b, kc in groups.items():
        X = np.array([f for f, _ in kc], np.float64); w = np.asarray([c for _, c in kc], np.float64); w = w / w.sum()
        mu = np.array(spec['params'][b]['mu']); C = ((X - mu).T * w) @ (X - mu)
        R = np.eye(C.shape[0]) - C @ np.linalg.pinv(C, rcond=1e-10)
        spec['params'][b]['R'] = R.tolist(); spec['params'][b]['rstar'] = max(_resid(f, mu, R) for f, _ in kc)
    return spec


def gate_of(spec):
    if not spec['name'].startswith('FB_Mr'):
        return _gate_of(spec)
    base = _gate_of(dict(spec, name='FB_Mq' + spec['name'][-1]))
    prm = {b: (np.array(p['mu'], np.float64), np.array(p['R'], np.float64), p['rstar']) for b, p in spec['params'].items()}
    cond = spec['cond']

    def g(key):
        if base(key):
            return True
        b = str(key[0]) if cond else 'all'
        if b not in prm:
            return True
        mu, R, rs = prm[b]
        return _resid(key[1:], mu, R) > rs
    return g


RP.build = build; RP.gate_of = gate_of
RP.DETECTORS.extend(['FB_Mr+', 'FB_Mr-'])
RP.SOURCES.append('scripts/MARL_e3_repair_panel_eval_v2.py')

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--relay'); p.add_argument('--z'); p.add_argument('--tag', default='')
    p.add_argument('--calibrate', action='store_true'); p.add_argument('--calib-old')
    p.add_argument('--calib-lo', type=int, default=301); p.add_argument('--calib-hi', type=int, default=332)
    p.add_argument('--z-only', action='store_true')
    p.add_argument('--detectors'); p.add_argument('--floors')
    p.add_argument('--arms', nargs='+', default=['PLAIN', 'FB_S+', 'FB_Mq-', 'FB_Mq+', 'FB_Mr-', 'FB_Mr+'])
    p.add_argument('--K', type=int, default=0); p.add_argument('--ktrain', type=int, default=1)
    p.add_argument('--parity', nargs='*', default=[])
    p.add_argument('--codebook', default='research/marl_budget/e3_payload_codebook_20260929.json')
    p.add_argument('--traffic-seeds', type=int, nargs='*', default=[]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    a = p.parse_args()
    if not a.calibrate and not a.z_only and 'PLAIN' not in a.arms:
        p.error('PLAIN is required (first-episode identities)')
    RP.main(a)
