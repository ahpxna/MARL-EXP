#!/usr/bin/env python3
"""BCWI-inspired weight interpolation (03/10/2026; PROTOCOL_E3_ADAPT_PILOT_20261003 §2; Schumann et al., arXiv 2301.10546):
theta = (1 - alpha) * theta_parent + alpha * theta_child, for a child fine-tuned FROM that parent (same parameterisation;
asserted through the child's recorded parent sha).  Writes a checkpoint in the trainers' format."""
import argparse, hashlib, sys
from pathlib import Path
import torch
p = argparse.ArgumentParser(); p.add_argument('--parent', required=True); p.add_argument('--child', required=True)
p.add_argument('--alpha', type=float, required=True); p.add_argument('--out', required=True); a = p.parse_args()
P = torch.load(a.parent, weights_only=False); C = torch.load(a.child, weights_only=False)
if C['config'].get('parent_sha256') != hashlib.sha256(Path(a.parent).read_bytes()).hexdigest():
    sys.exit('the child was not fine-tuned from this parent')
if P['schema'] != C['schema'] or set(P['actor']) != set(C['actor']):
    sys.exit('parameterisations differ')
actor = {k: (1 - a.alpha) * P['actor'][k].float() + a.alpha * C['actor'][k].float() for k in P['actor']}
cfg = dict(C['config'], bcwi_alpha=a.alpha, bcwi_parent=a.parent, bcwi_child=a.child)
Path(a.out).parent.mkdir(parents=True, exist_ok=True); torch.save(dict(actor=actor, config=cfg, schema=C['schema']), a.out); print('wrote', a.out)
