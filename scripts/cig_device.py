"""Learner device for the gradient phase of every trainer (user 18/11/2026: use the RTX 4090 wherever it can be used).

CIG_DEVICE = auto (default: cuda if torch sees one, else cpu) | cpu | cuda | cuda:N | mps.

What moves: the update step only (replay minibatches, PPO epochs, DAgger epochs). Rollouts stay on CPU: SUMO steps on the
CPU, and a 64-unit MLP called on a batch of 16 signals per step is faster on the CPU than across PCIe. `on_learner` moves the
networks and their optimizer state to the device for the update and back to the CPU afterwards, so policies, checkpoints
and every caller keep seeing CPU tensors.

With device cpu every helper is a no-op: CPU runs execute exactly the code they did before and stay bit-identical.
CIG_DETERMINISTIC=1 (default) asks torch for deterministic CUDA kernels and disables TF32. GPU arithmetic still differs
from CPU arithmetic in the last bits, so a GPU run is a new registered run, never a reproduction of a CPU row.
"""
from __future__ import annotations

import contextlib
import os
import sys

import torch

_DEV = None


def device() -> torch.device:
    global _DEV
    if _DEV is not None:
        return _DEV
    want = os.environ.get('CIG_DEVICE', 'auto').strip().lower()
    if want == 'auto':
        want = 'cuda' if torch.cuda.is_available() else 'cpu'
    d = torch.device(want)
    if d.type == 'cuda':
        if not torch.cuda.is_available():
            raise RuntimeError(f'CIG_DEVICE={want} but torch.cuda.is_available() is False')
        if os.environ.get('CIG_DETERMINISTIC', '1') == '1':
            os.environ.setdefault('CUBLAS_WORKSPACE_CONFIG', ':4096:8')
            torch.backends.cudnn.deterministic = True
            torch.backends.cudnn.benchmark = False
            torch.backends.cuda.matmul.allow_tf32 = False
            torch.backends.cudnn.allow_tf32 = False
            torch.use_deterministic_algorithms(True, warn_only=True)
        else:
            torch.backends.cudnn.benchmark = True
            torch.backends.cuda.matmul.allow_tf32 = True
            torch.backends.cudnn.allow_tf32 = True
        print(f'[cig_device] learner on {d} ({torch.cuda.get_device_name(d)}), '
              f'deterministic={os.environ.get("CIG_DETERMINISTIC", "1")}', file=sys.stderr, flush=True)
    elif d.type == 'mps':
        if not torch.backends.mps.is_available():
            raise RuntimeError('CIG_DEVICE=mps but MPS is not available')
        print('[cig_device] learner on mps', file=sys.stderr, flush=True)
    _DEV = d
    return d


def describe() -> dict:
    """Provenance record for configs and manifests."""
    d = device()
    rec = dict(learner_device=str(d), torch=torch.__version__, deterministic=os.environ.get('CIG_DETERMINISTIC', '1'))
    if d.type == 'cuda':
        rec.update(gpu=torch.cuda.get_device_name(d), cuda=torch.version.cuda)
    return rec


def to_dev(*xs):
    """numpy arrays / tensors -> tensors on the learner device (torch.as_tensor semantics, so dtypes are kept)."""
    d = device()
    out = tuple(torch.as_tensor(x).to(d, non_blocking=True) for x in xs)
    return out if len(out) != 1 else out[0]


def _move_optimizer(opt, d):
    for st in opt.state.values():
        for k, v in st.items():
            if k != 'step' and torch.is_tensor(v):          # Adam keeps 'step' on the CPU unless capturable/fused
                st[k] = v.to(d)


@contextlib.contextmanager
def on_learner(modules, optimizers=()):
    """Move modules (and the optimizers that own their parameters) to the learner device for the block, then back to CPU."""
    d = device()
    if d.type == 'cpu':
        yield d
        return
    modules = [m for m in modules if m is not None]
    for m in modules:
        m.to(d)
    for o in optimizers:
        _move_optimizer(o, d)
    try:
        yield d
    finally:
        for m in modules:
            m.to('cpu')
        for o in optimizers:
            _move_optimizer(o, torch.device('cpu'))
