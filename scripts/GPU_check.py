"""GPU check and CPU-vs-GPU timing of the shared learners (run on the RTX 4090 box after scripts/setup_linux_gpu.sh).

  external_envs/city_runtime/bin/python -u scripts/GPU_check.py

For each learner it times the same synthetic update on CPU and on CUDA (fresh process each, via CIG_DEVICE) and checks the
CPU/CUDA results agree to float tolerance. The table says, per learner, whether CIG_DEVICE=cuda is worth setting: tiny
64-unit MLPs on minibatch 256 may well be faster on the CPU; big DAgger buffers and PPO minibatches of 4096 should not be.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CASES = ('dqn', 'ppo', 'distill')


def child(case):
    sys.path.insert(0, str(ROOT))
    import numpy as np
    import torch
    import torch.nn as nn
    import scripts.cig_device as CD
    torch.set_num_threads(int(os.environ.get('CHECK_THREADS', '1')))
    rng = np.random.default_rng(0); torch.manual_seed(0)
    if case == 'dqn':
        from scripts.CITY_q7_cross_version import DQN
        ag = DQN(7, 2, 0.9, 11)
        for _ in range(20_000):
            s = rng.random(7, dtype=np.float32); ag.add([(s, int(rng.integers(2)), float(rng.random()), s, 0.0)])
        t = time.perf_counter(); loss = ag.train(400); sec = time.perf_counter() - t
        w = float(sum(p.double().sum() for p in ag.net.parameters()))
    elif case == 'ppo':
        import scripts.CITY_fleet_v8 as V8
        net = V8.Net(0); opt = torch.optim.Adam(net.parameters(), lr=3e-4); n = 60_000
        batch = (rng.random((n, V8.OBS_DIM), dtype=np.float32), rng.standard_normal(n).astype(np.float32),
                 np.full(n, -1.0, np.float32), rng.standard_normal(n).astype(np.float32), rng.standard_normal(n).astype(np.float32))
        t = time.perf_counter(); loss = float(V8.ppo_update(net, opt, batch, rng=np.random.default_rng(0))[1]); sec = time.perf_counter() - t
        w = float(sum(p.double().sum() for p in net.parameters()))
    else:                                                            # DAgger-sized set actor: (N*m, dim) -> 5 actions, epochs over a big buffer
        net = nn.Sequential(nn.Linear(64, 256), nn.ReLU(), nn.Linear(256, 256), nn.ReLU(), nn.Linear(256, 5)); opt = torch.optim.Adam(net.parameters(), 1e-3)
        X = rng.random((400_000, 64), dtype=np.float32); Y = rng.integers(0, 5, 400_000)
        idx = np.arange(len(Y)); t = time.perf_counter()
        with CD.on_learner([net], [opt]):
            Xd, Yd = CD.to_dev(X, Y)
            for _ in range(3):
                rng.shuffle(idx)
                for mb in np.array_split(idx, len(idx) // 1024):
                    mb = CD.to_dev(mb); l = nn.functional.cross_entropy(net(Xd[mb]), Yd[mb]); opt.zero_grad(); l.backward(); opt.step()
            loss = float(l)
        sec = time.perf_counter() - t; w = float(sum(p.double().sum() for p in net.parameters()))
    print(json.dumps(dict(case=case, seconds=sec, loss=float(loss), wsum=w, **CD.describe())))


def main():
    import torch
    print(f'torch {torch.__version__}, cuda available {torch.cuda.is_available()}', flush=True)
    if torch.cuda.is_available():
        print(f'GPU: {torch.cuda.get_device_name(0)}; CUDA {torch.version.cuda}', flush=True)
    rows = []
    for case in CASES:
        r = {}
        for dev in (('cpu', 'cuda') if torch.cuda.is_available() else ('cpu',)):
            env = dict(os.environ, CIG_DEVICE=dev, PYTHONHASHSEED='0', OMP_NUM_THREADS='1')
            p = subprocess.run([sys.executable, __file__, '--child', case], env=env, capture_output=True, text=True)
            if p.returncode:
                print(f'{case} on {dev} FAILED:\n{p.stderr[-2000:]}', flush=True); continue
            r[dev] = json.loads(p.stdout.strip().splitlines()[-1])
        if 'cpu' in r and 'cuda' in r:
            c, g = r['cpu'], r['cuda']; rel = abs(c['wsum'] - g['wsum']) / max(1e-9, abs(c['wsum']))
            verdict = 'use cuda' if g['seconds'] < 0.8 * c['seconds'] else 'keep cpu'
            rows.append(f'{case:8s} cpu {c["seconds"]:7.2f}s  cuda {g["seconds"]:7.2f}s  speedup {c["seconds"] / g["seconds"]:5.2f}x  '
                        f'weights rel.diff {rel:.1e}  -> {verdict}')
        elif 'cpu' in r:
            rows.append(f'{case:8s} cpu {r["cpu"]["seconds"]:7.2f}s  (no cuda)')
    print('\n'.join(rows))


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == '--child':
        child(sys.argv[2])
    else:
        main()
