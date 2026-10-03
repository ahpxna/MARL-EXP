#!/usr/bin/env python3
"""SELF-CHECK of MARL_e3_actor_distill_v9.py exact resume (01/10/2026 22:1x).  Tiny configuration (6 iterations, 2 episodes
per iteration, buffer 3, evaluation every 2, 1 thread) in <out>/{A, B, C}:
  A  v9 uninterrupted;  B  v9 with --stop-after 3 (state at iteration 2 only), then rerun in place (must resume at 2);
  C  v8 uninterrupted (v9 without interruption must be v8).
PASS iff every tensor of ckpt_last.pt and ckpt_best.pt is equal between A and B and between A and C, and the last-attempt
log records (loss, agree, n, select) of iterations 1-6 are equal.  Usage: TEST_marl_distill_v9_resume.py <out dir>."""
import json, os, subprocess, sys
from pathlib import Path
import torch

ROOT = Path(__file__).resolve().parents[1]; OUT = Path(sys.argv[1]); OUT.mkdir(parents=True, exist_ok=False)
PY = str(ROOT / 'external_envs/runtime/bin/python'); D = 'research/marl_budget/e3_delivery_actors_20260929'
BASE = ['--teacher', f'{D}/set_full_s0/ckpt_best.pt', '--student-delivery', 'prefix', '--relay', 'age', '--quant', '4', '--order', 'agefirst',
        '--capacity', 'iid', '--seed', '0', '--iters', '6', '--eps-per-iter', '2', '--buffer', '3', '--eval-every', '2', '--threads', '1']
env = dict(os.environ, CIG_EXTERNAL_RUNTIME_ACTIVE='1', PYTHONDONTWRITEBYTECODE='1', OMP_NUM_THREADS='1')


def run(script, out, extra=()):
    r = subprocess.run([PY, '-u', f'scripts/{script}', *BASE, '--out', str(out), *extra], cwd=ROOT, env=env, capture_output=True, text=True)
    print(f'--- {script} {out.name} {" ".join(extra)} rc={r.returncode}\n' + r.stdout[-600:] + r.stderr[-600:], flush=True)
    return r.returncode


def records(out):
    last = {}
    for l in (out / 'log.jsonl').read_text().splitlines():
        d = json.loads(l)
        if 'it' in d:
            last[d['it']] = (round(d['loss'], 12), d['agree'], d['n'], d.get('select_queue_sum'))
    return last


def same_ck(x, y):
    ok = True
    for f in ('ckpt_last.pt', 'ckpt_best.pt'):
        a, b = torch.load(x / f, weights_only=False), torch.load(y / f, weights_only=False)
        ok &= a['it'] == b['it'] and a['select'] == b['select'] and all(torch.equal(a['actor'][k], b['actor'][k]) for k in a['actor'])
    return ok


rc = [run('MARL_e3_actor_distill_v9.py', OUT / 'A'), run('MARL_e3_actor_distill_v9.py', OUT / 'B', ['--stop-after', '3'])]
rc.append(run('MARL_e3_actor_distill_v9.py', OUT / 'B')); rc.append(run('MARL_e3_actor_distill_v8.py', OUT / 'C'))
logB = (OUT / 'B' / 'log.jsonl').read_text()
checks = dict(return_codes=rc == [0, 0, 0, 0], B_resumed_at_2='"from_it": 2' in logB, B_manifest=(OUT / 'B' / 'manifest.json').exists(),
              A_eq_B_ckpts=same_ck(OUT / 'A', OUT / 'B'), A_eq_C_ckpts=same_ck(OUT / 'A', OUT / 'C'),
              A_eq_B_log=records(OUT / 'A') == records(OUT / 'B'), A_eq_C_log=records(OUT / 'A') == records(OUT / 'C'),
              six_iterations=sorted(records(OUT / 'B')) == [1, 2, 3, 4, 5, 6])
print(json.dumps(checks, indent=1)); verdict = 'PASS' if all(checks.values()) else 'FAIL'
(OUT / 'RESULT.json').write_text(json.dumps(dict(checks=checks, verdict=verdict), indent=1)); print('RESUME SELF-CHECK', verdict)
