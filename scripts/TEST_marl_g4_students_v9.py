#!/usr/bin/env python3
"""SELF-CHECK for the optimised 4x4 relaunch (02/10/2026 01:5x): the exact-resume trainer v9 may replace the 4x4 chain's
student trainers only if, on the 4x4 grid wrappers, it reproduces them bit for bit.  Tiny configuration (4 iterations, 2
episodes per iteration, buffer 3, evaluation every 2, 1 thread), 4x4 teacher set_full_s0, in <out>/:
  Z1 / Z9   zero-byte student: MARL_e3_actor_distill.py (the chain's) vs v9, --student-delivery none   (MARL_grid_wrapper)
  R6 / R9   relay student: MARL_e3_actor_distill_v6.py (the chain's) vs v9, prefix / age / quant 4 / agefirst
            (MARL_grid_relay_wrapper, nearest8 slots)
  RB        v9 relay with --stop-after 3 (state at iteration 2), then rerun in place under the wrapper (must resume at 2)
PASS iff Z9 = Z1, R9 = R6 and RB = R9 (every tensor of ckpt_last / ckpt_best, the last-attempt log records), and every run
exits 0.  Usage: TEST_marl_g4_students_v9.py <out dir>."""
import json, os, subprocess, sys
from pathlib import Path
import torch

ROOT = Path(__file__).resolve().parents[1]; OUT = Path(sys.argv[1]); OUT.mkdir(parents=True, exist_ok=False)
PY = str(ROOT / 'external_envs/runtime/bin/python'); T = 'research/marl_budget/e3_grid4x4_20260930/actors/set_full_s0/ckpt_best.pt'
W = ['scripts/MARL_grid_wrapper.py', '--rows', '4', '--cols', '4', '--']
WR = ['scripts/MARL_grid_relay_wrapper.py', '--rows', '4', '--cols', '4', '--relay-slots', 'nearest8', '--']
TINY = ['--teacher', T, '--seed', '0', '--iters', '4', '--eps-per-iter', '2', '--buffer', '3', '--eval-every', '2', '--threads', '1']
ZA = ['--student-delivery', 'none']; RA = ['--student-delivery', 'prefix', '--relay', 'age', '--quant', '4', '--order', 'agefirst']
env = dict(os.environ, CIG_EXTERNAL_RUNTIME_ACTIVE='1', PYTHONDONTWRITEBYTECODE='1', OMP_NUM_THREADS='1')


def run(wrap, script, args, out, extra=()):
    r = subprocess.run([PY, '-u', *wrap, f'scripts/{script}', *TINY, *args, '--out', str(out), *extra], cwd=ROOT, env=env, capture_output=True, text=True)
    print(f'--- {script} {out.name} {" ".join(extra)} rc={r.returncode}\n' + r.stdout[-400:] + r.stderr[-600:], flush=True)
    return r.returncode


def records(out):
    last = {}
    for l in (out / 'log.jsonl').read_text().splitlines():
        d = json.loads(l)
        if 'it' in d:
            last[d['it']] = (round(d['loss'], 12), d['agree'], d['n'], d.get('select_queue_sum'))
    return last


def same(x, y):
    ok = records(x) == records(y)
    for f in ('ckpt_last.pt', 'ckpt_best.pt'):
        a, b = torch.load(x / f, weights_only=False), torch.load(y / f, weights_only=False)
        ok &= a['it'] == b['it'] and a['select'] == b['select'] and all(torch.equal(a['actor'][k], b['actor'][k]) for k in a['actor'])
    return ok


V9 = 'MARL_e3_actor_distill_v9.py'
rc = [run(W, 'MARL_e3_actor_distill.py', ZA, OUT / 'Z1'), run(W, V9, ZA, OUT / 'Z9'),
      run(WR, 'MARL_e3_actor_distill_v6.py', RA, OUT / 'R6'), run(WR, V9, RA, OUT / 'R9'),
      run(WR, V9, RA, OUT / 'RB', ['--stop-after', '3']), run(WR, V9, RA, OUT / 'RB')]
checks = dict(return_codes=rc == [0] * 6, Z9_eq_Z1=same(OUT / 'Z9', OUT / 'Z1'), R9_eq_R6=same(OUT / 'R9', OUT / 'R6'),
              RB_resumed_at_2='"from_it": 2' in (OUT / 'RB' / 'log.jsonl').read_text(), RB_eq_R9=same(OUT / 'RB', OUT / 'R9'),
              grid_4x4=all(json.loads((OUT / f'{n}.grid.json').read_text()).get('rows') == 4 for n in ('Z9', 'R9', 'RB')))
print(json.dumps(checks, indent=1)); verdict = 'PASS' if all(checks.values()) else 'FAIL'
(OUT / 'RESULT.json').write_text(json.dumps(dict(checks=checks, verdict=verdict), indent=1)); print('G4 STUDENTS v9 SELF-CHECK', verdict)
