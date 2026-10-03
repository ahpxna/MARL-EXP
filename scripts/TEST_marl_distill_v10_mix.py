#!/usr/bin/env python3
"""SELF-CHECK of MARL_e3_actor_distill_v10.py (02/10/2026 01:4x; PROTOCOL_E3_MIXED_CHANNEL_20261001.md Addendum 1).  Tiny
configuration (6 iterations, 2 episodes per iteration, buffer 3, evaluation every 3, 1 thread) in <out>/:
  I10 / I9   v10 and v9 at --capacity iid      (v10 at a single regime must be v9)
  K10 / K9   v10 and v9 at --capacity const1
  M          v10 at --capacity mix, uninterrupted
  MB         v10 at --capacity mix with --stop-after 4 (state at iteration 3 only), then rerun in place (must resume at 3)
  regimes    MIX_REGIME gives every regime exactly 32 of TRAIN's 128 and 4 of SELECT's 16 episodes, and apply_capacity()
             under mix sets env._trace to K everywhere for a constK episode and leaves the scenario's own trace for an iid one
PASS iff I10 = I9, K10 = K9, MB = M (every tensor of ckpt_last / ckpt_best, the last-attempt log records), M differs from
I10 and from K10 (the mix changes training, a check that can fail), and the regime checks hold.
Usage: TEST_marl_distill_v10_mix.py <out dir>."""
import json, os, subprocess, sys
from collections import Counter
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; OUT = Path(sys.argv[1]); OUT.mkdir(parents=True, exist_ok=False)
sys.path.insert(0, str(ROOT))
PY = str(ROOT / 'external_envs/runtime/bin/python'); D = 'research/marl_budget/e3_delivery_actors_20260929'
BASE = ['--teacher', f'{D}/set_full_s0/ckpt_best.pt', '--student-delivery', 'prefix', '--relay', 'age', '--quant', '4', '--order', 'agefirst',
        '--seed', '0', '--iters', '6', '--eps-per-iter', '2', '--buffer', '3', '--eval-every', '3', '--threads', '1']
env = dict(os.environ, CIG_EXTERNAL_RUNTIME_ACTIVE='1', PYTHONDONTWRITEBYTECODE='1', OMP_NUM_THREADS='1')


def run(script, out, cap, extra=()):
    r = subprocess.run([PY, '-u', f'scripts/{script}', *BASE, '--capacity', cap, '--out', str(out), *extra], cwd=ROOT, env=env, capture_output=True, text=True)
    print(f'--- {script} {out.name} {cap} {" ".join(extra)} rc={r.returncode}\n' + r.stdout[-400:] + r.stderr[-600:], flush=True)
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


V10, V9 = 'MARL_e3_actor_distill_v10.py', 'MARL_e3_actor_distill_v9.py'
rc = [run(V10, OUT / 'I10', 'iid'), run(V9, OUT / 'I9', 'iid'), run(V10, OUT / 'K10', 'const1'), run(V9, OUT / 'K9', 'const1'),
      run(V10, OUT / 'M', 'mix'), run(V10, OUT / 'MB', 'mix', ['--stop-after', '4']), run(V10, OUT / 'MB', 'mix')]

import scripts.MARL_e3_actor_distill_v10 as V
from scripts.MARL_e3_actor_train import Scenarios, TRAIN, SELECT
cT = Counter(V.MIX_REGIME[(int(s), float(h))] for s, h in TRAIN); cS = Counter(V.MIX_REGIME[(int(s), float(h))] for s, h in SELECT)
sc = Scenarios(OUT / 'S'); V.DV.DELIVERY['capacity'] = 'mix'; trace_ok = []
for want in V.MIX:
    s, h = next((s, h) for s, h in TRAIN if V.MIX_REGIME[(int(s), float(h))] == want)
    e, *_ = sc.env(s, h); own = np.asarray(e._trace).copy(); got = V.apply_capacity(e, s, h, e.n_agents); tr = np.asarray(e._trace)
    trace_ok.append(got == want and (np.array_equal(tr, own) if want == 'iid' else bool((tr == int(want[5:])).all())))
    print(want, (s, h), 'trace values', sorted(set(tr.ravel().tolist()))[:8], flush=True)
logMB = (OUT / 'MB' / 'log.jsonl').read_text()
checks = dict(return_codes=rc == [0] * 7, I10_eq_I9=same_ck(OUT / 'I10', OUT / 'I9') and records(OUT / 'I10') == records(OUT / 'I9'),
              K10_eq_K9=same_ck(OUT / 'K10', OUT / 'K9') and records(OUT / 'K10') == records(OUT / 'K9'),
              MB_resumed_at_3='"from_it": 3' in logMB, MB_eq_M=same_ck(OUT / 'M', OUT / 'MB') and records(OUT / 'M') == records(OUT / 'MB'),
              M_differs_from_iid_and_const1=not same_ck(OUT / 'M', OUT / 'I10') and not same_ck(OUT / 'M', OUT / 'K10'),
              regimes_balanced=all(cT[r] == 32 and cS[r] == 4 for r in V.MIX), traces=all(trace_ok),
              config_records_mix=json.loads((OUT / 'M' / 'config.json').read_text()).get('mix_regimes') == list(V.MIX))
print(json.dumps(checks, indent=1)); verdict = 'PASS' if all(checks.values()) else 'FAIL'
(OUT / 'RESULT.json').write_text(json.dumps(dict(checks=checks, verdict=verdict, train_counts=cT, select_counts=cS), indent=1)); print('V10 MIX SELF-CHECK', verdict)
