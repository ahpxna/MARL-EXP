#!/usr/bin/env python3
"""SELF-CHECK of MARL_e3_actor_distill_v11.py (02/10/2026 15:2x; PROTOCOL_E3_MIX2_20261002.md).  Tiny configuration as
TEST_marl_distill_v10_mix (6 iterations, 2 episodes per iteration, buffer 3, evaluation every 3, 1 thread):
  V10 / V11   v10 --capacity mix vs v11 --capacity mix with the default regimes (must be identical: weights and logs)
  M2          v11 --capacity mix --mix-regimes iid,const1 (must differ from V11; config records the two regimes)
  regimes     _mix_regimes(('iid', 'const1')) gives 64 / 64 of TRAIN and 8 / 8 of SELECT.
Usage: TEST_marl_distill_v11_mix2.py <out dir>."""
import json, os, subprocess, sys
from collections import Counter
from pathlib import Path
import torch

ROOT = Path(__file__).resolve().parents[1]; OUT = Path(sys.argv[1]); OUT.mkdir(parents=True, exist_ok=False); sys.path.insert(0, str(ROOT))
PY = str(ROOT / 'external_envs/runtime/bin/python'); D = 'research/marl_budget/e3_delivery_actors_20260929'
BASE = ['--teacher', f'{D}/set_full_s0/ckpt_best.pt', '--student-delivery', 'prefix', '--relay', 'age', '--quant', '4', '--order', 'agefirst',
        '--seed', '0', '--iters', '6', '--eps-per-iter', '2', '--buffer', '3', '--eval-every', '3', '--threads', '1', '--capacity', 'mix']
env = dict(os.environ, CIG_EXTERNAL_RUNTIME_ACTIVE='1', PYTHONDONTWRITEBYTECODE='1', OMP_NUM_THREADS='1')


def run(script, out, extra=()):
    r = subprocess.run([PY, '-u', f'scripts/{script}', *BASE, '--out', str(out), *extra], cwd=ROOT, env=env, capture_output=True, text=True)
    print(f'--- {script} {out.name} {" ".join(extra)} rc={r.returncode}\n' + r.stdout[-300:] + r.stderr[-600:], flush=True)
    return r.returncode


def records(out):
    return {d['it']: (round(d['loss'], 12), d['agree'], d['n'], d.get('select_queue_sum')) for d in map(json.loads, (out / 'log.jsonl').read_text().splitlines()) if 'it' in d}


def same(x, y):
    ok = records(x) == records(y)
    for f in ('ckpt_last.pt', 'ckpt_best.pt'):
        a, b = torch.load(x / f, weights_only=False), torch.load(y / f, weights_only=False)
        ok &= a['it'] == b['it'] and a['select'] == b['select'] and all(torch.equal(a['actor'][k], b['actor'][k]) for k in a['actor'])
    return ok


rc = [run('MARL_e3_actor_distill_v10.py', OUT / 'V10'), run('MARL_e3_actor_distill_v11.py', OUT / 'V11'),
      run('MARL_e3_actor_distill_v11.py', OUT / 'M2', ['--mix-regimes', 'iid,const1'])]
import scripts.MARL_e3_actor_distill_v11 as V
from scripts.MARL_e3_actor_train import TRAIN, SELECT
R = V._mix_regimes(('iid', 'const1')); cT = Counter(R[(int(s), float(h))] for s, h in TRAIN); cS = Counter(R[(int(s), float(h))] for s, h in SELECT)
checks = dict(return_codes=rc == [0, 0, 0], V11_eq_V10=same(OUT / 'V11', OUT / 'V10'), M2_differs=not same(OUT / 'M2', OUT / 'V11'),
              M2_config=json.loads((OUT / 'M2' / 'config.json').read_text()).get('mix_regimes') == ['iid', 'const1'],
              balanced=cT['iid'] == 64 and cT['const1'] == 64 and cS['iid'] == 8 and cS['const1'] == 8)
print(json.dumps(checks, indent=1)); verdict = 'PASS' if all(checks.values()) else 'FAIL'
(OUT / 'RESULT.json').write_text(json.dumps(dict(checks=checks, verdict=verdict), indent=1)); print('V11 SELF-CHECK', verdict)
