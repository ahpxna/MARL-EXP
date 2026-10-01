#!/usr/bin/env bash
# The DFL round (PROTOCOL_E3_DFL_20260928.md, Amendment 1) REPLICATED with selector v8 (floored normaliser, L-65/L-82):
# 3 arms x inits 0-2 x lr grid {1e-3, 3e-4, 3e-3} (chosen on SELECT), same labels/inputs/network/epochs, into
# <actor>/selectors_v8dfl.  Self-check: the lr 1e-3 sub-run of legal_bid_resp_mse s0 must reproduce the test-1 v8 job
# <actor>/selectors_v8/job_legal_bid_resp_s0.json (same trainer path) where that job exists.  Then
# MARL_e3_dfl_decision_v8.py on labels_dev.  Descriptive replication, not the registered round.
# Usage: bash scripts/RUN_marl_e3_dfl_v8.sh <actor dir> [<actor dir>...]   (one actor at a time, 9 processes)
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python; LRS="0.001 0.0003 0.003"
for A in "$@"; do
  O="$A/selectors_v8dfl"; PIDS=""; COMMON=(--train "$A/labels_train_*" --select "$A/labels_select" --dev "$A/labels_dev" --out "$O" --bid --resp --epochs 40 --lrs $LRS --threads 2)
  for s in 0 1 2; do
    for v in "legal_bid_resp_mse:mse" "legal_bid_resp_msefeas:mse_feas" "legal_bid_resp_dfl:dfl"; do
      N=${v%%:*}; LOSS=${v#*:}
      [ -f "$O/job_${N}_s$s.json" ] || { $PY -u scripts/MARL_e3_selector_train_v8.py "${COMMON[@]}" --name $N --loss $LOSS --temps 1.0 --seed $s > "$A/v8dfl_${N}_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
    done
  done
  rc=0; for p in $PIDS; do wait $p || rc=$?; done; [ $rc = 0 ] || { echo "a v8 DFL training job failed ($rc)"; exit $rc; }
  if [ -f "$A/selectors_v8/job_legal_bid_resp_s0.json" ]; then python3 - "$A" <<'PYEOF'
import json, sys
A = sys.argv[1]
ref = json.load(open(f'{A}/selectors_v8/job_legal_bid_resp_s0.json')); new = json.load(open(f'{A}/selectors_v8dfl/job_legal_bid_resp_mse_s0.json'))
c = new['per_config']['lr=0.001']
chk = dict(dev_chosen=ref['results']['direct']['dev_chosen'] == c['dev_chosen'], select_metric=abs(ref['select_metric'] - c['select_metric']) < 1e-9,
           best_epoch=ref['best_epoch'] == c['best_epoch'])
print(f'reproduction self-check (v8dfl mse lr 1e-3 s0 vs test-1 v8 job): {chk}')
if not all(chk.values()):
    sys.exit('SELF-CHECK FAIL: the v8 DFL round does not reproduce the test-1 v8 job')
PYEOF
  fi
  $PY -u scripts/MARL_e3_dfl_decision_v8.py --actor-dir "$A" --out "$A/dfl_v8_decision_dev.json" 2>&1 | tee "$A/dfl_v8_decision_dev.txt"
  echo "DFL v8 done $A $(date)"
done
