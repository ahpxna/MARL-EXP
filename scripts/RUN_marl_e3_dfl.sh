#!/usr/bin/env bash
# PROTOCOL_E3_DFL_20260928.md with Amendment 1 (20:08): decision loss vs value regression on the same actor, labels,
# inputs (bid + response head), network, optimiser and epochs, with EQUAL tuning.  Per actor, each stage skipped when
# complete:
#   1. selector v6, 3 arms x init seeds 0,1,2, every job over lr in {1e-3, 3e-4, 3e-3} (chosen on SELECT; ties -> 1e-3):
#        legal_bid_resp_mse      --loss mse       (v3 MSE, every candidate)
#        legal_bid_resp_msefeas  --loss mse_feas  (MSE, feasible set)
#        legal_bid_resp_dfl      --loss dfl       (expected gain, T = 1 fixed)
#      = 27 fits per actor, 9 processes;
#   2. self-check: the lr = 1e-3 sub-run of legal_bid_resp_mse s0 must reproduce the v3 job legal_bid_resp_s0
#      (dev_chosen, select_metric, best_epoch, tau) -- otherwise the runner stops;
#   3. MARL_e3_dfl_decision.py on labels_dev (--primary for the first actor only), and on dense/labels_dev when COMPLETE
#      (secondary; same 8 seeds);
#   4. selector diagnostic v3 on selectors_v6.
# Usage: bash scripts/RUN_marl_e3_dfl.sh <primary actor dir> [<secondary actor dir>...]
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python
PROTO=research/marl_budget/PROTOCOL_E3_DFL_20260928.md; FIRST=1; LRS="0.001 0.0003 0.003"
for A in "$@"; do
  bash scripts/e3_writers_check.sh "$A/selectors_v6" > /dev/null || { echo "refusing: live writer on $A/selectors_v6"; exit 3; }
  echo "DFL $A protocol sha256 $(shasum -a 256 $PROTO | cut -d' ' -f1) trainer sha256 $(shasum -a 256 scripts/MARL_e3_selector_train_v6.py | cut -d' ' -f1) $(date)" | tee -a "$A/dfl_chain.log"
  O="$A/selectors_v6"; PIDS=""; COMMON=(--train "$A/labels_train_*" --select "$A/labels_select" --dev "$A/labels_dev" --out "$O" --bid --resp --epochs 40 --lrs $LRS)
  for s in 0 1 2; do
    for v in "legal_bid_resp_mse:mse" "legal_bid_resp_msefeas:mse_feas" "legal_bid_resp_dfl:dfl"; do
      N=${v%%:*}; LOSS=${v#*:}
      [ -f "$O/job_${N}_s$s.json" ] || { $PY -u scripts/MARL_e3_selector_train_v6.py "${COMMON[@]}" --name $N --loss $LOSS --temps 1.0 --seed $s > "$A/v6_${N}_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
    done
  done
  rc=0; for p in $PIDS; do wait $p || rc=$?; done; [ $rc = 0 ] || { echo "a v6 training job failed ($rc)" | tee -a "$A/dfl_chain.log"; exit $rc; }
  python3 - "$A" <<'EOF' | tee -a "$A/dfl_chain.log"
import json, sys
A = sys.argv[1]
v3 = json.load(open(f'{A}/selectors_v3/job_legal_bid_resp_s0.json')); v6 = json.load(open(f'{A}/selectors_v6/job_legal_bid_resp_mse_s0.json'))
c = v6['per_config']['lr=0.001']
chk = dict(dev_chosen=v3['results']['direct']['dev_chosen'] == c['dev_chosen'], select_metric=abs(v3['select_metric'] - c['select_metric']) < 1e-9,
           best_epoch=v3['best_epoch'] == c['best_epoch'], tau=v3['results']['direct']['tau'] == c['tau'])
print(f'reproduction self-check (v6 --loss mse, lr 1e-3 sub-run, seed 0, vs v3): {chk}')
if not all(chk.values()):
    sys.exit('SELF-CHECK FAIL: v6 MSE-all at lr 1e-3 does not reproduce v3; the comparison would not isolate what it claims')
EOF
  P=""; [ $FIRST = 1 ] && P="--primary"
  $PY -u scripts/MARL_e3_dfl_decision.py --actor-dir "$A" $P --out "$A/dfl_decision_dev.json" 2>&1 | tee "$A/dfl_decision_dev.txt"
  if [ -f "$A/dense/labels_dev/manifest.json" ]; then
    $PY -u scripts/MARL_e3_dfl_decision.py --actor-dir "$A" --labels "$A/dense/labels_dev" --out "$A/dfl_decision_dense_dev.json" 2>&1 | tee "$A/dfl_decision_dense_dev.txt"
  fi
  bash scripts/RUN_marl_e3_diag_v3.sh "$A" selectors_v6
  FIRST=0; echo "DFL done $A $(date)" | tee -a "$A/dfl_chain.log"
done
