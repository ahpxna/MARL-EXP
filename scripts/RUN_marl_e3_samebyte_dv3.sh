#!/usr/bin/env bash
# dv3 (28/09 19:2x, handoff 19:10 W1, ledger L-58): identical training stage to RUN_marl_e3_samebyte.sh (kept unchanged as history); the
# diagnostic is v3 (tie-half pair accuracy) via RUN_marl_e3_diag_v3.sh -> <selectors>_diag_v3.json.  The retired v2
# entry point refuses to run, so RUN_marl_e3_samebyte.sh now stops at its diagnostic step.
# Handoff F3: same-byte bid comparison on learned actors (selector v4): top-2 response bid vs queue bid vs no bid,
# same code/tuning, 3 init seeds, then diagnostic v3.  Usage: bash scripts/RUN_marl_e3_samebyte_dv3.sh <actor dir>...
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python
for A in "$@"; do
  O="$A/selectors_v4"; PIDS=""
  for s in 0 1 2; do for v in "sb_nobid:" "sb_top2bid:--bid" "sb_queuebid:--qbid"; do N=${v%%:*}; FL=${v#*:}
    [ -f "$O/job_${N}_s$s.json" ] || { $PY -u scripts/MARL_e3_selector_train_v4.py --train "$A/labels_train_*" --select "$A/labels_select" --dev "$A/labels_dev" \
        --out "$O" --name $N $FL --seed $s --epochs 40 > "$A/v4_${N}_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
  done; done
  for p in $PIDS; do wait $p; done
  bash scripts/RUN_marl_e3_diag_v3.sh "$A" selectors_v4
done
