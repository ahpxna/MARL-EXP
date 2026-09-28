#!/usr/bin/env bash
# Handoff F3: same-byte bid comparison on learned actors (selector v4): top-2 response bid vs queue bid vs no bid,
# same code/tuning, 3 init seeds, then diagnostic v2.  Usage: bash scripts/RUN_marl_e3_samebyte.sh <actor dir>...
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
  $PY scripts/MARL_e3_selector_diag_v2.py --actor-dir "$A" --selectors selectors_v4 --out "$A/selectors_v4_diag.json" > "$A/selectors_v4_diag.txt" 2>&1
  echo "== $A"; cat "$A/selectors_v4_diag.txt"
done
