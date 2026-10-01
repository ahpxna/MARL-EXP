#!/usr/bin/env bash
# Step-3 audit diagnostic: legal vs PRIVILEGED (joint actions of candidate and prefix) evaluators on the same labels,
# selector v3, 3 init seeds; then diagnostic v2 on all of them.  Usage: bash scripts/RUN_marl_e3_priv_diag.sh <actor dir>...
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python
for A in "$@"; do
  O="$A/selectors_v3"; PIDS=""
  for s in 0 1 2; do
    for v in "legal_bid_resp:--bid --resp" "priv_bid_resp:--bid --resp --priv-joint" "priv_only:--priv-joint"; do
      N=${v%%:*}; FL=${v#*:}
      [ -f "$O/job_${N}_s$s.json" ] || { $PY -u scripts/MARL_e3_selector_train_v3.py --train "$A/labels_train_*" --select "$A/labels_select" --dev "$A/labels_dev" \
          --out "$O" --name $N $FL --seed $s --epochs 40 > "$A/v3_${N}_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
    done
  done
  for p in $PIDS; do wait $p; done
  $PY scripts/MARL_e3_selector_diag_v2.py --actor-dir "$A" --selectors selectors_v3 --out "$A/selectors_v3_diag.json" > "$A/selectors_v3_diag.txt" 2>&1
  echo "== $A"; cat "$A/selectors_v3_diag.txt"
done
