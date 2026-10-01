#!/usr/bin/env bash
# Handoff F2-B: multi-class response head (selector v5), with and without the bid, 3 init seeds; diagnostic v2.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python
for A in "$@"; do
  O="$A/selectors_v5"; PIDS=""
  for s in 0 1 2; do for v in "multi_bid:--bid --resp-multi" "multi_nobid:--resp-multi"; do N=${v%%:*}; FL=${v#*:}
    [ -f "$O/job_${N}_s$s.json" ] || { $PY -u scripts/MARL_e3_selector_train_v5.py --train "$A/labels_train_*" --select "$A/labels_select" --dev "$A/labels_dev" \
        --out "$O" --name $N $FL --seed $s --epochs 40 > "$A/v5_${N}_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
  done; done
  for p in $PIDS; do wait $p; done
  $PY scripts/MARL_e3_selector_diag_v2.py --actor-dir "$A" --selectors selectors_v5 --out "$A/selectors_v5_diag.json" > "$A/selectors_v5_diag.txt" 2>&1
  echo "== $A"; cat "$A/selectors_v5_diag.txt"; grep -h "multi head" "$A"/v5_*.log
done
