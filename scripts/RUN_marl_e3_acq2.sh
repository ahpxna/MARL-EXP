#!/usr/bin/env bash
# Acquisition ablation v2 (legal gap bins, provenance) for actor dirs: 4 strategies x 3 seeds, then diagnostic v2.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python
for A in "$@"; do
  PIDS=""
  for st in singleton uniform targeted full; do for s in 0 1 2; do
    [ -f "$A/acquisition_v2/job_acq2_${st}_s$s.json" ] || { $PY -u scripts/MARL_e3_acquisition_v2.py --train "$A/labels_train_*" --select "$A/labels_select" \
        --dev "$A/labels_dev" --out "$A/acquisition_v2" --strategy $st --seed $s > "$A/acq2_${st}_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
  done; done
  for p in $PIDS; do wait $p; done
  $PY scripts/MARL_e3_selector_diag_v2.py --actor-dir "$A" --selectors acquisition_v2 --out "$A/acquisition_v2_diag.json" > "$A/acquisition_v2_diag.txt" 2>&1
  echo "== $A"; cat "$A/acquisition_v2_diag.txt"
done
