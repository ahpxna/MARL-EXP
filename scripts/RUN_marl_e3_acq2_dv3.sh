#!/usr/bin/env bash
# dv3 (28/09 19:2x, handoff 19:10 W1, ledger L-58): identical training stage to RUN_marl_e3_acq2.sh (kept unchanged as history); the
# diagnostic is v3 (tie-half pair accuracy) via RUN_marl_e3_diag_v3.sh -> <selectors>_diag_v3.json.  The retired v2
# entry point refuses to run, so RUN_marl_e3_acq2.sh now stops at its diagnostic step.
# Acquisition ablation v2 (legal gap bins, provenance) for actor dirs: 4 strategies x 3 seeds, then diagnostic v3.
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
  bash scripts/RUN_marl_e3_diag_v3.sh "$A" acquisition_v2
done
