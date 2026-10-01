#!/usr/bin/env bash
# Selector diagnostic v3 (tie-half pair order accuracy; strict v2 value kept as pair_order_accuracy_strict_v2) for the
# saved checkpoints of one or more selector directories of an actor.  Read-only: no training, no rollouts.
# Handoff MARL_REMAINING_WORK_HANDOFF_20260928_1910 W1 (ledger L-58): every runner that called the retired
# MARL_e3_selector_diag_v2.py entry point now calls this.  Output <actor dir>/<selectors>_diag_v3.{json,txt}; an
# existing JSON is kept (never overwritten); a v2 JSON of the same selectors is left untouched as history.
# Usage: bash scripts/RUN_marl_e3_diag_v3.sh <actor dir> <selectors subdir>...
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A="${1:?actor dir}"; shift
[ $# -gt 0 ] || { echo "usage: $0 <actor dir> <selectors subdir>..."; exit 2; }
for sel in "$@"; do
  ls "$A/$sel"/model_*.pt > /dev/null 2>&1 || { echo "refusing: no checkpoints in $A/$sel"; exit 2; }
  O="$A/${sel}_diag_v3"
  if [ ! -f "$O.json" ]; then
    "$PY" -u scripts/MARL_e3_selector_diag_v3.py --actor-dir "$A" --selectors "$sel" --out "$O.json.tmp" > "$O.txt" 2>&1
    mv "$O.json.tmp" "$O.json"
  fi
  echo "== $A/$sel (selector diagnostic v3, tie-half)"; cat "$O.txt"
done
