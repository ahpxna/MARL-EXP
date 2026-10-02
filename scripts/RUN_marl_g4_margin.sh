#!/usr/bin/env bash
# PROTOCOL_E3_G4_REPLICATION_ADDENDUM1_20261001.md: teacher-margin probes on the 4x4 development episodes, all seeds in parallel,
# after the replication chain.  Usage: bash scripts/RUN_marl_g4_margin.sh
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=research/marl_budget/e3_grid4x4_20260930/actors; E=research/marl_budget/e3_g4_replication_20261001
WR="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
for s in 0 1 2 3 4 5 6 7 8 9; do
  [ -f "$E/Rdev_s${s}_low/manifest.json" ] || { echo "skip MG_s$s (no Rdev)"; continue; }
  [ -f "$E/MG_s$s/manifest.json" ] && continue
  [ -e "$E/MG_s$s" ] && mv "$E/MG_s$s" "legacy/g4rep_MG_s${s}_partial_$(date +%Y%m%d_%H%M%S)"
  "$PY" scripts/run_with_watchdog.py --log "$E/MG_s$s.log" --out "$E/MG_s$s" --stall 900 --retries 3 -- "$PY" -u $WR scripts/MARL_e3_teacher_margin_probe.py \
    --relay "$A/relayCage_st_s$s/ckpt_best.pt" --teacher "$A/set_full_s$s/ckpt_best.pt" --parity "$E/Rdev_s${s}_low/rows.json" --out "$E/MG_s$s" &
done
wait; echo "g4 margin done $(date)"
