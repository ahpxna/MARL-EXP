#!/usr/bin/env bash
# SWEEPER for the 30/09 overnight chain (30/09 23:5x EDT; user 23:5x: "re-run what was lost, make sure it runs tonight";
# ledger L-190).  Waits until every running lane / trigger of the chain has exited, then re-runs the SAME launchers, which
# are idempotent (each training and evaluation is skipped when its manifest.json exists; partial outputs are moved to legacy/,
# never deleted).  Anything that failed after the watchdog's retries (or was skipped because an input was missing) is
# therefore redone, in dependency order: 3x3 lanes -> 4x4 phase 1 -> 4x4 phase 2 -> ten-seed panel -> overnight report.
# Usage: nohup bash scripts/RUN_marl_overnight_sweeper_20260930.sh <pid> [<pid> ...] > research/marl_budget/overnight_sweeper.log 2>&1 &
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
echo "sweeper start $(date); waiting for: $*"
for p in "$@"; do caffeinate -i -w "$p"; done
echo "chain finished $(date); sweeping"
M=research/marl_budget
for k in 0 1 2 3; do bash scripts/RUN_marl_e3_overnight_seeds_20260930.sh $k > $M/overnight_lane_${k}_sweep.log 2>&1 & done; wait
echo "lanes swept $(date)"
for s in 0 1 2 3; do bash scripts/RUN_marl_g4_phase1.sh $s > $M/g4_phase1_s${s}_sweep.log 2>&1 & done; wait
echo "4x4 phase 1 swept $(date)"
for s in 0 1 2 3; do bash scripts/RUN_marl_g4_phase2.sh $s > $M/g4_phase2_s${s}_sweep.log 2>&1 & done; wait
echo "4x4 phase 2 swept $(date)"
bash scripts/RUN_marl_e3_ten_seed_panel.sh 0 > $M/ten_seed_panel_0_sweep.log 2>&1 &
bash scripts/RUN_marl_e3_ten_seed_panel.sh 1 > $M/ten_seed_panel_1_sweep.log 2>&1 &
wait
echo "ten-seed panel swept $(date)"
external_envs/runtime/bin/python scripts/MARL_e3_overnight_report_20260930.py > $M/e3_overnight_report_20260930.log 2>&1
echo "sweeper done $(date)"
