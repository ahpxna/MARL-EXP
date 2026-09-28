#!/usr/bin/env bash
# E3 frontier and shift (readiness audit P3), for actor dirs that already have selectors:
#   caps +28 +56 +84 +140 (direct, pilot panel 901-916) -> frontier figure;
#   one declared shift at +84: headway 12 (held-out load) and bursty capacities -> report.
# All runs under scripts/run_with_watchdog.py.  Usage: bash scripts/RUN_marl_e3_frontier.sh <actor dir>...
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY=external_envs/runtime/bin/python; WD="$PY scripts/run_with_watchdog.py"; SEEDS="$(seq -s ' ' 901 916)"
for D in "$@"; do
  [ -f "$D/selectors/job_sel_bid_s2.json" ] || { echo "skip $D: selectors missing"; continue; }
  RUNS=""
  for cap in 28 56 84 140; do
    O="$D/frontier_c$cap"; RUNS="$RUNS $O"
    [ -f "$O/manifest.json" ] || $WD --log "$O.log" --out "$O" --stall 1800 -- "$PY" -u scripts/MARL_e3_closed_loop_v2.py --actor "$D/ckpt_best.pt" \
        --selectors "$D/selectors" --names sel_nobid sel_bid --policy direct --cap $cap --out "$O" --traffic-seeds $SEEDS
  done
  "$PY" scripts/MARL_make_e3_frontier.py --runs $RUNS --out "$D/figures" --stem frontier --title "E3 frontier, $(basename $(dirname $D))/$(basename $D), panel 901-916" > "$D/frontier.txt"
  for sh in "12 iid" "8 bursty" "16 bursty"; do
    read -r H C <<< "$sh"; O="$D/shift_h${H}_$C"
    [ -f "$O/manifest.json" ] || $WD --log "$O.log" --out "$O" --stall 1800 -- "$PY" -u scripts/MARL_e3_closed_loop_v2.py --actor "$D/ckpt_best.pt" \
        --selectors "$D/selectors" --names sel_nobid sel_bid --policy direct --cap 84 --headways $H --capacity $C --mp2 --out "$O" --traffic-seeds $SEEDS
    python3 scripts/MARL_hetero_closed_loop_report.py "$O" --control sel_nobid > "$O/full_endpoints.txt"
  done
  echo "frontier+shift done $D $(date)"
done
