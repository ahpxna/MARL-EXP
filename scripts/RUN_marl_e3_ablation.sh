#!/usr/bin/env bash
# E3 ablation (readiness audit P3): for each actor dir whose continuation labels are complete, train the four
# selector variants x 3 init seeds (MARL_e3_selector_train_v2.py: sel_nobid, sel_bid, sel_resp, sel_bid_resp),
# then closed loop v3 (direct, +84, pilot panel 901-916, MP2 reference), report vs sel_nobid, fig3.
# Usage: bash scripts/RUN_marl_e3_ablation.sh <actor dir>...     SMOKE=1 for tiny settings.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY=external_envs/runtime/bin/python; WD="$PY scripts/run_with_watchdog.py"
if [ "${SMOKE:-0}" = 1 ]; then EP=4; SEEDS="901"; else EP=40; SEEDS="$(seq -s ' ' 901 916)"; fi
for D in "$@"; do
  ok=1; for f in "$D"/labels_select "$D"/labels_dev; do [ -f "$f/manifest.json" ] || ok=0; done
  for f in $(ls -d "$D"/labels_train_[0-9]* | grep -v '\.log$'); do [ -f "$f/manifest.json" ] || ok=0; done
  [ $ok = 1 ] || { echo "skip $D: labels incomplete"; continue; }
  O="$D/selectors_v2"; PIDS=""
  for s in 0 1 2; do
    for v in "sel_nobid:" "sel_bid:--bid" "sel_resp:--resp" "sel_bid_resp:--bid --resp"; do
      N=${v%%:*}; FL=${v#*:}
      [ -f "$O/job_${N}_s$s.json" ] || { "$PY" -u scripts/MARL_e3_selector_train_v2.py --train "$D/labels_train_*" --select "$D/labels_select" \
          --dev "$D/labels_dev" --out "$O" --name $N $FL --seed $s --epochs $EP > "$D/v2_${N}_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
    done
  done
  for p in $PIDS; do wait $p; done
  C="$D/cl_v3_direct"
  [ -f "$C/manifest.json" ] || $WD --log "$C.log" --out "$C" --stall 1800 -- "$PY" -u scripts/MARL_e3_closed_loop_v3.py --actor "$D/ckpt_best.pt" \
      --selectors "$O" --names sel_nobid sel_bid sel_resp sel_bid_resp --policy direct --mp2 --out "$C" --traffic-seeds $SEEDS
  python3 scripts/MARL_hetero_closed_loop_report.py "$C" --control sel_nobid > "$C/full_endpoints.txt"
  "$PY" scripts/MARL_make_fig3_v4.py --run "$C" --out "$D/figures" --stem fig3_ablation --title "E3 ablation, $(basename $(dirname $D))/$(basename $D), panel 901-916" >> "$D/figures.log" 2>&1
  echo "ablation done $D $(date)"
done
