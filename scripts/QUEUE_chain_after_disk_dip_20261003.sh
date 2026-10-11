#!/usr/bin/env bash
# Relaunch after the 03/10/2026 03:12 EDT disk dip (swap growth took free space below the 15 GB guard; every launcher refused).
# Written 03:4x (wake 2).  Everything is resumable: finished items are skipped.  Runs the queues ONE AFTER ANOTHER (fallback ->
# age emulation -> NYC) instead of in parallel, so that memory / swap stay lower; test D's lanes 0,1,2,4 are still running and
# its lane 3 (seeds 3, 8) is relaunched in parallel by the second part.  The logs the refused runs wrote are archived first.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; M=research/marl_budget; ts=$(date +%Y%m%d_%H%M%S)
if [ "${1:-}" != d3 ]; then
L=legacy/disk_dip_refused_logs_$ts; mkdir -p $L/fallback $L/emulation $L/nyc
mv $M/e3_fallback_20261002/lane*.log $M/e3_fallback_20261002/queue.log $M/e3_fallback_20261002/report_stdout.txt $L/fallback/ 2>/dev/null
mv $M/e3_age_emulation_20261003/lane*.log $M/e3_age_emulation_20261003/queue.log $M/e3_age_emulation_20261003/report.txt \
   $M/e3_age_emulation_20261003/report_stdout.txt $L/emulation/ 2>/dev/null
mv $M/e3_nyc16x3_20261002/lane_s*.log $M/e3_nyc16x3_20261002/queue_after_fb.log $M/e3_nyc16x3_20261002/fallback_nyc_report.txt $L/nyc/ 2>/dev/null
echo "archived refused logs to $L $(date); free $(df -g /System/Volumes/Data | awk 'NR==2{print $4}') GB"
fi
if [ "${1:-}" = d3 ]; then
  echo "D lane 3 relaunch $(date)"
  caffeinate -i bash scripts/RUN_marl_g4_mix.sh 3 8 >> $M/e3_g4_mix_lane3_8.log 2>&1
  echo "D lane 3 done $(date); waiting for the D queue (PID 33890)"
  caffeinate -w 33890
  [ -f $M/e3_mixq_D_report_20261002.txt ] && mv $M/e3_mixq_D_report_20261002.txt legacy/e3_mixq_D_report_20261002_without_lane3_$ts.txt
  external_envs/runtime/bin/python scripts/MARL_e3_mixq_report.py --test D
  python3 scripts/DASH_build.py
  echo "D report rerun $(date)"
  exit 0
fi
echo "chain: fallback $(date)"; bash scripts/QUEUE_marl_e3_fallback_20261002.sh > $M/e3_fallback_20261002/queue.log 2>&1
echo "chain: age emulation $(date)"; bash scripts/QUEUE_marl_e3_age_emulation_20261003.sh > $M/e3_age_emulation_20261003/queue.log 2>&1
echo "chain: nyc $(date)"; bash scripts/QUEUE_marl_nyc_20261002.sh > $M/e3_nyc16x3_20261002/queue_after_chain.log 2>&1
echo "chain end $(date)"
