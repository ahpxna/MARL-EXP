#!/usr/bin/env bash
# NYC 16x3 queue, THROTTLED (03/10/2026 23:1x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003 "NYC"): the producers and per-seed runners of
# QUEUE_marl_nyc_20261002.sh unchanged, but at most TWO seeds at a time (the 22:42 five-lane launch, 13 trainers x 2 threads on
# 10 cores / 16 GB, was killed ~22:58 with 1.6 GB swap).  Teacher s1 first (resumes in place), then seed pairs, then the reports.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; G=research/marl_budget/e3_nyc16x3_20261002; mkdir -p $G
echo "nyc throttled queue start $(date)"
lane() { ( caffeinate -i nice -n 5 bash scripts/RUN_marl_nyc_teacher.sh $1 && caffeinate -i nice -n 5 bash scripts/RUN_marl_nyc.sh $1 ) >> $G/lane_s$1.log 2>&1; }
caffeinate -i nice -n 5 bash scripts/RUN_marl_nyc_teacher.sh 1 >> $G/lane_s1.log 2>&1
for pair in "0 2" "3 4" "1"; do
  pids=(); for s in $pair; do lane $s & pids+=($!); done
  for p in "${pids[@]}"; do wait "$p"; done; echo "pair $pair done $(date); free $(df -g /System/Volumes/Data | awk 'NR==2{print $4}') GB"
done
echo "nyc lanes done $(date)"; grep -h "FAIL\|REFUSED\|stop" $G/lane_s*.log | tail -5
[ -f scripts/MARL_e3_nyc_report.py ] && external_envs/runtime/bin/python scripts/MARL_e3_nyc_report.py
external_envs/runtime/bin/python scripts/MARL_e3_fallback_report.py --nets nyc --root research/marl_budget/e3_fallback_20261002 > $G/fallback_nyc_report.txt 2>&1
echo "nyc throttled queue end $(date)"
