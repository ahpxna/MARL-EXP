#!/usr/bin/env bash
# NYC 16x3 queue (02/10/2026 22:4x EDT; PROTOCOL_E3_NYC16X3_20261002.md): seeds 0-4 in parallel lanes (nice 5), then the report.
# Launched detached (nohup) from the user's terminal so a session exit cannot kill it.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; G=research/marl_budget/e3_nyc16x3_20261002; mkdir -p $G
echo "nyc queue start $(date)"
for s in 0 1 2 3 4; do ( caffeinate -i nice -n 5 bash scripts/RUN_marl_nyc_teacher.sh $s && caffeinate -i nice -n 5 bash scripts/RUN_marl_nyc.sh $s ) > $G/lane_s$s.log 2>&1 & done
wait
echo "nyc lanes done $(date)"; grep -h "FAIL\|REFUSED\|stop" $G/lane_s*.log
[ -f scripts/MARL_e3_nyc_report.py ] && external_envs/runtime/bin/python scripts/MARL_e3_nyc_report.py
external_envs/runtime/bin/python scripts/MARL_e3_fallback_report.py --nets nyc --root research/marl_budget/e3_fallback_20261002 > $G/fallback_nyc_report.txt 2>&1
echo "nyc queue end $(date)"
