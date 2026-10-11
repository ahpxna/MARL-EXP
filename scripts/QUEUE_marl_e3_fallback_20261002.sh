#!/usr/bin/env bash
# Fallback queue (02/10/2026 22:5x EDT; PROTOCOL_E3_SUPPORT_FALLBACK_20261002.md + Amendment 1): 5 lanes (nice 10), lane i =
# 3x3 seed i, then 4x4 seeds i and i+5; then the report and a dashboard rebuild.  Launched detached (nohup).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; F=research/marl_budget/e3_fallback_20261002; mkdir -p $F
echo "fallback queue start $(date)"
for i in 0 1 2 3 4; do ( caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_fallback.sh 3x3 $i; caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_fallback.sh 4x4 $i $((i + 5)) ) > $F/lane$i.log 2>&1 & done
wait
echo "fallback lanes done $(date)"; grep -h "FAIL\|REFUSED" $F/lane*.log
external_envs/runtime/bin/python scripts/MARL_e3_fallback_report.py --nets 3x3 4x4 > $F/report_stdout.txt 2>&1; tail -20 $F/report_stdout.txt
python3 scripts/DASH_build.py
echo "fallback queue end $(date)"
