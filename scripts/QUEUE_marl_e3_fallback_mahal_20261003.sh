#!/usr/bin/env bash
# Mahalanobis-gate queue (03/10/2026 13:0x EDT; PROTOCOL_E3_FALLBACK_MAHAL_20261003.md): 5 lanes (nice 10), lane i = 3x3 seed i, then 4x4
# seeds i and i+5; a dedupe pass (hard links of identical scenario files in FINISHED runs, nothing deleted) every 30 min while
# free disk < 25 GB (the precedent of QUEUE_marl_d_resume_20261002.sh); then the report and a dashboard rebuild.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; E=research/marl_budget/e3_fallback_mahal_20261003; mkdir -p $E
PY=external_envs/runtime/bin/python; echo "fallback mahal queue start $(date)"; pids=()
for i in 0 1 2 3 4; do ( caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_fallback_mahal.sh 3x3 $i; caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_fallback_mahal.sh 4x4 $i $((i + 5)) ) > $E/lane$i.log 2>&1 & pids+=($!); done
( while kill -0 "${pids[0]}" 2>/dev/null || kill -0 "${pids[1]}" 2>/dev/null || kill -0 "${pids[2]}" 2>/dev/null || kill -0 "${pids[3]}" 2>/dev/null || kill -0 "${pids[4]}" 2>/dev/null; do
    sleep 1800; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
    [ "${f:-0}" -lt 25 ] && { echo "dedupe $(date) free $f GB"; nice -n 15 "$PY" -u scripts/UTIL_dedupe_hardlink.py --log research/marl_budget/dedupe_hardlink_20261003.jsonl research/marl_budget legacy | tail -1; }; done ) &
for p in "${pids[@]}"; do wait "$p"; done
echo "fallback mahal lanes done $(date)"; grep -h "FAIL\|REFUSED" $E/lane*.log
"$PY" scripts/MARL_e3_fallback_mahal_report.py > $E/report_stdout.txt 2>&1; tail -20 $E/report_stdout.txt
python3 scripts/DASH_build.py
echo "fallback mahal queue end $(date)"
