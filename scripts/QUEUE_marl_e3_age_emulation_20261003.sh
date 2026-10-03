#!/usr/bin/env bash
# Age-emulation queue (03/10/2026 03:0x EDT; PROTOCOL_E3_AGE_EMULATION_20261003.md): 5 lanes (nice 10), lane i = 3x3 seed i, then
# 4x4 seeds i and i+5; then the report and a dashboard rebuild.  Launched detached (nohup) after the fallback queue ends.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; E=research/marl_budget/e3_age_emulation_20261003; mkdir -p $E
echo "age emulation queue start $(date)"
for i in 0 1 2 3 4; do ( caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_age_emulation.sh 3x3 $i; caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_age_emulation.sh 4x4 $i $((i + 5)) ) > $E/lane$i.log 2>&1 & done
wait
echo "age emulation lanes done $(date)"; grep -h "FAIL\|REFUSED" $E/lane*.log
external_envs/runtime/bin/python scripts/MARL_e3_age_emulation_report.py > $E/report_stdout.txt 2>&1; tail -20 $E/report_stdout.txt
python3 scripts/DASH_build.py
echo "age emulation queue end $(date)"
