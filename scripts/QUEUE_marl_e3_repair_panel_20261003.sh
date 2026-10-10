#!/usr/bin/env bash
# Repair-panel queue (03/10/2026 18:3x EDT; PROTOCOL_E3_REPAIR_PANEL_20261003.md).  LANES parallel jobs (default 7, nice 10):
# phase A calibrations + Z; phase B the 120 panel cells (CK1, Cage, MIX); main report; phase C the corrected-FB_Mq reruns on every
# cell of 4901 / 4801 and their report; a dedupe pass (hard links of identical scenario files in FINISHED runs, nothing deleted)
# when free disk < 25 GB.  SMOKE=1: seed 0 only, traffic 9001-9002 (phase C on 2 traffic seeds), through both reports.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; PY=external_envs/runtime/bin/python
E=research/marl_budget/e3_repair_panel_20261003; [ "${SMOKE:-0}" = 1 ] && E=$E/smoke_pipe; mkdir -p $E; L=${LANES:-7}
if [ "${SMOKE:-0}" = 1 ]; then S="0"; S3="0"; else S="0 1 2 3 4 5 6 7 8 9"; S3="0 1 2 3 4"; fi
run() { xargs -P $L -L 1 caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_repair_panel.sh; }
echo "repair panel queue start $(date); lanes $L; free $(df -g /System/Volumes/Data | awk 'NR==2{print $4}') GB"
{ for s in $S; do echo "Z $s"; echo "DET4 CK1 $s"; echo "DET4 Cage $s"; done; } | run
echo "phase A done $(date)"
{ for s in $S; do for K in 0 1 2 3; do echo "C4 CK1 $s $K"; echo "C4 Cage $s $K"; done; done; for s in $S; do for K in 0 1 2 3; do echo "C4 MIX $s $K"; done; done; } | run
echo "phase B done $(date)"; grep -h "FAIL\|REFUSED" $E/4x4/*.log 2>/dev/null | head
SMOKEFLAG=$([ "${SMOKE:-0}" = 1 ] && echo --smoke)
"$PY" scripts/MARL_e3_repair_panel_report.py $SMOKEFLAG > $E/report_stdout.txt 2>&1; tail -40 $E/report_stdout.txt
{ for s in $S3; do echo "DET3 CK1 $s"; echo "DET3 Cage $s"; done; } | run
{ for s in $S; do for K in 0 1 2 3; do echo "RR4 CK1 $s $K"; echo "RR4 Cage $s $K"; done; done; for s in $S3; do for K in 0 1 2 3; do echo "RR3 CK1 $s $K"; echo "RR3 Cage $s $K"; done; done; } | run
echo "phase C done $(date)"
"$PY" scripts/MARL_e3_repair_panel_report.py $SMOKEFLAG --rerun > $E/rerun_report_stdout.txt 2>&1; tail -30 $E/rerun_report_stdout.txt
f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
[ "${f:-0}" -lt 25 ] && nice -n 15 "$PY" -u scripts/UTIL_dedupe_hardlink.py --log research/marl_budget/dedupe_hardlink_20261003.jsonl research/marl_budget legacy | tail -1
echo "repair panel queue end $(date)"
