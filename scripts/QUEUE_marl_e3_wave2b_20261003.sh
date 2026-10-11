#!/usr/bin/env bash
# Wave 2b queue (03/10/2026 23:5x EDT): E2 / E10 training (v13) -> evaluation -> report.  LANES default 3, nice 10.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; PY=external_envs/runtime/bin/python; L=${LANES:-3}
E=research/marl_budget/e3_wave_20261003/w2b; [ "${SMOKE:-0}" = 1 ] && E=research/marl_budget/e3_wave_20261003/smoke_pipe/w2b; mkdir -p $E
if [ "${SMOKE:-0}" = 1 ]; then S="0"; LV="1 2"; else S="0 1"; LV="1 2 5 10"; fi; ARMS="SI OP UNI V2S V2D"
run() { xargs -P $L -L 1 caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_wave2b.sh; }
echo "wave2b queue start $(date); lanes $L"
{ for s in $S; do for r in $ARMS; do echo "T $r $s"; done; done; } | run
{ for s in $S; do for r in $ARMS; do for l in $LV; do for K in 0 1; do echo "E $r $s $l $K"; done; done; done; done; } | run
"$PY" scripts/MARL_e3_wave2b_report.py $([ "${SMOKE:-0}" = 1 ] && echo --smoke) > $E/report_stdout.txt 2>&1; tail -40 $E/report_stdout.txt
echo "wave2b queue end $(date)"
