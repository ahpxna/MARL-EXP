#!/usr/bin/env bash
# Adaptation pilot queue (03/10/2026 19:1x EDT; PROTOCOL_E3_ADAPT_PILOT_20261003.md): LANES jobs (default 3, nice 10):
# Z + training (7 arms x 2 seeds) -> BCWI checkpoints -> evaluation of every checkpoint on K = 0 (new) and K = 1 (old) -> report.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; PY=external_envs/runtime/bin/python; L=${LANES:-3}
E=research/marl_budget/e3_adapt_pilot_20261003; [ "${SMOKE:-0}" = 1 ] && E=$E/smoke_pipe; mkdir -p $E
if [ "${SMOKE:-0}" = 1 ]; then SS="0"; BUD="8 16"; else SS="0 1"; BUD="8 16 40 80"; fi; ARMS="FTNEW FTMIX PCT PAIRED A0 A1 A2"; AL="0.25 0.5 0.75"
run() { xargs -P $L -L 1 caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_adapt_pilot.sh; }
echo "adapt pilot queue start $(date); lanes $L"
{ for s in $SS; do echo "Z $s"; for r in $ARMS; do echo "T $r $s"; done; done; } | run
{ for s in $SS; do for b in $BUD; do for al in $AL; do echo "I $s $b $al"; done; done; done; } | run
{ for s in $SS; do for K in 0 1; do echo "E PARENT $s 0 $K"; for b in $BUD; do for r in $ARMS; do echo "E $r $s $b $K"; done; for al in $AL; do echo "E BCWI$al $s $b $K"; done; done; done; done; } | run
grep -h "FAIL\|REFUSED" $E/*.log 2>/dev/null | head
"$PY" scripts/MARL_e3_adapt_pilot_report.py $([ "${SMOKE:-0}" = 1 ] && echo --smoke) > $E/report_stdout.txt 2>&1; tail -40 $E/report_stdout.txt
echo "adapt pilot queue end $(date)"
