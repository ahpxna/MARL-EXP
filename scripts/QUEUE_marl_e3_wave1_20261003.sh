#!/usr/bin/env bash
# Wave 1 queue (03/10/2026 23:3x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003): LANES jobs (default 3, nice 10): E6 closed loop -> E11 training
# -> E11 evaluation -> E3 panel -> report.  Runs next to the throttled NYC queue.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; PY=external_envs/runtime/bin/python; L=${LANES:-3}
E=research/marl_budget/e3_wave_20261003; [ "${SMOKE:-0}" = 1 ] && E=$E/smoke_pipe; mkdir -p $E
if [ "${SMOKE:-0}" = 1 ]; then S10="0"; S2="0"; BUD="8 16"; else S10="0 1 2 3 4 5 6 7 8 9"; S2="0 1"; BUD="8 16 40 80"; fi; T="SCRATCH_NEW SCRATCH_MIX SCRATCH_MIX_T"
run() { xargs -P $L -L 1 caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_wave1.sh; }
echo "wave1 queue start $(date); lanes $L"
{ for s in $S10; do echo "E6C $s"; done; for s in $S2; do echo "E11Z $s"; for t in $T; do echo "E11T $t $s"; done; done; } | run
{ for s in $S2; do for b in $BUD; do for t in $T; do for K in 0 1; do echo "E11E $t $s $b $K"; done; done; done; done; } | run
{ for s in $S10; do echo "E3 $s"; done; } | run
"$PY" scripts/MARL_e3_wave1_report.py $([ "${SMOKE:-0}" = 1 ] && echo --smoke) > $E/report_stdout.txt 2>&1; tail -50 $E/report_stdout.txt
echo "wave1 queue end $(date)"
