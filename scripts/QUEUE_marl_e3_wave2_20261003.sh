#!/usr/bin/env bash
# Wave 2a queue (03/10/2026 23:4x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003 E8 / E9 / E7): LANES jobs (default 3, nice 10).
# Calibrations + FT / PCT-old training + E9 replay -> E7 references + mixed cells -> E8 cells -> report.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; PY=external_envs/runtime/bin/python; L=${LANES:-3}
E=research/marl_budget/e3_wave_20261003/w2; [ "${SMOKE:-0}" = 1 ] && E=research/marl_budget/e3_wave_20261003/smoke_pipe/w2; mkdir -p $E
if [ "${SMOKE:-0}" = 1 ]; then S="0"; else S="0 1 2 3 4 5 6 7 8 9"; fi
run() { xargs -P $L -L 1 caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_wave2.sh; }
echo "wave2a queue start $(date); lanes $L"
{ for s in $S; do echo "DET CK1 $s"; echo "DET Cage $s"; echo "FTOLD FTMIX $s"; echo "FTOLD PCT $s"; echo "E9R $s"; echo "E8Z $s"; done; } | run
{ for s in $S; do echo "REF $s"; echo "MIX $s D"; echo "MIX $s C"; done; } | run
"$PY" scripts/MARL_e3_wave2_report.py --part e7 $([ "${SMOKE:-0}" = 1 ] && echo --smoke) > $E/report_e7_stdout.txt 2>&1; tail -40 $E/report_e7_stdout.txt
{ for s in $S; do for r in CK1 Cage; do for K in 1 0 2 3; do echo "E8 $r $s $K"; done; done; done; } | run
"$PY" scripts/MARL_e3_wave2_report.py --part e8 $([ "${SMOKE:-0}" = 1 ] && echo --smoke) > $E/report_e8_stdout.txt 2>&1; tail -30 $E/report_e8_stdout.txt
echo "wave2a queue end $(date)"
