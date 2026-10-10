#!/usr/bin/env bash
# P2 nesting panel queue (03/10/2026 18:4x EDT; PROTOCOL_E3_P2_NESTING_20261003.md): LANES parallel jobs (default 3, nice 10), then the report.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; PY=external_envs/runtime/bin/python; L=${LANES:-3}
E=research/marl_budget/e3_p2_nesting_20261003; [ "${SMOKE:-0}" = 1 ] && E=$E/smoke_pipe; mkdir -p $E
if [ "${SMOKE:-0}" = 1 ]; then S="0"; else S="0 1 2 3 4 5 6 7 8 9"; fi
echo "p2 nesting queue start $(date); lanes $L"
{ for s in $S; do echo "R CK1 $s"; echo "Z $s"; echo "R Cage $s"; echo "R MIX $s"; done; } | xargs -P $L -L 1 caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_p2_nesting.sh
grep -h "FAIL\|REFUSED" $E/4x4/*.log 2>/dev/null | head
"$PY" scripts/MARL_e3_p2_nesting_report.py $([ "${SMOKE:-0}" = 1 ] && echo --smoke) > $E/report_stdout.txt 2>&1; tail -25 $E/report_stdout.txt
echo "p2 nesting queue end $(date)"
