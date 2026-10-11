#!/usr/bin/env bash
# Mixed-fleet pilot queue (03/10/2026 20:2x EDT; PROTOCOL_E3_MIXED_FLEET_20261003.md): LANES jobs (default 3, nice 10), then the report.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; PY=external_envs/runtime/bin/python; L=${LANES:-3}
E=research/marl_budget/e3_mixed_fleet_20261003; [ "${SMOKE:-0}" = 1 ] && E=$E/smoke_pipe; mkdir -p $E
if [ "${SMOKE:-0}" = 1 ]; then SS="0"; else SS="0 1 2 3 4"; fi
echo "mixed fleet queue start $(date); lanes $L"
{ for s in $SS; do echo "MIX $s D"; echo "MIX $s C"; echo "REF $s"; done; } | xargs -P $L -L 1 caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_mixed_fleet.sh
echo "jobs exit status $?"
"$PY" scripts/MARL_e3_mixed_fleet_report.py $([ "${SMOKE:-0}" = 1 ] && echo --smoke) > $E/report_stdout.txt 2>&1; tail -40 $E/report_stdout.txt
echo "mixed fleet queue end $(date)"
