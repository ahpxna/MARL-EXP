#!/usr/bin/env bash
# E9c queue (04/10/2026 00:4x EDT): waits for the E9b queue (PID $1, optional), then dev checks + controls, then panel wire5/wire4; LANES (default 2, nice 10).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; L=${LANES:-2}
[ -n "${1:-}" ] && caffeinate -w "$1"
echo "e9c queue start $(date)"
{ for s in 0 1 2 3 4 5 6 7 8 9; do echo "DEV $s"; done; for s in 0 1 2 3 4 5 6 7 8 9; do echo "PANEL $s"; done; } | xargs -P $L -L 1 caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_e9c.sh
echo "e9c queue end $(date)"
