#!/usr/bin/env bash
# E9b queue (04/10/2026 00:2x EDT): dev checks then E7-panel decoder runs, LANES (default 2, nice 10).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; L=${LANES:-2}
echo "e9b queue start $(date)"
{ for s in 0 1 2 3 4 5 6 7 8 9; do echo "DEV $s"; done; for s in 0 1 2 3 4 5 6 7 8 9; do echo "PANEL $s"; done; } | xargs -P $L -L 1 caffeinate -i nice -n 10 bash scripts/RUN_marl_e3_e9b.sh
echo "e9b queue end $(date)"
