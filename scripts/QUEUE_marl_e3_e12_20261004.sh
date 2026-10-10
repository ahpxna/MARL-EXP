#!/usr/bin/env bash
# E12 queue (04/10/2026 wake 2): actor seeds 0-9, LANES (default 2, nice 10; two-population runs have CPU priority).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; L=${LANES:-2}; echo "e12 queue start $(date)"
seq 0 9 | xargs -P "$L" -I{} sh -c 'nice -n 10 bash scripts/RUN_marl_e3_e12.sh PANEL {} || echo "FAIL PANEL {}"'
echo "e12 queue end $(date)"
