#!/usr/bin/env bash
# Runs CITY_eval4 configurations read from stdin (one argument line each, without --out) with LANES lanes into OUT.
# PYTHONHASHSEED=0, OMP_NUM_THREADS=1; per-vehicle XML in OUT/tmp (removed after each run).  Used by the wave-2 spool jobs.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; OUT=$1; L=${LANES:-4}; PY=external_envs/city_runtime/bin/python
mkdir -p "$OUT/tmp"; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 XPLAY_TMP="$ROOT/$OUT/tmp"
xargs -P "$L" -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_eval4.py "$@" --out '"$OUT"' >> '"$OUT"'/run.log 2>&1 || echo "FAIL $*"' sh
echo "eval4 batch done $(date): $(ls "$OUT"/*.json 2>/dev/null | wc -l) json"
