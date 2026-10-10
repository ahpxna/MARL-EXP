#!/usr/bin/env bash
# G3 prerequisite (04/10/2026 01:2x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003 E5-G3): FROZEN rerun of the C0 exact tables and panels
# with the current hashed scripts/CITY_c0_testbed.py (C-9: c0_v3's producer is unverifiable).  Three lanes, one light group each.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; export OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
O=research/city_sim/c0_g3_frozen_20261004; mkdir -p "$O"; shasum -a 256 scripts/CITY_c0_testbed.py > "$O/SOURCE.sha256"
nice -n 10 external_envs/runtime/bin/python -u scripts/CITY_c0_testbed.py --out "$O" --panels FT ACT EXT CUT > "$O/panels_main.log" 2>&1 &
nice -n 10 external_envs/runtime/bin/python -u scripts/CITY_c0_testbed.py --out "$O" --panels A1 A2 A3 > "$O/panels_a123.log" 2>&1 &
nice -n 10 external_envs/runtime/bin/python -u scripts/CITY_c0_testbed.py --out "$O" --panels A4 A5 A6 > "$O/panels_a456.log" 2>&1 &
wait; shasum -a 256 scripts/CITY_c0_testbed.py | diff -q - "$O/SOURCE.sha256" > /dev/null && echo "source unchanged" || echo "SOURCE CHANGED DURING RUN"
echo "g3 panels end $(date)"
