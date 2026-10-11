#!/usr/bin/env bash
# L4 green-release guard (research/city_sim/PROTOCOL_CITY_GREEN_GUARD_20261004.md): SELECT 156 configs (seeds 100-104) + TEST 40 configs
# (seeds 200-209), PYTHONHASHSEED=0, LANES (default 4).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; L=${LANES:-4}; PY=external_envs/city_runtime/bin/python
O=research/city_sim/green_guard_20261004; mkdir -p "$O/select" "$O/test" "$O/tmp"; export PYTHONHASHSEED=0 XPLAY_TMP="$ROOT/$O/tmp"; echo "guard queue start $(date)"
{ for g in green+oos none green; do for lt in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3 RL-C50:0 RL-C50:1 RL-C50:2 RL-C50:3 RL-J:0 RL-J:1 RL-J:2 RL-J:3; do
    for f in L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3; do echo "$lt $f $g select 100 101 102 103 104"; done; done; done
  for g in green+oos none; do for lt in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3; do for f in L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3; do
    echo "$lt $f $g test 200 201 202 203 204 205 206 207 208 209"; done; done; done; } |
  xargs -P "$L" -L 1 sh -c 'l=$0 f=$1 g=$2 d=$3; shift 3; nice -n 5 '"$PY"' -u scripts/CITY_xplay_guard.py --light "$l" --fleet "$f" --guard "$g" --seeds "$@" --out '"$O"'/$d >> '"$O"'/run.log 2>&1 || echo "FAIL $l $f $g $d"'
echo "guard queue end $(date)"
