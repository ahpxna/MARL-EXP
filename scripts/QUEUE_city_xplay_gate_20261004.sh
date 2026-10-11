#!/usr/bin/env bash
# B4F (research/city_sim/PROTOCOL_CITY_FLEET_GATE_20261004.md): 13 lights x L-ACT_0..3 x gates fallback / clip, PYTHONHASHSEED=0, LANES (default 2).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; L=${LANES:-2}; PY=external_envs/city_runtime/bin/python; O=research/city_sim/xplay_gate_20261004
mkdir -p "$O" "$O/tmp"; export PYTHONHASHSEED=0 XPLAY_TMP="$ROOT/$O/tmp"; echo "gate queue start $(date)"
for g in fallback clip; do for lt in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3 RL-C50:0 RL-C50:1 RL-C50:2 RL-C50:3 RL-J:0 RL-J:1 RL-J:2 RL-J:3; do
  for f in L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3; do echo "$lt $f $g"; done; done; done |
  xargs -P "$L" -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_xplay_gate.py --light "$0" --fleet "$1" --gate "$2" --out '"$O"' >> '"$O"'/run.log 2>&1 || echo "FAIL $0 $1 $2"'
echo "gate queue end $(date)"
