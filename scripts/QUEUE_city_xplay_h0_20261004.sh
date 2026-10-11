#!/usr/bin/env bash
# Addendum A1 of research/city_sim/PROTOCOL_CITY_XPLAY_HCRAWL_20261004.md (04/10/2026 wake 2): the B1/B1b panel with PYTHONHASHSEED=0
# (deterministic) + the jitter envelope (16 Q7b fleet configs under hash seeds 1..4) + a determinism re-run.  LANES (default 3).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; L=${LANES:-3}; PY=external_envs/city_runtime/bin/python
O=research/city_sim/xplay_h0_20261004; J=research/city_sim/xplay_jitter_20261004; mkdir -p "$O" "$J"; echo "xplay h0 queue start $(date)"
{ for lt in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3 RL-C50:0 RL-C50:1 RL-C50:2 RL-C50:3 RL-J:0 RL-J:1 RL-J:2 RL-J:3; do
    for f in human L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3 L-RLH:0; do echo "0 $lt $f default $O"; done; done
  for lt in RL-H:0 RL-H:1 RL-H:2 RL-H:3; do for f in human L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3 L-RLH:0; do echo "0 $lt $f crawl $O"; done; done
  for h in 1 2 3 4; do for t in 0 1 2 3; do for lt in ACT RL-H:$t RL-C50:$t RL-J:$t; do echo "$h $lt L-ACT:$t default $J/h$h"; done; done; done
  echo "0 ACT L-ACT:0 default $J/det0"; echo "0 RL-H:2 L-ACT:1 crawl $J/det0"; } |
  xargs -P "$L" -L 1 sh -c 'PYTHONHASHSEED=$0 nice -n 5 '"$PY"' -u scripts/CITY_xplay.py --light "$1" --fleet "$2" --sense "$3" --out "$4" >> '"$O"'/run.log 2>&1 || echo "FAIL $0 $1 $2 $3 $4"'
echo "xplay h0 queue end $(date)"
