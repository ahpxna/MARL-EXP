#!/usr/bin/env bash
# B1 cross-play + B1b hidden-queue sensing (research/city_sim/PROTOCOL_CITY_XPLAY_HCRAWL_20261004.md), 04/10/2026 wake 1.  LANES (default 3).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; L=${LANES:-3}; PY=external_envs/city_runtime/bin/python; O=research/city_sim/xplay_20261004
mkdir -p "$O"; echo "xplay queue start $(date)"
{ for lt in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3 RL-C50:0 RL-C50:1 RL-C50:2 RL-C50:3 RL-J:0 RL-J:1 RL-J:2 RL-J:3; do
    for f in human L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3 L-RLH:0; do echo "$lt $f default"; done; done
  for lt in RL-H:0 RL-H:1 RL-H:2 RL-H:3; do for f in human L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3 L-RLH:0; do echo "$lt $f crawl"; done; done; } |
  xargs -P "$L" -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_xplay.py --light "$0" --fleet "$1" --sense "$2" --out '"$O"' >> '"$O"'/run.log 2>&1 || echo "FAIL $0 $1 $2"'
echo "xplay queue end $(date)"
