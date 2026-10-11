#!/usr/bin/env bash
# B3-X (research/city_sim/PROTOCOL_CITY_COTRAIN_20261004.md): every light x every fleet, PYTHONHASHSEED=0.  Phase 1 (existing checkpoints,
# LANES1 default 3) runs at once; phase 2 waits for the training queue (COTRAIN_PID) and runs with LANES2 (default 8).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; PY=external_envs/city_runtime/bin/python; O=research/city_sim/xplay2_20261004
mkdir -p "$O" "$O/tmp"; export PYTHONHASHSEED=0 XPLAY_TMP="$ROOT/$O/tmp"; echo "xplay2 queue start $(date)"
OLDL="ACT FT RL-H:0 RL-H:1 RL-H:2 RL-H:3 RL-C50:0 RL-C50:1 RL-C50:2 RL-C50:3 RL-J:0 RL-J:1 RL-J:2 RL-J:3"
OLDF="human L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3 L-FT:0 L-FT:1 L-FT:2 L-FT:3 L-RLH:0"
NEWL=""; NEWF="L-RLH:1 L-RLH:2 L-RLH:3"
for arm in SIM-halt ALT-halt SIM-delay; do for k in 0 1 2 3; do NEWL="$NEWL $arm:$k"; NEWF="$NEWF $arm:$k"; done; done
run() { xargs -P "$1" -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_xplay2.py --light "$0" --fleet "$1" --out '"$O"' >> '"$O"'/run.log 2>&1 || echo "FAIL $0 $1"'; }
for l in $OLDL; do for f in $OLDF; do echo "$l $f"; done; done | run "${LANES1:-3}"
echo "phase 1 end $(date)"
[ -n "$COTRAIN_PID" ] && caffeinate -w "$COTRAIN_PID"
echo "training queue gone $(date); checkpoints: $(ls research/city_sim/cotrain_20261004/*.pt | wc -l) (expect 27)"
{ for l in $OLDL $NEWL; do for f in $NEWF; do echo "$l $f"; done; done
  for l in $NEWL; do for f in $OLDF; do echo "$l $f"; done; done; } | run "${LANES2:-8}"
echo "xplay2 queue end $(date)"
