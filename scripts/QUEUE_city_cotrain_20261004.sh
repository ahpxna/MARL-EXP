#!/usr/bin/env bash
# B2 + B3 training (research/city_sim/PROTOCOL_CITY_COTRAIN_20261004.md), 04/10/2026 wake 2.  PYTHONHASHSEED=0.  LANES (default 5).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; L=${LANES:-5}; PY=external_envs/city_runtime/bin/python; O=research/city_sim/cotrain_20261004
mkdir -p "$O"; echo "cotrain queue start $(date)"; export PYTHONHASHSEED=0
{ for k in 0 1 2 3; do echo "ALT-halt_k$k --mode alt --reward halt --light-seed $((1011 + 100 * k)) --fleet-seed $((1013 + 100 * k))"; done
  for k in 0 1 2 3; do echo "SIM-halt_k$k --mode sim --reward halt --light-seed $((1011 + 100 * k)) --fleet-seed $((1013 + 100 * k))"
                       echo "SIM-delay_k$k --mode sim --reward delay --light-seed $((1011 + 100 * k)) --fleet-seed $((1013 + 100 * k))"; done
  for t in 1 2 3; do echo "L-RLH_t$t --mode fleet-vs --light-ckpt research/city_sim/q7b_contract_20261002/RL-H_t$t.pt --fleet-seed $((13 + 100 * t))"; done; } |
  xargs -P "$L" -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_cotrain.py --name "$0" "$@" --out '"$O"' > '"$O"'/"$0".out 2>&1 || echo "FAIL $0"'
echo "cotrain queue end $(date)"
