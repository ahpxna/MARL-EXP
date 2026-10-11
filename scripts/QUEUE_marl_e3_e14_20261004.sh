#!/usr/bin/env bash
# E14 queue (04/10/2026 wake 2): confirmation seeds 2-9, one chain per seed (Z, three trainings, eight evaluations), LANES (default 2, nice 10).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; L=${LANES:-2}; echo "e14 queue start $(date)"
chain() { local s=$1 R="bash scripts/RUN_marl_e3_e14.sh"
  $R Z $s; for a in OP FTMIX PCT; do $R T $a $s; done
  for a in CK1 OP FTMIX PCT; do for k in 0 1; do $R E $a $s $k; done; done; echo "e14 seed $s chain done $(date)"; }
export -f chain
seq 2 9 | xargs -P "$L" -I{} nice -n 10 bash -c 'chain {}'
echo "e14 queue end $(date)"
