#!/usr/bin/env bash
# Route 3: MARL_e3_pair_critic_train.py (legal and privileged-diagnostic arms, 3 inits) on the given actors, 2 lanes.
# Output <actor>/selectors_pair/.  Usage: bash scripts/RUN_marl_e3_pair_critic.sh <actor rel dir>...
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python; M=research/marl_budget
SCR=$M/e3_pair_critic_scenarios_20260929
one() {
  local A="$M/$1" O="$M/$1/selectors_pair" s arm fl
  mkdir -p "$O"
  for arm in legal priv; do fl=""; [ $arm = priv ] && fl="--priv"; for s in 0 1 2; do
    [ -f "$O/job_pair_${arm}_s$s.json" ] && continue
    "$PY" -u scripts/MARL_e3_pair_critic_train.py --train "$A/labels_train_*" --select "$A/labels_select" --dev "$A/labels_dev" --out "$O" \
        --scratch "$SCR/$(echo $1 | tr / _)_${arm}_s$s" $fl --seed $s --epochs 40 --threads 2 > "$A/pair_${arm}_s$s.log" 2>&1 || echo "FAIL $1 $arm s$s"
    tail -1 "$A/pair_${arm}_s$s.log"
  done; done
}
lane() { for a in "$@"; do one "$a"; done; }
N=$#; half=$(( (N + 1) / 2 )); L1=("${@:1:$half}"); L2=("${@:$((half + 1))}")
lane "${L1[@]}" & [ ${#L2[@]} -gt 0 ] && lane "${L2[@]}" &
wait; echo "pair critic done $(date)"
