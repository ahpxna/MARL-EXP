#!/usr/bin/env bash
# Learned SchedNet-style scheduling baseline (scripts/MARL_e3_schednet_train.py) for frozen E3 actors that
# passed G1/G2: train 3 init seeds per actor (select split), evaluate each on the E3 pilot panel 901-916,
# report against the same actor's prefix.  Usage: bash scripts/RUN_marl_e3_schednet.sh <run dir> <actor ckpt>...
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
RUN="${1:?run dir}"; shift
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY=external_envs/runtime/bin/python; mkdir -p "$RUN"
n=0
for A in "$@"; do
  for s in 0 1 2; do
    D="$RUN/actor$n/sched_s$s"; mkdir -p "$RUN/actor$n"; echo "$A" > "$RUN/actor$n/ACTOR"
    echo "== actor $A sched seed $s: train $(date)" | tee -a "$RUN/chain.log"
    "$PY" -u scripts/MARL_e3_schednet_train.py --actor "$A" --out "$D" --seed $s --iters ${ITERS:-300} > "$D.log" 2>&1
    "$PY" -u scripts/MARL_e3_schednet_train.py --mode eval --actor "$A" --ckpt "$D/ckpt_best.pt" --out "${D}_eval" > "${D}_eval.log" 2>&1
    python3 scripts/MARL_hetero_closed_loop_report.py "${D}_eval" --control prefix > "${D}_eval/full_endpoints.txt"
    grep -A1 "== schednet" "${D}_eval/full_endpoints.txt" | tee -a "$RUN/chain.log"
  done
  n=$((n + 1))
done
echo "CHAIN COMPLETE $(date)" | tee -a "$RUN/chain.log"
