#!/usr/bin/env bash
# Auditor's test 2 (29/09): offline learnability of g3 / g1 / delayed by the legal bid+head critic, safe normaliser
# (MARL_e3_selector_train_v7.py), 3 inits per target, every actor with DEV labels, 4 sequential lanes.
# Output <actor>/selectors_v7/job_legal_bid_resp_<target>_s<seed>.json (+ model_*.pt); skipped when present.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python; M=research/marl_budget
one() {
  local A="$M/$1" O="$M/$1/selectors_v7" t s
  mkdir -p "$O"
  for t in g1 delayed g3; do for s in 0 1 2; do
    [ -f "$O/job_legal_bid_resp_${t}_s$s.json" ] && continue
    "$PY" -u scripts/MARL_e3_selector_train_v7.py --train "$A/labels_train_*" --select "$A/labels_select" --dev "$A/labels_dev" --out "$O" \
        --name legal_bid_resp --bid --resp --target $t --seed $s --epochs 40 --threads 2 > "$A/v7_${t}_s$s.log" 2>&1 || echo "FAIL $1 $t s$s"
  done; done
  echo "done $1 $(date)"
}
lane() { for a in "$@"; do one "$a"; done; }
lane e3_scratch_seeds34_20260928/actor_s3 e3_run_20260928_003858/actor_s1 e3_scratch_rs_20260928/actor_s1 &
lane e3_run_seeds34_20260928/actor_s3 e3_run_20260928_003858/actor_s2 e3_scratch_rs_20260928/actor_s2 &
lane e3_scratch_rs_20260928/actor_s0 e3_run_seeds34_20260928/actor_s4 &
lane e3_run_20260928_003858/actor_s0 e3_scratch_rs_20260928/actor_s4 &
wait; echo "v7 learnability all lanes done $(date)"
