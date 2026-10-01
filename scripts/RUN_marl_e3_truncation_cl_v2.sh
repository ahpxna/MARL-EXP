#!/usr/bin/env bash
# Direction (b), legal closed loop v2 (29/09): more episodes (seeds 901-964 x 8/16 = 128) and the fixed-cap blind curve
# (cap 2..7), the receiver proxy, the exact current-step oracle rule (diagnostic) and TMC d=4, on 5 actors; parity
# against the saved closed-loop prefix rows where they exist (901-916).  2 lanes, one thread each, under the watchdog.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
OUT=research/marl_budget/e3_truncation_cl_v2_20260929; mkdir -p "$OUT"; B=research/marl_budget
JOBS=("scratch_s3 $B/e3_scratch_seeds34_20260928/actor_s3 cl_v8_direct" "bc_s3 $B/e3_run_seeds34_20260928/actor_s3 cl_v8_direct"
      "mix_s3 $B/e3_mixactor_20260928/actor_s3 cl_v8_direct" "scratch_rs_s0 $B/e3_scratch_rs_20260928/actor_s0 cl_v3_direct"
      "bc_s0 $B/e3_run_20260928_003858/actor_s0 cl_v3_direct")
lane() {
  local k="$1" n; for ((n = k; n < ${#JOBS[@]}; n += 2)); do
    set -- ${JOBS[$n]}; local tag="$1" A="$2" CL="$3"
    [ -f "$OUT/$tag/manifest.json" ] && { echo "done $tag"; continue; }
    [ -e "$OUT/$tag" ] && mv "$OUT/$tag" "legacy/$(echo "$OUT/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
    echo "launch $tag $(date)"
    "$PY" scripts/run_with_watchdog.py --log "$OUT/$tag.log" --out "$OUT/$tag" --stall 600 --retries 2 -- "$PY" -u scripts/MARL_e3_truncation_closed_loop_v2.py \
      --actor "$A/ckpt_best.pt" --out "$OUT/$tag" --traffic-seeds $(seq 901 964) --headways 8 16 --capacity iid \
      --caps 2 3 4 5 6 7 --proxy --exact-local --proxy-age 40 60 --tmc 4 --parity-rows "$A/$CL/rows.json"
    echo "finished $tag rc=$? $(date)"
  done
}
for k in 0 1; do lane $k & done
wait; echo "truncation closed loop v2 done $(date)"
