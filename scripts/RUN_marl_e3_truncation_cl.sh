#!/usr/bin/env bash
# Direction (b), legal closed loop (29/09): MARL_e3_truncation_closed_loop.py on the 11 learned actors, the closed-loop
# panel 901-916 x 8/16, iid capacities; rules prefix, blind 0.1-0.5, proxy (+ oracle check), TMC d in {0,1,2,4};
# parity against each actor's saved closed-loop prefix rows.  ONE lane (sequential), one thread, under the watchdog.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
OUT=research/marl_budget/e3_truncation_cl_20260929; mkdir -p "$OUT"; B=research/marl_budget
JOBS=(
  "scratch_s3 $B/e3_scratch_seeds34_20260928/actor_s3 cl_v8_direct"  "bc_s3 $B/e3_run_seeds34_20260928/actor_s3 cl_v8_direct"
  "mix_s3 $B/e3_mixactor_20260928/actor_s3 cl_v8_direct"            "scratch_rs_s0 $B/e3_scratch_rs_20260928/actor_s0 cl_v3_direct"
  "bc_s0 $B/e3_run_20260928_003858/actor_s0 cl_v3_direct"           "scratch_rs_s1 $B/e3_scratch_rs_20260928/actor_s1 cl_v3_direct"
  "bc_s1 $B/e3_run_20260928_003858/actor_s1 cl_v3_direct"           "scratch_rs_s2 $B/e3_scratch_rs_20260928/actor_s2 cl_v3_direct"
  "bc_s2 $B/e3_run_20260928_003858/actor_s2 cl_v3_direct"           "scratch_rs_s4 $B/e3_scratch_rs_20260928/actor_s4 cl_v3_direct"
  "bc_s4 $B/e3_run_seeds34_20260928/actor_s4 cl_v3_direct"
)
for J in "${JOBS[@]}"; do
  set -- $J; tag="$1" A="$2" CL="$3"
  [ -f "$OUT/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$OUT/$tag" ] && mv "$OUT/$tag" "legacy/$(echo "$OUT/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "launch $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$OUT/$tag.log" --out "$OUT/$tag" --stall 600 --retries 2 -- "$PY" -u scripts/MARL_e3_truncation_closed_loop.py \
    --actor "$A/ckpt_best.pt" --out "$OUT/$tag" --traffic-seeds $(seq 901 916) --headways 8 16 --capacity iid \
    --fracs 0.1 0.2 0.3 0.4 0.5 --proxy --oracle-check --tmc 0 1 2 4 --parity-rows "$A/$CL/rows.json"
  echo "finished $tag rc=$? $(date)"
done
echo "truncation closed loop done $(date)"
