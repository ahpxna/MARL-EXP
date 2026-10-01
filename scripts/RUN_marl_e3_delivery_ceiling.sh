#!/usr/bin/env bash
# Information ceiling (29/09): evaluate the delivery-trained actors and the 5 scratch prefix actors on the panel
# (901-916 x 8/16) under prefix / full / none / random delivery; parity of every scratch actor's prefix rows.
# Usage: bash scripts/RUN_marl_e3_delivery_ceiling.sh <tag=ckpt> ...   (extra delivery-trained actors to include)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
B=research/marl_budget; OUT=$B/e3_delivery_ceiling_$(date +%Y%m%d_%H%M%S)
"$PY" -u scripts/MARL_e3_delivery_eval.py --out "$OUT" --deliveries prefix full none random \
  --actors scratch_s3=$B/e3_scratch_seeds34_20260928/actor_s3/ckpt_best.pt scratch_rs_s0=$B/e3_scratch_rs_20260928/actor_s0/ckpt_best.pt \
           scratch_rs_s1=$B/e3_scratch_rs_20260928/actor_s1/ckpt_best.pt scratch_rs_s2=$B/e3_scratch_rs_20260928/actor_s2/ckpt_best.pt \
           scratch_rs_s4=$B/e3_scratch_rs_20260928/actor_s4/ckpt_best.pt mix_s3=$B/e3_mixactor_20260928/actor_s3/ckpt_best.pt "$@" \
  --parity scratch_s3=$B/e3_scratch_seeds34_20260928/actor_s3/cl_v8_direct/rows.json scratch_rs_s0=$B/e3_scratch_rs_20260928/actor_s0/cl_v3_direct/rows.json \
           scratch_rs_s1=$B/e3_scratch_rs_20260928/actor_s1/cl_v3_direct/rows.json scratch_rs_s2=$B/e3_scratch_rs_20260928/actor_s2/cl_v3_direct/rows.json \
           scratch_rs_s4=$B/e3_scratch_rs_20260928/actor_s4/cl_v3_direct/rows.json mix_s3=$B/e3_mixactor_20260928/actor_s3/cl_v8_direct/rows.json
