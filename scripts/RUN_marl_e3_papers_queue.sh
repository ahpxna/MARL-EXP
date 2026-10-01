#!/usr/bin/env bash
# The papers-prescribed E3 arms (research/marl_budget/PROTOCOL_E3_PAPERS_PRESCRIBED_20260929.md), 29/09 20:1x.
# 4 lanes; each job: train with MARL_e3_actor_train_delivery_v6.py (scratch recipe, seed 0, watchdog with in-place resume),
# then the 128-episode evaluation (MARL_e3_delivery_eval_v5.py, seeds 901-964 x 8/16) and the co-design report.
# Eval-only jobs (training elsewhere) refuse if the checkpoint's run is not COMPLETE.  Skips finished work.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929; mkdir -p "$E"
COMMON="--iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2"
# tag | trainer flags ('-' = eval only) | eval deliveries | capacity process
JOBS=(
  "set_rxq_s0|--set-actor --delivery rxq|rxq prefix|iid"
  "rand_s0|--delivery random|random prefix|iid"
  "fixcap_s0|--delivery prefix --capacity fixed|prefix|fixed"
  "set_rand_s0|--set-actor --delivery random|random prefix|iid"
  "rxq_s0|--delivery rxq|rxq prefix|iid"
  "set_rxold_s0|--set-actor --delivery rxold|rxold prefix|iid"
  "rxold_s0|--delivery rxold|rxold prefix|iid"
  "highcap_s0|--delivery prefix --capacity high|prefix|high"
  "mixrand_s0|--delivery mixrand0.5|prefix random|iid"
  "set_fixcap_s0|--set-actor --delivery prefix --capacity fixed|prefix|fixed"
  "set_prefix_s0|-|prefix|iid"
  "set_nbr_s0|-|nbr prefix|iid"
  "set_none_s0|-|none|iid"
  "nbrmask_s1|-|nbr prefix|iid"
)
job() {
  IFS='|' read -r tag flags dels cap <<< "$1"
  if [ "$flags" != "-" ]; then
    if [ ! -f "$D/$tag/manifest.json" ]; then
      echo "train $tag $(date)"
      "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v6.py \
        --out "$D/$tag" --seed 0 $COMMON $flags
    fi
  fi
  [ -f "$D/$tag/manifest.json" ] || { echo "REFUSE eval $tag: training not COMPLETE $(date)"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done eval $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag ($dels, capacity $cap) $(date)"
  "$PY" -u scripts/MARL_e3_delivery_eval_v5.py --actors "$tag=$D/$tag/ckpt_best.pt" --deliveries $dels --capacity "$cap" \
    --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" > "$E/$tag.log" 2>&1
  "$PY" scripts/MARL_e3_codesign_report.py --run "$E/$tag" --out "$E/${tag}_report" >> "$E/$tag.log" 2>&1
  echo "finished $tag $(date)"
}
lane() { local k="$1" n; for ((n = k; n < ${#JOBS[@]}; n += 4)); do job "${JOBS[$n]}"; done; }
for k in 0 1 2 3; do lane $k & done
wait; echo "papers queue done $(date)"
