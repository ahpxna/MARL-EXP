#!/usr/bin/env bash
# 128-episode development-panel evals of the seed-3/4 (and fullq4 seed-2) runs of L-154; unfinished checkpoints are skipped,
# so the script is rerun as runs finish.  Watchdog on every eval.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929; SEEDS=$(seq 901 964)
ev() {  # tag actor prog deliveries quant bpp override
  local tag=$1 actor=$2 prog=$3 dels=$4 q=$5 bpp=$6 ov=$7
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  local extra=(); [ "$prog" = v7 ] && extra=(--quant "$q" --byte-capacity "$bpp"); [ -n "$ov" ] && extra+=(--adapter-override "$ov")
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u "scripts/MARL_e3_delivery_eval_$prog.py" --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity iid \
    ${extra[@]+"${extra[@]}"} --traffic-seeds $SEEDS --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
for s in 3 4; do
  ev set_none_s$s set_none_s$s v6 "none" 0 0 ""
  ev set_full_s$s set_full_s$s v6 "full prefix none" 0 0 ""
  ev bb_set_full_s$s set_full_s$s v7 "prefix" 4 3 freshonly
  ev distill_none_s$s distill_none_s$s v6 "none" 0 0 ""
done
ev q4t_s2_bc3_fo set_fullq4_s2 v7 "prefix" 4 3 freshonly
echo "seeds34 evals pass done $(date)"
