#!/usr/bin/env bash
# 128-episode evaluations after the 02:41 alarm (ledger L-149), development panel 901-964 x 8/16, watchdog on every eval.
# Usage: bash RUN_marl_e3_evals_0241.sh A|B   (two lanes)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929; SEEDS=$(seq 901 964)
ev() {  # tag actor eval deliveries quant bpp override
  local tag=$1 actor=$2 prog=$3 dels=$4 q=$5 bpp=$6 ov=$7
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  local extra=(); [ "$prog" = v7 ] && extra=(--quant "$q" --byte-capacity "$bpp"); [ -n "$ov" ] && extra+=(--adapter-override "$ov")
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u "scripts/MARL_e3_delivery_eval_$prog.py" --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity iid \
    ${extra[@]+"${extra[@]}"} --traffic-seeds $SEEDS --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
case "$1" in
  A) ev distill_none_fromnone_s0 distill_none_fromnone_s0 v6 "none" 0 0 ""
     ev distill_none_fromprefix_s0 distill_none_fromprefix_s0 v6 "none" 0 0 ""
     ev set_none_s0_cont2500 set_none_s0_cont2500 v6 "none" 0 0 ""
     ev set_none_s2 set_none_s2 v6 "none prefix" 0 0 ""
     ev set_fresh_s2 set_fresh_s2 v6 "prefix cap4 none" 0 0 ""
     ev set_fresh_s3 set_fresh_s3 v6 "prefix cap4 none" 0 0 "";;
  B) ev q4t_s1_bc3_fo set_fullq4_s1 v7 "prefix" 4 3 freshonly
     ev q4t_s1_full set_fullq4_s1 v7 "full none" 4 0 ""
     ev set_full_s2 set_full_s2 v6 "full prefix none" 0 0 ""
     ev bb_set_full_s2 set_full_s2 v7 "prefix" 4 3 freshonly;;
esac
echo "lane $1 done $(date)"
