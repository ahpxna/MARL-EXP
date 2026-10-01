#!/usr/bin/env bash
# OVERNIGHT seed expansion on the 3x3 grid (30/09 20:1x EDT; user 20:0x: "increase seeds, run the long experiments,
# results by morning"; ledger L-186).  32 jobs, each = train (if not done) + development-panel evaluation, same commands as
# the existing launchers:
#   zrep     distill_none_rep_s<s>  (scripts/MARL_e3_actor_distill.py, seed 100+s; RUN_marl_e3_zero_replicate.sh) + eval v6 none
#   relay6   relay6_st_s<s>         (distill v6, --relay age --quant 4; RUN_marl_e3_ABC_v2.sh student)       + satrot grid
#   b8       relay6B8_st_s<s>       (distill v6, --quant 9008 --codebook field-sensitivity)               + satrot grid
#   clow     relay6Clow_st_s<s>     (distill v6, --quant 4 --capacity low)                                 + satrot grid
# for s = 2..9.  Lane k (0..3) runs jobs k, k+4, k+8, ... in priority order (zrep first, then relay6, b8, clow).
# A run already in progress elsewhere is skipped; partial outputs are moved to legacy/ (never deleted).  Watchdog on every run.
# Usage: nohup bash scripts/RUN_marl_e3_overnight_seeds_20260930.sh <lane> > research/marl_budget/overnight_lane_<lane>.log 2>&1 &
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
lane=$1; D=research/marl_budget/e3_delivery_actors_20260929; C=research/marl_budget/e3_codesign_eval_20260929
R=research/marl_budget/e3_satrot_eval_20260930; M=research/marl_budget; CBS=$M/e3_field_sensitivity_20260930.json
train() {  # tag script args...
  local tag=$1; shift
  [ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  pgrep -f -- "--out $D/$tag " > /dev/null && { echo "in progress elsewhere: $tag"; return 1; }
  [ -e "$D/$tag" ] && mv "$D/$tag" "legacy/${tag}_partial_$(date +%Y%m%d_%H%M%S)"
  [ -e "$D/$tag.log" ] && mv "$D/$tag.log" "legacy/${tag}_partial_$(date +%Y%m%d_%H%M%S).log"
  echo "train $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$D/$tag" || { echo "FAIL $tag"; return 1; }
}
ev() {  # tag actor order capacity deliveries extra-args...
  local tag=$1 actor=$2 order=$3 cap=$4 dels=$5; shift 5
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag (no $actor)"; return 0; }
  [ -f "$R/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$R/$tag" ] && mv "$R/$tag" "legacy/$(echo "$R/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  "$PY" scripts/run_with_watchdog.py --log "$R/$tag.log" --out "$R/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_relay_satrot.py --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity "$cap" \
    --relay age --order "$order" "$@" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$R/$tag" || echo "FAIL $tag"
}
grid() { local a=$1; shift; for o in prefix agefirst; do ev ${a}_${o}_iid $a $o iid "prefix cap4" "$@"; ev ${a}_${o}_low $a $o low "prefix" "$@"; done; }
job() {  # kind seed
  local kind=$1 s=$2
  case $kind in
    zrep) train distill_none_rep_s$s scripts/MARL_e3_actor_distill.py --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery none \
            --seed $((100 + s)) --iters 500 --threads 2 && {
            [ -f "$C/distill_none_rep_s$s/manifest.json" ] || "$PY" scripts/run_with_watchdog.py --log "$C/distill_none_rep_s$s.log" --out "$C/distill_none_rep_s$s" \
              --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_rep_s$s=$D/distill_none_rep_s$s/ckpt_best.pt" \
              --deliveries none --capacity iid --traffic-seeds $(seq 901 964) --headways 8 16 --out "$C/distill_none_rep_s$s"; } ;;
    relay6) train relay6_st_s$s scripts/MARL_e3_actor_distill_v6.py --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age \
            --seed $s --iters 500 --quant 4 && grid relay6_st_s$s --quant 4 ;;
    b8) train relay6B8_st_s$s scripts/MARL_e3_actor_distill_v6.py --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age \
            --seed $s --iters 500 --quant 9008 --codebook "$CBS" && grid relay6B8_st_s$s --quant 9008 --codebook "$CBS" ;;
    clow) train relay6Clow_st_s$s scripts/MARL_e3_actor_distill_v6.py --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age \
            --seed $s --iters 500 --quant 4 --capacity low && grid relay6Clow_st_s$s --quant 4 ;;
  esac
}
jobs=(); for kind in zrep relay6 b8 clow; do for s in 2 3 4 5 6 7 8 9; do jobs+=("$kind $s"); done; done
for ((n = lane; n < ${#jobs[@]}; n += 4)); do echo "=== job ${jobs[$n]} $(date)"; job ${jobs[$n]}; done
echo "overnight lane $lane done $(date)"
