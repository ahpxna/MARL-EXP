#!/usr/bin/env bash
# Follow-up to RUN_marl_e3_ABC_v2.sh (30/09 14:1x EDT; ledger L-173).  Two additions found after that launcher started (it is running,
# so it is not edited):
#   rot   the ROTATING-HEAD grid under the correct 25 B layout: scripts/MARL_e3_delivery_eval_relay_satrot.py (the parallel
#         session's relay eval v3, cap-correct orders from models/marl_delivery_music.py + AgeMirror self-check, with the
#         saturated-age merge of models/marl_relay_v2.py).  Actors: relay_st_s0/s1 (v1-trained), relay6_st_s0/s1 (trained under
#         the prefix order, correct layout), relay6Cage_st_s0/s1 (trained under agefirst, correct layout).  Orders prefix and
#         agefirst; capacities iid (deliveries prefix and cap4) and low (prefix).  --order prefix is row-identical to
#         scripts/MARL_e3_delivery_eval_relay_sat.py (checked 14:1x on seeds 901-902).
#   b12   B-train with key 9012: 20-bit packets, relay packet 16 + 8 x 20 = 176 bits <= 200.  Key 9016 (24-bit packets) gives a
#         212-bit relay packet (26.5 B > 25 B), so relay6B16_* of RUN_marl_e3_ABC_v2.sh is OVER the byte budget: diagnostic only.
#   seeds relay6Cage_st_s2..s9 (correct layout, trained under agefirst), two at a time at OMP 1, each pair then evaluated on the rot grid.
# A run already in progress elsewhere (pgrep on its --out) is skipped, so the chains can overlap safely.
# Development panel 901-964 only.  Watchdog on every run.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; R=research/marl_budget/e3_satrot_eval_20260930; M=research/marl_budget
CBS=$M/e3_field_sensitivity_20260930.json
mkdir -p "$R"
ev() {  # tag actor order capacity deliveries extra-args...
  local tag=$1 actor=$2 order=$3 cap=$4 dels=$5; shift 5
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag (no $actor)"; return 0; }
  [ -f "$R/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  pgrep -f -- "--out $R/$tag --stall" > /dev/null && { echo "in progress elsewhere: $tag"; return 0; }
  [ -e "$R/$tag" ] && mv "$R/$tag" "legacy/$(echo "$R/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  OMP_NUM_THREADS=1 "$PY" scripts/run_with_watchdog.py --log "$R/$tag.log" --out "$R/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_relay_satrot.py --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity "$cap" \
    --relay age --order "$order" "$@" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$R/$tag" || echo "FAIL $tag"
}
rot() {
  for s in 0 1; do for a in relay6_st_s$s relay6Cage_st_s$s relay_st_s$s; do for o in prefix agefirst; do
    ev ${a}_${o}_iid $a $o iid "prefix cap4" --quant 4
    ev ${a}_${o}_low $a $o low "prefix" --quant 4
  done; done; done
}
b12() {
  for s in 0 1; do
    tag=relay6B12_st_s$s
    if [ -f "$D/$tag/manifest.json" ]; then echo "done $tag"; else
      echo "train $tag $(date)"
      "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v6.py \
        --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed "$s" --out "$D/$tag" --iters 500 --quant 9012 --codebook "$CBS" || echo "FAIL $tag" &
    fi
  done; wait
  for s in 0 1; do for o in prefix agefirst; do
    ev relay6B12_st_s${s}_${o}_iid relay6B12_st_s$s $o iid "prefix cap4" --quant 9012 --codebook "$CBS"
    ev relay6B12_st_s${s}_${o}_low relay6B12_st_s$s $o low "prefix" --quant 9012 --codebook "$CBS"
  done; done
}
seeds() {  # relay6Cage students (correct layout, trained under agefirst) for the teachers set_full_s2..s9, two at a time, OMP 1
  for pair in "2 3" "4 5" "6 7" "8 9"; do
    for s in $pair; do
      tag=relay6Cage_st_s$s
      if [ -f "$D/$tag/manifest.json" ]; then echo "done $tag"
      elif pgrep -f -- "--out $D/$tag --stall" > /dev/null; then echo "in progress elsewhere: $tag"
      else
        echo "train $tag $(date)"
        OMP_NUM_THREADS=1 "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v6.py \
          --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed "$s" --out "$D/$tag" --iters 500 --quant 4 --order agefirst || echo "FAIL $tag" &
      fi
    done; wait
    for s in $pair; do for o in prefix agefirst; do
      ev relay6Cage_st_s${s}_${o}_iid relay6Cage_st_s$s $o iid "prefix cap4" --quant 4
      ev relay6Cage_st_s${s}_${o}_low relay6Cage_st_s$s $o low "prefix" --quant 4
    done; done
  done
}
case "${1:-}" in
  rot) rot;;
  b12) b12;;
  seeds) seeds;;
  *) echo "usage: $0 rot|b12|seeds"; exit 2;;
esac
echo "$1 done $(date)"
