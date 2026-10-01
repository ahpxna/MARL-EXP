#!/usr/bin/env bash
# Papers A / B / C experiments on the RELAY method, v2 (30/09 14:2x; ledger L-173).  RUN_marl_e3_ABC.sh with the relay
# packet of models/marl_relay_v2.py (the 25 B bit layout of L-165: positional slots, 4-bit ages saturated at 14 steps):
#   * training: scripts/MARL_e3_actor_distill_v6.py (distill v5 + the v2 merge);
#   * evaluation: scripts/MARL_e3_delivery_eval_relay_sat.py (relay eval v2 + the v2 merge);
#   * every new student carries "6" in its tag (relay6*), so no v1-layout directory is reused.
# The fits (A-fit, B-fit) and the age diagnostic (C-diag) are those of RUN_marl_e3_ABC.sh, unchanged: they read the v1-trained
# relay_st_s0 and write the same JSONs (skipped if present).  Development panel 901-964 only; a pre-registration is written
# BEFORE any new-panel run.  Watchdog on every run.
#
#   bash scripts/RUN_marl_e3_ABC_v2.sh fits      A-fit, B-fit, C-diag (one process at a time; RUN_marl_e3_ABC.sh sets OMP 2)
#   bash scripts/RUN_marl_e3_ABC_v2.sh train     waves of <= 4 students: R (base, correct layout) + C-age, then A, then B, then C-low
#   bash scripts/RUN_marl_e3_ABC_v2.sh eval      development-panel evals of every finished relay6 student + the v1 students re-measured
#   bash scripts/RUN_marl_e3_ABC_v2.sh all       train then eval (the fits must have run, or A/B are skipped with a message)
# agefirst is used only with the uncapped prefix rule: deliver_agefirst ignores cap<c> (bug found by the parallel session).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929; M=research/marl_budget
CBR=$M/e3_payload_codebook_relay_20260930.json; CBS=$M/e3_field_sensitivity_20260930.json
student() {  # tag seed extra-args...   (DAgger relay student from set_full_s<seed>, distill v6)
  local tag=$1 s=$2; shift 2
  [ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  echo "train $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v6.py \
    --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed "$s" --out "$D/$tag" --iters 500 "$@" || echo "FAIL $tag"
}
ev() {  # tag actor deliveries capacity extra-args...   (relay eval SAT)
  local tag=$1 actor=$2 dels=$3 cap=$4; shift 4
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag (no $actor)"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  OMP_NUM_THREADS=1 "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_relay_sat.py --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity "$cap" \
    --relay age "$@" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
train() {
  for s in 0 1; do student relay6_st_s$s $s --quant 4 & student relay6Cage_st_s$s $s --quant 4 --order agefirst & done; wait
  if [ -f "$CBR" ]; then for s in 0 1; do student relay6A4_st_s$s $s --quant 4 --codebook "$CBR" & student relay6A504_st_s$s $s --quant 50004 --codebook "$CBR" & done; wait
  else echo "skip A-train: no $CBR"; fi
  if [ -f "$CBS" ]; then for s in 0 1; do student relay6B8_st_s$s $s --quant 9008 --codebook "$CBS" & student relay6B16_st_s$s $s --quant 9016 --codebook "$CBS" & done; wait
  else echo "skip B-train: no $CBS"; fi
  for s in 0 1; do student relay6Clow_st_s$s $s --quant 4 --capacity low & done; wait
}
evals() {
  for s in 0 1; do
    ev relay_st_s${s}_sat relay_st_s$s "prefix cap4" iid --quant 4                      # the v1-trained students under the correct layout
    ev relay6_st_s${s}_eval relay6_st_s$s "prefix cap4" iid --quant 4
    ev relay6_st_s${s}_evlow relay6_st_s$s "prefix" low --quant 4
    ev relay6Cage_st_s${s}_eval relay6Cage_st_s$s "prefix" iid --quant 4 --order agefirst
    ev relay6Cage_st_s${s}_evprefix relay6Cage_st_s$s "prefix" iid --quant 4
    ev relay6A4_st_s${s}_eval relay6A4_st_s$s "prefix cap4" iid --quant 4 --codebook "$CBR"
    ev relay6A504_st_s${s}_eval relay6A504_st_s$s "prefix cap4" iid --quant 50004 --codebook "$CBR"
    ev relay6B8_st_s${s}_eval relay6B8_st_s$s "prefix cap4" iid --quant 9008 --codebook "$CBS"
    ev relay6B16_st_s${s}_eval relay6B16_st_s$s "prefix cap4" iid --quant 9016 --codebook "$CBS"
    ev relay6Clow_st_s${s}_eval relay6Clow_st_s$s "prefix cap4" iid --quant 4
    ev relay6Clow_st_s${s}_evlow relay6Clow_st_s$s "prefix" low --quant 4
  done
}
case "${1:-}" in
  fits) bash scripts/RUN_marl_e3_ABC.sh A-fit; bash scripts/RUN_marl_e3_ABC.sh B-fit
        bash scripts/RUN_marl_e3_ABC.sh C-diag;;
  train) train;;
  eval) evals;;
  all) train; evals;;
  *) echo "usage: $0 fits|train|eval|all"; exit 2;;
esac
echo "$1 done $(date)"
