#!/usr/bin/env bash
# QUEUE (30/09 16:3x EDT; ledger L-178; user 16:2x: "queue what you planned but could not run, to start when the current runs end").
# No polling: each lane blocks on `caffeinate -i -w <pid>` of the processes it depends on, then runs.
#   cage45  after the relay6Cage_st_s4 / s5 trainings (watchdog PIDs 59634, 59632): their rotating-head grid
#   cage69  after RUN_marl_e3_relaunch_crashed.sh seeds (PID 59600; it trains s6..s9 in pairs): their grid
#   abc     after RUN_marl_e3_relaunch_crashed.sh A (PID 59599) and the parallel session's RUN_marl_e3_ABC_v2.sh all (PID 50736,
#           B8/B16/Clow training + its own prefix-order evals): the rotating-head grid of A4, A504, B8, B16 (B16 = 212-bit packet,
#           OVER the 25 B budget: diagnostic only) and Clow.  B12 is trained and evaluated by the parallel session's
#           RUN_marl_e3_ABC_v2b.sh b12 (already queued on PID 50736).
# The grid is that of RUN_marl_e3_ABC_v2b.sh rot/seeds (satrot evaluator, orders prefix / agefirst, iid [prefix, cap4] and low
# [prefix]), same directory, same tag scheme, same in-progress guard.  Development panel 901-964 only.
# Usage: nohup bash scripts/QUEUE_marl_e3_after_current_20260930.sh cage45|cage69|abc > research/marl_budget/queue_<lane>.log 2>&1 &
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; R=research/marl_budget/e3_satrot_eval_20260930; M=research/marl_budget
CBR=$M/e3_payload_codebook_relay_20260930.json; CBS=$M/e3_field_sensitivity_20260930.json
waitfor() { for p in "$@"; do echo "waiting for PID $p $(date)"; caffeinate -i -w "$p" 2>/dev/null; done; echo "released $(date)"; }
ev() {  # tag actor order capacity deliveries extra-args...
  local tag=$1 actor=$2 order=$3 cap=$4 dels=$5; shift 5
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag (no $actor)"; return 0; }
  [ -f "$R/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  pgrep -f -- "--out $R/$tag --stall" > /dev/null && { echo "in progress elsewhere: $tag"; return 0; }
  [ -e "$R/$tag" ] && mv "$R/$tag" "legacy/$(echo "$R/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$R/$tag.log" --out "$R/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_relay_satrot.py --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity "$cap" \
    --relay age --order "$order" "$@" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$R/$tag" || echo "FAIL $tag"
}
grid() {  # actor extra-args...
  local a=$1; shift
  for o in prefix agefirst; do ev ${a}_${o}_iid $a $o iid "prefix cap4" "$@"; ev ${a}_${o}_low $a $o low "prefix" "$@"; done
}
case "${1:-}" in
  cage45) waitfor 59634 59632; for s in 4 5; do grid relay6Cage_st_s$s --quant 4 & done; wait;;
  cage69) waitfor 59600; for s in 6 7 8 9; do grid relay6Cage_st_s$s --quant 4 & done; wait;;
  abc) waitfor 59599 50736
       for s in 0 1; do
         grid relay6A4_st_s$s --quant 4 --codebook "$CBR" & grid relay6A504_st_s$s --quant 50004 --codebook "$CBR" & wait
         grid relay6B8_st_s$s --quant 9008 --codebook "$CBS" & grid relay6B16_st_s$s --quant 9016 --codebook "$CBS" & wait
         grid relay6Clow_st_s$s --quant 4
       done;;
  *) echo "usage: $0 cage45|cage69|abc"; exit 2;;
esac
echo "queue $1 done $(date)"
