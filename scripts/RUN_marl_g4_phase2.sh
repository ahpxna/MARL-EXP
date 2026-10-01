#!/usr/bin/env bash
# 4x4 GRID, phase 2 (30/09 20:5x EDT; ledger L-186): relay students and the relay grid for one seed, after phase 1.
# Relay packets keep the 185-bit 25 B layout with 8 slots per sender (the 8 nearest agents; models/marl_relay_v3.py),
# through scripts/MARL_grid_relay_wrapper.py (UNCHANGED distill v6 / satrot evaluator; parity with the 3x3 rows 8/8, and the
# 4x4 mirror check PASS in the smoke, ledger L-186).  Students: trained under the congestion order (as relay6_st) and under
# age-first ordering (as relay6Cage_st), in parallel.  Then the grid: both orders x iid (prefix, cap4) and low; FO (teacher,
# fresh-only receiver, raw packets) under both orders.  Watchdog on every run.
# Usage: bash scripts/RUN_marl_g4_phase2.sh <seed>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; G=research/marl_budget/e3_grid4x4_20260930; A=$G/actors; E=$G/eval; mkdir -p "$A" "$E"
WR="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
[ -f "$A/set_full_s$s/manifest.json" ] || { echo "no teacher set_full_s$s: phase 1 did not finish"; exit 1; }
train() {  # tag args...
  local tag=$1; shift
  [ -f "$A/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$A/$tag" ] && mv "$A/$tag" "legacy/g4_${tag}_partial_$(date +%Y%m%d_%H%M%S)"
  echo "train $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$A/$tag.log" --out "$A/$tag" --stall 1200 --retries 3 -- "$PY" -u $WR \
    scripts/MARL_e3_actor_distill_v6.py --teacher "$A/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed $s \
    --iters 500 --quant 4 "$@" --out "$A/$tag" || echo "FAIL $tag"
}
ev() {  # tag actor order capacity deliveries extra...
  local tag=$1 actor=$2 order=$3 cap=$4 dels=$5; shift 5
  [ -f "$A/$actor/manifest.json" ] || { echo "skip $tag"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 600 --retries 3 -- "$PY" -u $WR \
    scripts/MARL_e3_delivery_eval_relay_satrot.py --actors "$actor=$A/$actor/ckpt_best.pt" --deliveries $dels --capacity "$cap" \
    --order "$order" "$@" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
train relay_st_s$s &
train relayCage_st_s$s --order agefirst &
wait
for a in relay_st_s$s relayCage_st_s$s; do for o in prefix agefirst; do
  ev ${a}_${o}_iid $a $o iid "prefix cap4" --relay age --quant 4
  ev ${a}_${o}_low $a $o low "prefix" --relay age --quant 4
done; done
for o in prefix agefirst; do
  ev FO_s${s}_${o}_iid set_full_s$s $o iid "prefix cap4" --adapter-override freshonly
  ev FO_s${s}_${o}_low set_full_s$s $o low "prefix" --adapter-override freshonly
done
echo "g4 phase2 seed $s done $(date)"
