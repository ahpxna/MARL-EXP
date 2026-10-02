#!/usr/bin/env bash
# PROTOCOL_E3_DECISION_RETURN_GAP_20261001.md (EXPLORATORY)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
W="scripts/MARL_grid_wrapper.py --rows 4 --cols 4 --"; WR="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
A4=research/marl_budget/e3_grid4x4_20260930/actors; A3=research/marl_budget/e3_delivery_actors_20260929; L=research/marl_budget/e3_g4_s0_devlook_20261001
P=research/marl_budget/e3_decision_return_gap_20261001; mkdir -p "$P"
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
for c in const1 const2 iid; do
  K=${c#const}; [ "$c" = iid ] && K=0
  run g4_s0_$c $WR scripts/MARL_e3_negflip_probe_v3.py --relay $A4/relayCage_st_s0/ckpt_best.pt --teacher $A4/set_full_s0/ckpt_best.pt --z $A4/distill_none_s0/ckpt_best.pt \
    --zrows $L/Zdev/rows.json --capacity $c --parity $L/R_K$K/rows.json &
done
run g4_s0_Zmore $W scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s0=$A4/distill_none_s0/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $(seq 905 916) --headways 8 16 &
run g4_s0_Rmore $WR scripts/MARL_e3_ageclip_eval.py --relay $A4/relayCage_st_s0/ckpt_best.pt --tag relayCage_st_s0 --K 1 --A -1 --traffic-seeds $(seq 905 916) --headways 8 16 &
wait
for s in 0 1 2 3 4 5 6 7 8 9; do
  run g3_s${s}_const1 scripts/MARL_e3_negflip_probe_v3.py --relay $A3/relay6Cage_st_s$s/ckpt_best.pt --teacher $A3/set_full_s$s/ckpt_best.pt --z $A3/distill_none_s$s/ckpt_best.pt \
    --zrows research/marl_budget/e3_dev_Z_20261001/Z_s$s/rows.json --capacity const1 --parity research/marl_budget/e3_negflip_20261001/s${s}_K1/rows.json &
  [ $((s % 3)) -eq 2 ] && wait
done
wait; echo "decision-return gap done $(date)"
