#!/usr/bin/env bash
# PROTOCOL_E3_G4_S0_DEVLOOK_20261001.md (EXPLORATORY): 4x4 seed 0, development episodes, K = 1..6 and iid.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
W="scripts/MARL_grid_wrapper.py --rows 4 --cols 4 --"; WR="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
A=research/marl_budget/e3_grid4x4_20260930/actors; P=research/marl_budget/e3_g4_s0_devlook_20261001; mkdir -p "$P"
T=$A/set_full_s0/ckpt_best.pt; Zc=$A/distill_none_s0/ckpt_best.pt; R=$A/relayCage_st_s0/ckpt_best.pt
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
run Zdev $W scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s0=$Zc" --deliveries none --capacity iid --traffic-seeds 901 902 903 904 --headways 8 16
for K in 1 2 3 4 5 6 0; do
  c=const$K; [ $K -eq 0 ] && c=iid
  run NF_$c $WR scripts/MARL_e3_negflip_probe_v2.py --relay "$R" --teacher "$T" --z "$Zc" --zrows "$P/Zdev/rows.json" --capacity $c &
  run R_K$K $WR scripts/MARL_e3_ageclip_eval.py --relay "$R" --tag relayCage_st_s0 --K $K --A -1 --traffic-seeds 901 902 903 904 --headways 8 16 &
  wait
done
echo "g4 s0 devlook done $(date)"
