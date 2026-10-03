#!/usr/bin/env bash
# PROTOCOL_E3_G4_RELAUNCH_20261002.md: the const-K work of ONE seed (PROTOCOL_E3_G4_CONSTK_20261001 + addenda, full mode,
# which includes the R5 development items NF iid / low), loop body copied verbatim from scripts/RUN_marl_g4_constk.sh.
# Idempotent.  Usage: bash scripts/RUN_marl_g4_constk_seed.sh <seed>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
W="scripts/MARL_grid_wrapper.py --rows 4 --cols 4 --"; WR="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
mode=full; A=research/marl_budget/e3_grid4x4_20260930/actors; E=research/marl_budget/e3_g4_replication_20261001; P=research/marl_budget/e3_g4_constk_20261001; mkdir -p "$P"
DEV="901 902 903 904"; SEEDS=$(seq 3301 3364)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
s=$1
T=$A/set_full_s$s/ckpt_best.pt; Zc=$A/distill_none_s$s/ckpt_best.pt; R=$A/relayCage_st_s$s/ckpt_best.pt
for x in set_full distill_none relayCage_st; do [ -f "$A/${x}_s$s/manifest.json" ] || { echo "skip s$s (no $x)"; exit 1; }; done
run Zdev_s$s $W scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$Zc" --deliveries none --capacity iid --traffic-seeds $DEV --headways 8 16
par=""; [ -f "$E/Rdev_s${s}_low/rows.json" ] && par="--parity $E/Rdev_s${s}_low/rows.json"
CS="const1 const2 const3 iid low"
for c in $CS; do
  pc=""; [ "$c" = low ] && pc="$par"
  run NF_s${s}_$c $WR scripts/MARL_e3_negflip_probe_v2.py --relay "$R" --teacher "$T" --z "$Zc" --zrows "$P/Zdev_s$s/rows.json" --capacity $c $pc
done
for K in 1 2 3 0; do
  c=const$K; [ $K -eq 0 ] && c=iid
  run VS_s${s}_K$K $WR scripts/MARL_e3_viewstats_probe_v2.py --relay "$R" --teacher "$T" --z "$Zc" --parity-dir "$P/NF_s${s}_$c" --K $K
done
for K in 1 2 3 0; do
  c=const$K; [ $K -eq 0 ] && c=iid
  run NF3_s${s}_K$K $WR scripts/MARL_e3_negflip_probe_v3.py --relay "$R" --teacher "$T" --z "$Zc" --zrows "$P/Zdev_s$s/rows.json" --capacity $c
done
[ -f "$P/a95_s$s.txt" ] || "$PY" -c "import numpy as np; z=np.load('$P/VS_s${s}_K0/flags.npz'); m=z['max_age'][z['max_age']>=0]; print(int(round(float(np.percentile(m,95)))))" > "$P/a95_s$s.txt"
a95=$(cat "$P/a95_s$s.txt"); echo "s$s a95=$a95"
run Z_s$s $W scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$Zc" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16
for K in 1 2 3 0; do
  run R_s${s}_K${K}_A-1 $WR scripts/MARL_e3_ageclip_eval.py --relay "$R" --tag relayCage_st_s$s --K $K --A -1 --traffic-seeds $SEEDS --headways 8 16
done
run R_s${s}_K1_clip $WR scripts/MARL_e3_ageclip_eval.py --relay "$R" --tag relayCage_st_s$s --K 1 --A "$a95" --traffic-seeds $SEEDS --headways 8 16
n=0; for t in Zdev_s$s NF_s${s}_const1 NF_s${s}_const2 NF_s${s}_const3 NF_s${s}_iid NF_s${s}_low VS_s${s}_K1 VS_s${s}_K2 VS_s${s}_K3 VS_s${s}_K0 \
  NF3_s${s}_K1 NF3_s${s}_K2 NF3_s${s}_K3 NF3_s${s}_K0 Z_s$s R_s${s}_K1_A-1 R_s${s}_K2_A-1 R_s${s}_K3_A-1 R_s${s}_K0_A-1 R_s${s}_K1_clip; do
  [ -f "$P/$t/manifest.json" ] || { echo "INCOMPLETE $t"; n=$((n+1)); }; done
[ $n -eq 0 ] || exit 1
echo "g4 const-K seed $s done $(date)"
