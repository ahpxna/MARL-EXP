#!/usr/bin/env bash
# PROTOCOL_E3_ADAPT_PILOT_20261003.md (03/10/2026 19:1x EDT).  One JOB per call:
#   Z <s> | T <ARM> <s> | I <s> <B> <alpha> (BCWI checkpoint) | E <ARM> <s> <B> <K>   (ARM: FTNEW FTMIX PCT PAIRED A0 A1 A2 PARENT BCWI<alpha>)
# 4x4; training under the grid relay wrapper; evaluation = MARL_e3_repair_panel_eval.py arm PLAIN on traffic 5701-5748 x 8/16.
# SMOKE=1: budgets 8 16, traffic 9001-9002, under e3_adapt_pilot_20261003/smoke_pipe.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_adapt_pilot_20261003; [ "${SMOKE:-0}" = 1 ] && E=$E/smoke_pipe; A=$M/e3_grid4x4_20260930/actors
W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
if [ "${SMOKE:-0}" = 1 ]; then S="9001 9002"; BUD="8 16"; BMAX=16; else S=$(seq 5701 5748); BUD="8 16 40 80"; BMAX=80; fi
mkdir -p "$E"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$E/$tag/manifest.json" ] && return 0; guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$E/$tag" || echo "FAIL $tag"; }
args() { case $1 in FTNEW) echo "--method ft_new";; FTMIX) echo "--method ft_mix";; PCT) echo "--method pct --lam 1.0";;
  PAIRED) echo "--method paired --gamma 2.0 --lam 1.0";; A0) echo "--method paired --gamma 0 --lam 0";; A1) echo "--method paired --gamma 2.0 --lam 0";;
  A2) echo "--method paired --gamma 0 --lam 1.0";; esac; }
ckpt() { case $1 in PARENT) echo "$A/relayCK1_st_s$2/ckpt_best.pt";; BCWI*) echo "$E/bcwi/s$2_B$3_a${1#BCWI}.pt";; *) echo "$E/T_$1_s$2/ckpt_b$3.pt";; esac; }
case $1 in
  Z) wd Z_s$2 $W scripts/MARL_e3_repair_panel_eval.py --z-only --z $A/distill_none_s$2/ckpt_best.pt --traffic-seeds $S --headways 8 16 ;;
  T) wd T_$2_s$3 $W scripts/MARL_e3_actor_adapt_v12.py --init-from $A/relayCK1_st_s$3/ckpt_best.pt $(args $2) --seed $3 --budget $BMAX --save-at $BUD ;;
  I) f=$E/bcwi/s$2_B$3_a$4.pt; [ -f "$f" ] || "$PY" scripts/MARL_e3_bcwi_interp.py --parent $A/relayCK1_st_s$2/ckpt_best.pt --child $E/T_FTMIX_s$2/ckpt_b$3.pt --alpha $4 --out $f ;;
  E) c=$(ckpt $2 $3 $4); [ -f "$c" ] || { echo "FAIL missing $c"; exit 1; }
     wd E_$2_s$3_B$4_K$5 $W scripts/MARL_e3_repair_panel_eval.py --relay $c --z $A/distill_none_s$3/ckpt_best.pt --tag $2_s$3_B$4 --arms PLAIN --K $5 --traffic-seeds $S --headways 8 16 ;;
  *) echo "unknown job $1"; exit 1 ;;
esac
echo "job $* done $(date)"
