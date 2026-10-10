#!/usr/bin/env bash
# Wave 2b (E2 factorial + UNI, E10 PAIRED v2) of PROTOCOL_E3_WAVE_ALL_PENDING_20261003 (03/10/2026 23:5x EDT).  One JOB per call:
#   T <SI|OP|UNI|V2S|V2D> <s> | E <ARM> <s> <L> <K>      L = iteration level 1 / 2 / 5 / 10 (4 / 8 / 20 / 40 new-channel episodes)
# Training v13 from CK1 s; evaluation = MARL_e3_repair_panel_eval.py PLAIN on the adaptation pilot's blocks 5701-5748 x 8/16 (Z / FT-mix /
# PCT / PAIRED / A0 rows of the pilot are reused by the report).  SMOKE=1: levels 1 2, traffic 9001-9002.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_wave_20261003/w2b; [ "${SMOKE:-0}" = 1 ] && E=$M/e3_wave_20261003/smoke_pipe/w2b; A=$M/e3_grid4x4_20260930/actors
W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
if [ "${SMOKE:-0}" = 1 ]; then P="9001 9002"; LV="1 2"; else P=$(seq 5701 5748); LV="1 2 5 10"; fi
mkdir -p "$E"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$E/$tag/manifest.json" ] && return 0; guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$E/$tag" || { echo "FAIL $tag"; return 1; }; }
spi() { case $1 in SI|V2S|V2D) echo 12;; *) echo 8;; esac; }                       # simulated episodes per iteration
args() { case $1 in SI) echo "--method si";; OP) echo "--method op";; UNI) echo "--method paired --gamma 2 --uniform-h";;
  V2S) echo "--method v2 --gamma 2";; V2D) echo "--method v2 --gamma 2 --dynamic-h";; esac; }
case $1 in
  T) k=$(spi $2); sv=""; for l in $LV; do sv="$sv $((l * k))"; done; mx=$(( ${LV##* } * k ))
     wd T_$2_s$3 $W scripts/MARL_e3_actor_adapt_v13.py --init-from $A/relayCK1_st_s$3/ckpt_best.pt $(args $2) --seed $3 --budget $mx --save-at $sv ;;
  E) k=$(spi $2); c=$E/T_$2_s$3/ckpt_b$(( $4 * k )).pt; [ -f "$c" ] || { echo "FAIL missing $c"; exit 1; }
     wd E_$2_s$3_L$4_K$5 $W scripts/MARL_e3_repair_panel_eval.py --relay $c --z $A/distill_none_s$3/ckpt_best.pt --tag $2_s$3_L$4 --arms PLAIN --K $5 --traffic-seeds $P --headways 8 16 ;;
  *) echo "unknown job $1"; exit 1 ;;
esac
rc=$?; echo "job $* done rc=$rc $(date)"; exit $rc
