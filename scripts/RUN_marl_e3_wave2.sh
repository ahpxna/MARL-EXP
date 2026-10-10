#!/usr/bin/env bash
# Wave 2a of PROTOCOL_E3_WAVE_ALL_PENDING_20261003 (03/10/2026 23:4x EDT): E8 residual-guard panel, E9 exact-protocol replay, E7 mixed
# fleet confirmation.  One JOB per call:
#   DET <CK1|Cage> <s> | E8Z <s> | FTOLD <FTMIX|PCT> <s> | E8 <CK1|Cage> <s> <K> | E9R <s> | REF <s> | MIX <s> <D|C>
# 4x4 (grid relay wrapper).  E8: 7401-7464; E7: 7501-7564; E9R: dev 901-904; all x 8/16.  SMOKE=1: traffic 9001-9002.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_wave_20261003/w2; [ "${SMOKE:-0}" = 1 ] && E=$M/e3_wave_20261003/smoke_pipe/w2; A=$M/e3_grid4x4_20260930/actors
W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
if [ "${SMOKE:-0}" = 1 ]; then P8="9001 9002"; P7="9001 9002"; DEV="9001 9002"; else P8=$(seq 7401 7464); P7=$(seq 7501 7564); DEV="901 902 903 904"; fi
mkdir -p "$E"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$E/$tag/manifest.json" ] && return 0; guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$E/$tag" || { echo "FAIL $tag"; return 1; }; }
rn() { case $1 in CK1) echo relayCK1_st;; Cage) echo relayCage_st;; esac; }
ALT() { echo "--alt FT=$E/T_FTMIX_s$1/ckpt_b80.pt PCT=$E/T_PCT_s$1/ckpt_b80.pt"; }
FLEET="scripts/MARL_e3_mixed_fleet_eval_v2.py"; ARMS7="U1/PLAIN U2/PLAIN U2/EMU_OLD U2/EXACT_PROTO_OLD U1/FB_OLD U1/FBR_OLD U1/PLAIN@FT U1/PLAIN@PCT K1/ROLLBACK"
case $1 in
  DET) r=$(rn $2); wd det_${r}_s$3 $W scripts/MARL_e3_repair_panel_eval_v2.py --calibrate --relay $A/${r}_s$3/ckpt_best.pt --calib-old $M/e3_fallback_20261002/4x4/cal_${r}_s$3/calib.json ;;
  FTOLD) X="--method ft_mix"; [ $2 = PCT ] && X="--method pct --lam 1.0"
         wd T_$2_s$3 $W scripts/MARL_e3_actor_adapt_v12.py --init-from $A/relayCK1_st_s$3/ckpt_best.pt $X --seed $3 --budget 80 --save-at 80 ;;
  E8) r=$(rn $2); wd E8_${r}_s$3_K$4 $W scripts/MARL_e3_repair_panel_eval_v2.py --relay $A/${r}_s$3/ckpt_best.pt --z $A/distill_none_s$3/ckpt_best.pt --tag ${r}_s$3 \
        --detectors $E/det_${r}_s$3/detectors.json --K $4 --arms PLAIN FB_S+ FB_Mq- FB_Mq+ FB_Mr- FB_Mr+ --traffic-seeds $P8 --headways 8 16 ;;
  E8Z) wd E8Z_s$2 $W scripts/MARL_e3_repair_panel_eval.py --z-only --z $A/distill_none_s$2/ckpt_best.pt --traffic-seeds $P8 --headways 8 16 ;;
  E9R) wd E9R_s$2 $W $FLEET --old $A/relayCK1_st_s$2/ckpt_best.pt --new $A/relayCage_st_s$2/ckpt_best.pt --z $A/distill_none_s$2/ckpt_best.pt --layout ALL \
        --arms U2/EXACT_PROTO_OLD K1/ROLLBACK --traffic-seeds $DEV --headways 8 16 ;;
  REF) wd REF_s$2 $W $FLEET --old $A/relayCK1_st_s$2/ckpt_best.pt --new $A/relayCage_st_s$2/ckpt_best.pt --z $A/distill_none_s$2/ckpt_best.pt --refs --traffic-seeds $P7 --headways 8 16 ;;
  MIX) wd MIX_s$2_$3 $W $FLEET --old $A/relayCK1_st_s$2/ckpt_best.pt --new $A/relayCage_st_s$2/ckpt_best.pt --z $A/distill_none_s$2/ckpt_best.pt $(ALT $2) \
        --detectors $E/det_relayCK1_st_s$2/detectors.json --layout $3 --arms $ARMS7 --traffic-seeds $P7 --headways 8 16 ;;
  *) echo "unknown job $1"; exit 1 ;;
esac
rc=$?; echo "job $* done rc=$rc $(date)"; exit $rc
