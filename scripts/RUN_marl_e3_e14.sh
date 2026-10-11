#!/usr/bin/env bash
# E14 (research/marl_budget/PROTOCOL_E3_E12_E14_G3_G6_20261004.md; 04/10/2026 wake 2).  One JOB per call:
#   T <OP|FTMIX|PCT> <s>   adaptation from CK1 s at budget 40 (save at 40)
#   E <OP|FTMIX|PCT|CK1> <s> <K>   MARL_e3_repair_panel_eval.py PLAIN, panel 7601-7664 x 8/16
#   Z <s>                  the Z rows on the same panel (--z-only)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_wave_20261003/e14; A=$M/e3_grid4x4_20260930/actors; P=$(seq 7601 7664); mkdir -p "$E"
W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$E/$tag/manifest.json" ] && return 0; guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$E/$tag" || { echo "FAIL $tag"; return 1; }; }
case $1 in
  T) case $2 in OP) X="scripts/MARL_e3_actor_adapt_v13.py --method op";; FTMIX) X="scripts/MARL_e3_actor_adapt_v12.py --method ft_mix";;
                PCT) X="scripts/MARL_e3_actor_adapt_v12.py --method pct --lam 1.0";; *) echo "unknown arm $2"; exit 1;; esac
     wd T_$2_s$3 $W $X --init-from $A/relayCK1_st_s$3/ckpt_best.pt --seed $3 --budget 40 --save-at 40 ;;
  E) if [ $2 = CK1 ]; then c=$A/relayCK1_st_s$3/ckpt_best.pt; else c=$E/T_$2_s$3/ckpt_b40.pt; fi; [ -f "$c" ] || { echo "FAIL missing $c"; exit 1; }
     wd E_$2_s$3_K$4 $W scripts/MARL_e3_repair_panel_eval.py --relay $c --z $A/distill_none_s$3/ckpt_best.pt --tag $2_s$3 --arms PLAIN --K $4 --traffic-seeds $P --headways 8 16 ;;
  Z) wd Z_s$2 $W scripts/MARL_e3_repair_panel_eval.py --z-only --z $A/distill_none_s$2/ckpt_best.pt --traffic-seeds $P --headways 8 16 ;;
  *) echo "unknown job $1"; exit 1 ;;
esac
rc=$?; echo "job $* done rc=$rc $(date)"; exit $rc
