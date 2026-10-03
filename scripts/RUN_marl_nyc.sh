#!/usr/bin/env bash
# PROTOCOL_E3_NYC16X3_20261002.md (02/10/2026 22:4x EDT).  Usage: RUN_marl_nyc.sh <seed>
# One seed of the NYC 16x3 chain, the 4x4 commands through scripts/MARL_nyc_wrapper.py: teacher (resumable in place) ->
# Z ∥ relayCage_st (v9 iid = v6) ∥ relayCK1_st (v9 const1) -> the fallback calibrations and ruleA_s<seed>.json (BEFORE any panel
# run) -> panel evaluations (Z, relay K in {1, iid, 2, 3}) -> the fallback cells.  Idempotent; watchdog on every run.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1
if [ "${SMOKE:-0}" = 1 ]; then G=research/marl_budget/e3_nyc16x3_20261002/smoke_chain; TI=2; SI=2; SEEDS="5001"; CH=301; F=$G/fallback_cal
  export NYC_ACTORS=$G/actors SMOKE_DIR=smoke_nyc_chain
else G=research/marl_budget/e3_nyc16x3_20261002; TI=2000; SI=500; SEEDS=$(seq 5001 5064); CH=332; F=research/marl_budget/e3_fallback_20261002/nyc; fi
A=$G/actors; E=$G/eval; mkdir -p "$A" "$E" "$F"
W="scripts/MARL_nyc_wrapper.py --relay-slots none --"; WR="scripts/MARL_nyc_wrapper.py --relay-slots nearest8 --"
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
t=set_full_s$s
if [ ! -f "$A/$t/manifest.json" ]; then
  guard; [ -e "$A/$t" ] && [ ! -f "$A/$t/state_last.pt" ] && mv "$A/$t" "legacy/nyc_${t}_nostate_$(date +%Y%m%d_%H%M%S)"
  echo "train $t $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$A/$t.log" --stall 2400 --retries 20 -- "$PY" -u $W scripts/MARL_e3_actor_train_delivery_v6.py \
    --seed $s --iters $TI --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2 \
    --set-actor --delivery full --out "$A/$t" || { echo "FAIL $t"; exit 1; }
fi
[ -f "$A/$t/manifest.json" ] || { echo "no teacher $t: stop"; exit 1; }
z=distill_none_s$s
( if [ ! -f "$A/$z/manifest.json" ]; then guard; [ -e "$A/$z" ] && mv "$A/$z" "legacy/nyc_${z}_partial_$(date +%Y%m%d_%H%M%S)"; echo "train $z $(date)"
    "$PY" scripts/run_with_watchdog.py --log "$A/$z.log" --out "$A/$z" --stall 2400 --retries 3 -- "$PY" -u $W scripts/MARL_e3_actor_distill.py \
      --teacher "$A/$t/ckpt_best.pt" --student-delivery none --seed $s --iters $SI --threads 2 --out "$A/$z" || echo "FAIL $z"; fi ) &
for spec in relayCage_st:iid relayCK1_st:const1; do
  arm=${spec%%:*}; cap=${spec##*:}; a=${arm}_s$s
  ( if [ ! -f "$A/$a/manifest.json" ]; then guard; echo "train $a ($cap, v9 resumable) $(date)"
      "$PY" scripts/run_with_watchdog.py --log "$A/$a.log" --stall 2400 --retries 20 -- "$PY" -u $WR scripts/MARL_e3_actor_distill_v9.py \
        --teacher "$A/$t/ckpt_best.pt" --student-delivery prefix --relay age --seed $s --iters $SI --quant 4 --order agefirst --capacity $cap \
        --park-if-no-state --out "$A/$a" || echo "FAIL $a"; fi ) &
done
wait
for x in distill_none_s$s relayCage_st_s$s relayCK1_st_s$s; do [ -f "$A/$x/manifest.json" ] || { echo "missing $x: stop"; exit 1; }; done
for arm in relayCage_st relayCK1_st; do
  c=cal_${arm}_s$s
  [ -f "$F/$c/manifest.json" ] || { guard; [ -e "$F/$c" ] && mv "$F/$c" "legacy/nyc_${c}_partial_$(date +%Y%m%d_%H%M%S)"
    "$PY" scripts/run_with_watchdog.py --log "$F/$c.log" --out "$F/$c" --stall 1800 --retries 3 -- "$PY" -u $WR scripts/MARL_e3_fallback_eval.py \
      --calibrate --relay "$A/${arm}_s$s/ckpt_best.pt" --calib-lo 301 --calib-hi $CH --out "$F/$c" || echo "FAIL $c"; }
done
[ -f "$G/ruleA_s$s.json" ] || "$PY" - "$F/cal_relayCage_st_s$s/calib.json" "$G/ruleA_s$s.json" <<'PYEOF'
import json, sys, time
h = json.load(open(sys.argv[1]))['age_hist'][:15]; tot = sum(h); c = 0
for a, n in enumerate(h):
    c += n
    if c >= 0.99 * tot:
        break
tau = a; kmin = (1 - 0.08) * 47 / (tau + 2)
json.dump(dict(tau_train_p99=tau, tau_max=max(i for i, n in enumerate(h) if n), K_min=kmin, age_hist=h, written=time.ctime(),
               note='before any panel run of this seed (PROTOCOL_E3_NYC16X3_20261002, N2)'), open(sys.argv[2], 'w'), indent=1)
print('ruleA', sys.argv[2], tau, kmin)
PYEOF
run() { local tag=$1; shift; [ -f "$E/$tag/manifest.json" ] && return 0; guard; [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/nyc_${tag}_partial_$(date +%Y%m%d_%H%M%S)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 1800 --retries 3 -- "$PY" -u "$@" --out "$E/$tag" || echo "FAIL $tag"; }
run Z_s$s $W scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$A/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16
for arm in relayCage_st relayCK1_st; do for K in 1 0 2 3; do
  run R_${arm}_s${s}_K$K $WR scripts/MARL_e3_ageclip_eval.py --relay "$A/${arm}_s$s/ckpt_best.pt" --tag ${arm}_s$s --K $K --A -1 --traffic-seeds $SEEDS --headways 8 16
done; done
bash scripts/RUN_marl_e3_fallback.sh nyc $s
echo "nyc seed $s done $(date)"
