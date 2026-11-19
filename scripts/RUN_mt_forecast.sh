#!/usr/bin/env bash
# SPaT forecasters for lights trained on Midtown (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010, MT-A6, 11/10/2026): the W19 forecaster recipe
# (job 104a steps 2-4: traces -> open-loop table -> closed-loop c2 prep with the DEV fleet -> N2 logs -> N2 fit), unchanged, run through
# scripts/DEMO_midtown.py on Midtown TRAINING traffic 10-17 (never a test day).  CITY_n2_fit.py hard-codes train files feat_s0..5 and
# validation feat_s6,7; here the logs are named by their real seeds 10..17 and a separate folder of symlinks s<i> -> s<10+i> feeds the fit
# (the logs themselves are not renamed).  Sequential lights only (A4, ft): the closed-loop prep widens a Sequential net (CITY_m3_core.widen).
# Usage: RUN_mt_forecast.sh <lights dir> <out dir> "<k list>" [lanes]    (SMOKE=1: one 300 s prep episode, smoke-length traces and logs)
set -u; cd "$(dirname "$0")/.."
L=$(cd "$1" && pwd); D=$2; KS=$3; P=${4:-5}; mkdir -p $D/traces $D/m2b $D/prep $D/cdata $D/cmodel $D/check; D=$(cd $D && pwd)
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=${MT_BASE:-osm} MT_NET=${MT_NET:-midtown} W19_LIGHTS=$L XPLAY_TMP=$D/check W7_FPR_DIR=$D   # MT-F: map / base plan overridable
export PY=external_envs/city_runtime/bin/python DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt D
export RUN="$PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py"; export TS="10 11 12 13 14 15 16 17"
if [ "${SMOKE:-0}" = 1 ]; then export SM="--smoke" W7_PREP_N=1 W7_PREP_END=300; else export SM="" W7_PREP_N=8 W7_PREP_END=3600; fi
echo "MT forecasters for lights $L k [$KS] -> $D (smoke ${SMOKE:-0}, net $MT_NET, base $MT_BASE) $(date)"
one() {   # all steps for one light k; every step reports its own failure (errexit does not apply inside `one || ...`)
  k=$1
  [ -f $D/traces/fit_RLH$k.json ] || nice -n 5 $RUN scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$k --fleet L-ACT:0 --guard always --seeds $TS $SM --record $D/traces/rlh${k}_s{seed}.npz --tag fit_RLH$k --out $D/traces > $D/traces/run_t$k.log 2>&1 || { echo "FAIL traces t$k"; return 1; }
  F=""; for s in $TS; do F="$F $D/traces/rlh${k}_s$s.npz"; done
  [ -f $D/m2b/forecast_rlh$k.json ] || $RUN scripts/MT_spat_fit.py $k $D/m2b/forecast_rlh$k.json $F > $D/m2b/fit_t$k.log 2>&1 || { echo "FAIL open-loop fit t$k"; return 1; }
  [ -f $D/prep/prov_rlh${k}_cl.json ] || nice -n 5 $RUN scripts/CITY_w19_prep.py $k $D/prep > $D/prep/prep_k$k.out 2>&1 || { echo "FAIL prep t$k"; return 1; }
  for s in $TS; do [ -f $D/cdata/c2_t$k/feat_s$s.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/cdata/c2_t$k --spat-arm fc2:0.1:$D/prep/prov_rlh${k}_cl.json --light RL-H:$k --fleet PL:$DEV --seeds $s $SM --tag C_t${k}_s$s --out $D/cdata/c2_t$k >> $D/cdata/run_t$k.log 2>&1 || { echo "FAIL collect t$k s$s"; return 1; }; done
  mkdir -p $D/cdata/c2_t${k}_fit; i=0; for s in $TS; do ln -sf ../c2_t$k/feat_s$s.npz $D/cdata/c2_t${k}_fit/feat_s$i.npz; i=$((i+1)); done
  [ -f $D/cmodel/n2_k$k.pt ] || $RUN scripts/CITY_n2_fit.py $k $D/cdata/c2_t${k}_fit $D/cmodel > $D/cmodel/fit_t$k.log 2>&1 || { echo "FAIL n2 fit t$k"; return 1; }
  echo "t$k done $(date)"
}
export -f one
printf '%s\n' $KS | xargs -P $P -I{} bash -c 'one {} || { echo "FAIL t{}"; exit 255; }' || { echo "forecaster failure"; exit 1; }
for k in $KS; do test -f $D/cmodel/n2_k$k.pt && test -f $D/prep/prov_rlh${k}_cl.json || { echo "MISSING forecaster t$k"; exit 1; }
  $PY -c "import json; T=json.load(open('$D/prep/prov_rlh${k}_cl.json')); print('t$k provenance: lights', len(T['per']), 'files', T['n_files'])"; done
echo "forecasters done $(date)"
