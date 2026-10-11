#!/usr/bin/env bash
# M4 stage 3 complete (PROTOCOL_CITY_M4_STAGE3_20261004).  Usage: RUN_s3full.sh prep | all
#   prep: closed-loop traces (F0 on the open-loop table, q 0.5, TRAIN 0-7) -> fit -> KS3-1        all: prep + DEV selection + KS3-2/3/5 + 3b + 3c + report
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; SP=research/city_sim/m4_20261004/spider; D=$SP/s3b
EV=scripts/CITY_m4s_s3_eval.py; RULE=research/city_sim/f1_20261004/train/RULE0_fleet.pt; mkdir -p $D/traces/tmp $D/prov $D/dev/tmp $D/eval/tmp $D/check/tmp $D/train
echo "start $1 $(date)"
for k in 11 111; do [ -f $D/prov/fkcl_rlk$k.json ] && continue
  XPLAY_TMP=$PWD/$D/traces/tmp nice -n 5 $PY -u $EV --spat-arm fck:0.5:$SP/s4b/prov/fk_rlk$k.json --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3 \
    --seeds 0 1 2 3 4 5 6 7 --record $D/traces/cl_rlk${k}_s{seed}.npz --tag cl_RLK$k --out $D/traces >> $D/traces/run.log 2>&1 &
done; wait
for k in 11 111; do [ -f $D/prov/fkcl_rlk$k.json ] || $PY -c "
import sys, json; sys.path.insert(0,'.')
import scripts.CITY_m4s_run, scripts.CITY_spat_forecast_k as FK
T = FK.fit_k(['$D/traces/cl_rlk${k}_s%d.npz' % s for s in range(8)]); json.dump(T, open('$D/prov/fkcl_rlk$k.json', 'w')); print('fit closed-loop rlk$k: lights', len(T['per']), 'files', T['n_files'])" || exit 1; done
$PY scripts/CITY_m4s_run.py scripts/CITY_spat_forecast_k_conv.py $D/traces/cl_rlk*_s*.npz > $D/check/ks3_1_conv.txt || { echo "KS3-1 FAIL"; cat $D/check/ks3_1_conv.txt; exit 1; }
$PY scripts/CITY_m4s_run.py scripts/CITY_spat_forecast_k_conv.py --neg $D/traces/cl_rlk*_s*.npz > $D/check/ks3_1_negative_control.txt && { echo "KS3-1 negative control did not fail"; exit 1; }
echo "KS3-1 PASS $(date)"; [ "$1" = prep ] && exit 0
# ---- DEV q selection
S="100 101 102 103 104 105 106 107 108 109"; ev() { O=$1; shift; XPLAY_TMP=$PWD/$O/tmp nice -n 5 $PY -u $EV "$@" --out $O >> $O/run.log 2>&1 || echo "FAIL $*"; }
for k in 11 111; do L=RLK:$SP/RLK_sp$k.pt; T=$D/prov/fkcl_rlk$k.json; [ -f $D/dev/R_$k.json ] || ev $D/dev --spat-arm none --light $L --fleet GLOSAL:0.3 --seeds $S --tag R_$k &
  for q in 0.1 0.2 0.3 0.5; do [ -f $D/dev/Fq${q}_$k.json ] || ev $D/dev --spat-arm fck:$q:$T --light $L --fleet GLOSAL:0.3 --seeds $S --record $D/dev/fq${q}_rlk${k}_s{seed}.npz --tag Fq${q}_$k & done; done; wait
$PY scripts/CITY_m4_s3_select.py || exit 1; Q=$($PY -c "import json; print(json.load(open('$D/prov/locked.json'))['q'])"); echo "locked q $Q"
$PY scripts/CITY_m4s_run.py scripts/CITY_spat_forecast_k_validate.py $D/prov/fkcl_rlk11.json $Q $D/dev/fq${Q}_rlk11_s*.npz > $SP/report_m4_s3b_forecast_quality.json
# ---- KS3-2 / KS3-3 / KS3-5 (seed 100, sp11)
L=RLK:$SP/RLK_sp11.pt; T=$D/prov/fkcl_rlk11.json
[ -f $D/train/F1_zero_fleet.pt ] || $PY -u scripts/CITY_fleet_train_f1k.py --seed 213 --light-ckpt $SP/RLK_sp11.pt --init scratch --table $T --q $Q --episodes 0 --name F1_zero --out $D/train > $D/train/F1_zero.out 2>&1
ev $D/check --spat-arm fck:$Q:$T --light $L --fleet GLOSAL:0.3 --seeds 100 --tag KS_glosal & ev $D/check --spat-arm fck:$Q:$T --light $L --fleet PL:$RULE --seeds 100 --tag KS_rule0 &
ev $D/check --spat-arm fck:$Q:$T --light $L --fleet PL:$D/train/F1_zero_fleet.pt --seeds 100 --tag KS_zero & wait
$PY scripts/CITY_m4_s3full_check.py || { echo "KS3-2/3/5 FAIL: stop"; exit 1; }
# ---- 3b panel
S="$(seq -s ' ' 1000 1019)"
for k in 11 111; do [ -f $D/eval/F0_RLK${k}_fcast.json ] || ev $D/eval --spat-arm fck:$Q:$D/prov/fkcl_rlk$k.json --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3 --seeds $S --tag F0_RLK${k}_fcast & done
# ---- 3c training (concurrently with the 3b panel)
for p in "213 11" "313 11" "413 111" "513 111"; do set -- $p; [ -f $D/train/F1_s$1_fleet.pt ] || nice -n 5 $PY -u scripts/CITY_fleet_train_f1k.py --seed $1 --light-ckpt $SP/RLK_sp$2.pt \
  --init scratch --table $D/prov/fkcl_rlk$2.json --q $Q --episodes 200 --name F1_s$1 --out $D/train > $D/train/F1_s$1.out 2>&1 & done; wait; echo "3b panel + 3c training done $(date)"
$PY - <<PYC || { echo "KS3-4 FAIL"; exit 1; }
import hashlib, torch
for f, k in ((213, 11), (313, 11), (413, 111), (513, 111)):
    d = torch.load('$D/train/F1_s%d_fleet.pt' % f, weights_only=False); h = hashlib.sha256(open('$SP/RLK_sp%d.pt' % k, 'rb').read()).hexdigest()
    assert d['light_sha256'] == h and d['episodes'] == 200, (f, k); print('KS3-4', f, k, 'light sha ok, 200 episodes')
PYC
# ---- 3c panel: L1/F1 crossed (8 jobs), L0/F1 under FT with the program SPaT (4 jobs, CITY_eval6_m2 naive through the spider runner)
for k in 11 111; do for f in 213 313 413 513; do [ -f $D/eval/F1_s${f}_on_$k.json ] || ev $D/eval --spat-arm fck:$Q:$D/prov/fkcl_rlk$k.json --light RLK:$SP/RLK_sp$k.pt \
  --fleet PL:$D/train/F1_s${f}_fleet.pt --seeds $S --tag F1_s${f}_on_$k & done; done
for f in 213 313 413 513; do [ -f $D/eval/F1_s${f}_FT.json ] || XPLAY_TMP=$PWD/$D/eval/tmp nice -n 5 $PY -u scripts/CITY_m4s_run.py scripts/CITY_eval6_m2.py --spat-label naive --light FT \
  --fleet PL:$D/train/F1_s${f}_fleet.pt --seeds $S --tag F1_s${f}_FT --out $D/eval >> $D/eval/run.log 2>&1 & done; wait
$PY scripts/CITY_m4_s3full_report.py; echo "M4 stage 3 complete done $(date)"
