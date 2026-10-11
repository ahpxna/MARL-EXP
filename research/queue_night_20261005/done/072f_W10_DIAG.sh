#!/usr/bin/env bash
# W10-2 / W10-3 (PROTOCOL_CITY_WAVE10_20261005): served-answer forecast accounting (SERVE vs SHADOW) and held followers, grid4 and spider,
# through scripts/CITY_w10_run.py (run-time logger; no evaluator edited).  KW10-2 exactness check under FT with the fleet's own program SPaT.
# SMOKE=1: one light per network, one seed, 600 s, into W10_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W10_DIR:-research/city_sim/w10_20261005/diag}; mkdir -p $D/g4 $D/sp $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep; MOD=research/city_sim/tsi_20261005/cmodel/c2
CH=research/city_sim/tsi2_20261005/tune/choice.json; SP=research/city_sim/m4_20261004/spider; ST=research/city_sim/sptsi_20261005; SCH=$ST/tune/choice.json
W="$PY -u scripts/CITY_w10_run.py"; echo "W10-DIAG start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; GL="4"; SL="11"; GS="660"; SS="1100"; else SM=""; GL="4 5"; SL="11 111"; GS="660 661"; SS="1100 1101"; fi
J=$D/jobs.txt; : > $J
# grid4 (fleet s213; TSI-2 providers and adapters)
for t in $GL; do AB=$($PY -c "import json;print(json.load(open('$CH'))['$t']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt"; F="--light RL-H:$t --fleet PL:$P/L11_s213_fleet.pt"
  echo "g4 SHADOW_t$t shadow scripts/CITY_eval_n4.py $N4 $F" >> $J; echo "g4 HYB_t$t serve scripts/CITY_eval_n4.py $N4 $F" >> $J
  echo "g4 TSI_t$t serve scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J; done
echo "g4 FTX plain scripts/CITY_eval6_v11.py --light FT --fleet PL:$P/L11_s213_fleet.pt" >> $J
# spider (rule fleet GLOSAL:0.3; attempt-1 providers and adapters)
for k in $SL; do AB=$($PY -c "import json;print(json.load(open('$SCH'))['$k']['choice'].replace(',',':'))"); TK="n2k:$SP/s3b/prov/fkcl_rlk$k.json:$ST/model/n2k_sp$k.pt"
  echo "sp SHADOW_$k shadow --net spider scripts/CITY_m4s_tsi_eval.py --tk $TK --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
  echo "sp HYBK_$k serve --net spider scripts/CITY_m4s_tsi_eval.py --tk $TK --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
  echo "sp TSIK_$k serve --net spider scripts/CITY_m4s_tsi_eval.py --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J; done
echo "sp FTX plain --net spider scripts/CITY_eval6_lane.py --light FT --fleet GLOSAL:0.3" >> $J
export PY D W SM GS SS
xargs -P 6 -L 1 bash -c 'N=$0; T=$1; M=$2; shift 2; S=$GS; [ "$N" = sp ] && S=$SS; [ -f $D/$N/$T.json ] && exit 0
  W10_LOG=$D/$N/served nice -n 5 $W $M "$@" --seeds $S $SM --record $D/$N/rec/${T}_s{seed}.npz --tag $T --out $D/$N >> $D/$N/run.log 2>&1 || { echo "FAIL $N $T"; exit 255; }' < $J || { echo "W10-DIAG runs failed: stop"; exit 1; }
echo "runs done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W10_SMOKE=$(dirname $D) $PY scripts/CITY_w10_diag.py $D; else $PY scripts/CITY_w10_diag.py $D; fi || exit 1; echo "W10-DIAG done $(date)"
