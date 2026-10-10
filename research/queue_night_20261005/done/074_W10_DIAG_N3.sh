#!/usr/bin/env bash
# W10-2b (PROTOCOL_CITY_WAVE10_20261005): W10-2 / W10-3 on rand3 after 073 NET3 (lights RL-H t21 / t22, fleet N3_s213, NET3 providers and
# adapter choices; TUNE 660 / 661; SHADOW / HYB / TSI + FTX exactness), then the combined report (grid4, spider, rand3).
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W10_DIR:-research/city_sim/w10_20261005/diag}; N=research/city_sim/w8_20261005/net3; mkdir -p $D/n3 $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
[ -f $N/report_net3.txt ] && [ -f $N/tune/choice.json ] || { echo "NET3 not complete: W10-2b not run"; exit 0; }
W="$PY -u scripts/CITY_w10_run.py"; echo "W10-DIAG-N3 start $(date)"; J=$D/n3_jobs.txt; : > $J; F="--fleet PL:$N/fleets/N3_s213_fleet.pt"
for t in 21 22; do AB=$($PY -c "import json;print(json.load(open('$N/tune/choice.json'))['$t']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$N/prep/prov_rlh${t}_cl.json:$N/cmodel/n2_k$t.pt"
  echo "SHADOW_t$t shadow --net rand3 scripts/CITY_eval_n4.py $N4 --light RL-H:$t $F" >> $J; echo "HYB_t$t serve --net rand3 scripts/CITY_eval_n4.py $N4 --light RL-H:$t $F" >> $J
  echo "TSI_t$t serve --net rand3 scripts/CITY_eval_n4.py $N4 --light RL-H:$t $F --light-obs q:$AB" >> $J; done
echo "FTX plain --net rand3 scripts/CITY_eval6_v11.py --light FT $F" >> $J
export PY D W; xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/n3/$T.json ] && exit 0
  W10_LOG=$D/n3/served nice -n 5 $W $M "$@" --seeds 660 661 --record $D/n3/rec/${T}_s{seed}.npz --tag $T --out $D/n3 >> $D/n3/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "W10-2b runs failed: stop"; exit 1; }
$PY scripts/CITY_w10_diag.py $D || exit 1; echo "W10-DIAG-N3 done $(date)"
