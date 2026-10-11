#!/usr/bin/env bash
# TSI Amendment A1: collect under TSI(A*,B*) on TRAIN -> refit -> SELECT 2 jobs -> variant choice.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/tsi_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; M=research/city_sim/n2_20261005/model; TB=research/city_sim/m3_20261004/prep; echo "TSI-REFIT start $(date)"
[ -f $D/sel/choice.json ] || { echo "no TSI choice"; exit 1; }
AB=$($PY -c "import json;print(json.load(open('$D/sel/choice.json'))['choice'].replace(',',' '))"); set -- $AB; A=$1; B=$2; echo "A* $A B* $B"
J=$D/collect.txt; : > $J; for k in 0 1; do F=s13; [ $k = 1 ] && F=s113; for s in 0 1 2 3 4 5 6 7; do echo "$k $F $s" >> $J; done; done
export PY D P M TB A B; xargs -P 4 -L 1 bash -c '[ -f $D/data/k$0/feat_s$2.npz ] || nice -n 5 $PY -u scripts/CITY_eval_n4f.py --n4 0.5:hyb:$TB/prov_rlh$0_cl.json:$M/n2_k$0.pt --featlog $D/data/k$0 --light RL-H:$0 --fleet PL:$P/L11_$1_fleet.pt --light-obs q:$A:$B --seeds $2 --tag C_k$0_s$2 --out $D/data/k$0 >> $D/data/run.log 2>&1 || echo "FAIL collect $0 $2"' < $J
for k in 0 1; do [ "$(ls $D/data/k$k/feat_s*.npz | wc -l)" -eq 8 ] || { echo "collection incomplete k$k"; exit 1; }; done; echo "collected $(date)"
for k in 0 1; do $PY -u scripts/CITY_n2_fit.py $k $D/data/k$k $D/model > $D/model/fit_k$k.log 2>&1 & done; wait; ls $D/model
for k in 0 1; do T=$(echo "TR_a${A}_b${B}_k$k" | tr '.' 'p'); [ -f $D/sel/$T.json ] || nice -n 5 $PY -u scripts/CITY_eval_n4.py --n4 0.5:hyb:$TB/prov_rlh${k}_cl.json:$D/model/n2_k$k.pt --light RL-H:$k --fleet PL:$P/L11_s13_fleet.pt --light-obs q:$A:$B --seeds 650 651 652 653 654 655 --tag $T --out $D/sel >> $D/sel/run.log 2>&1 & done; wait
$PY scripts/CITY_tsi_variant.py | tee $D/sel/variant.txt; echo "TSI-REFIT done $(date)"
