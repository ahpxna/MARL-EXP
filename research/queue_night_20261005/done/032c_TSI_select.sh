#!/usr/bin/env bash
# TSI SELECT (PROTOCOL_CITY_TSI_20261005): 16 jobs on 650-655 -> choice.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/tsi_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; M=research/city_sim/n2_20261005/model; TB=research/city_sim/m3_20261004/prep; echo "TSI-SELECT start $(date)"
[ -f research/city_sim/n4_20261005/sel/R_k0.json ] || { echo "R SELECT rows missing"; exit 1; }; J=$D/sel_jobs.txt; : > $J
for k in 0 1; do for ab in "0 0" "1 0" "1.5 0" "2 0" "1 0.25" "1 0.5" "1.5 0.25" "2 0.25"; do set -- $ab; T=$(echo "T_a$1_b$2_k$k" | tr '.' 'p')
  echo "$T --n4 0.5:hyb:$TB/prov_rlh${k}_cl.json:$M/n2_k$k.pt --light RL-H:$k --fleet PL:$P/L11_s13_fleet.pt --light-obs q:$1:$2" >> $J; done; done
export PY D; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/sel/$T.json ] || nice -n 5 $PY -u scripts/CITY_eval_n4.py "$@" --seeds 650 651 652 653 654 655 --tag $T --out $D/sel >> $D/sel/run.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_tsi_select.py | tee $D/sel/select.txt; echo "TSI-SELECT done $(date)"
